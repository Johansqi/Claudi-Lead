'use strict';

const http = require('http');
const https = require('https');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

// ---------------------------------------------------------
// CONFIGURATION
// ---------------------------------------------------------
const PORT = parseInt(process.env.PORT || '3000', 10);
const HOST = process.env.HOST || '0.0.0.0';

const TG_BOT_TOKEN =
  process.env.TG_BOT_TOKEN || '9181958813:AAEde2nyyiTNwi6PtPyLjfhrkXvIcAOs0LM';
const TG_ADMIN_USERNAME = (process.env.TG_ADMIN_USERNAME || 'sanAtofe')
  .replace(/^@/, '')
  .toLowerCase();
const ENV_CHAT_ID = process.env.TG_CHAT_ID
  ? String(process.env.TG_CHAT_ID).trim()
  : null;

const SESSION_SECRET =
  process.env.SESSION_SECRET || crypto.randomBytes(32).toString('hex');
const TRUST_PROXY = process.env.TRUST_PROXY === '1';

const INDEX_PATH = path.join(__dirname, 'index.html');
const ORDERS_DB_PATH = path.join(__dirname, 'orders.json');

const RATE_LIMIT_WINDOW_MS = 10 * 60 * 1000; // 10 minutes
const RATE_LIMIT_MAX_REQUESTS = 3; // Max 3 orders per IP in 10 minutes
const TIME_TRAP_MIN_MS = 2500; // Reject submissions faster than 2.5s
const TOKEN_TTL_MS = 6 * 60 * 60 * 1000; // 6 hours
const MAX_BODY_BYTES = 16 * 1024; // 16 KB max JSON payload

const ALLOWED_NICHES = new Set([
  'Real Estate',
  'FinTech & Wealth',
  'Enterprise SaaS',
  'High-Ticket Commerce',
  'Custom'
]);

const ALLOWED_FILTERS = new Set([
  'Phone Verified',
  'Liquidity Screened',
  'Exclusive Zero-Resale',
  'Instant Webhook / TG'
]);

// ---------------------------------------------------------
// IN-MEMORY SECURITY STORES & DATABASE
// ---------------------------------------------------------
const rateLimitMap = new Map(); // ipHash -> number[] (timestamps)
const usedNonces = new Map(); // nonce -> expiresAt

let cachedChatId = ENV_CHAT_ID || null;
let ordersStore = [];
let writeQueue = Promise.resolve();

// Periodic cleanup for rate-limit & consumed CSRF nonces
setInterval(() => {
  const now = Date.now();
  for (const [ipHash, timestamps] of rateLimitMap.entries()) {
    const valid = timestamps.filter((ts) => now - ts < RATE_LIMIT_WINDOW_MS);
    if (valid.length === 0) {
      rateLimitMap.delete(ipHash);
    } else {
      rateLimitMap.set(ipHash, valid);
    }
  }
  for (const [nonce, expiresAt] of usedNonces.entries()) {
    if (now > expiresAt) {
      usedNonces.delete(nonce);
    }
  }
}, 60 * 1000).unref();

// ---------------------------------------------------------
// SANITIZATION, MASKING & CRYPTO HELPERS
// ---------------------------------------------------------
function stripControlChars(input, allowNewlines = false) {
  const str = typeof input === 'string' ? input : String(input || '');
  const cleaned = allowNewlines
    ? str.replace(/[\x00-\x09\x0B-\x1F\x7F]/g, '')
    : str.replace(/[\x00-\x1F\x7F]/g, ' ');
  return cleaned.replace(/[ \t]+/g, ' ').trim();
}

function escapeHtml(str) {
  return String(str || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function maskClientName(name) {
  const clean = stripControlChars(name);
  if (clean.length <= 2) return `${clean[0] || '*'}***`;
  if (clean.length <= 5) return `${clean.slice(0, 2)}***`;
  return `${clean.slice(0, 2)}***${clean.slice(-2)}`;
}

function maskContact(contact) {
  const clean = stripControlChars(contact);
  if (!clean) return '***';
  if (clean.startsWith('@')) {
    const body = clean.slice(1);
    if (body.length <= 3) return `@${body[0] || '*'}***`;
    return `@${body.slice(0, 2)}***${body.slice(-2)}`;
  }
  const digits = clean.replace(/\s+/g, '');
  if (digits.length <= 4) return '***';
  return `${digits.slice(0, 3)}***${digits.slice(-2)}`;
}

function computeIpHash(ip) {
  return crypto
    .createHmac('sha256', SESSION_SECRET)
    .update(String(ip || 'unknown'))
    .digest('hex')
    .slice(0, 12);
}

function getClientIp(req) {
  if (TRUST_PROXY && typeof req.headers['x-forwarded-for'] === 'string') {
    const first = req.headers['x-forwarded-for'].split(',')[0].trim();
    if (first) return first;
  }
  return req.socket?.remoteAddress || 'unknown';
}

function calculatePriorityTier(volume) {
  if (volume >= 3500) return 'TIER-X // SOVEREIGN ALLOCATION';
  if (volume >= 1500) return 'TIER-III // DEDICATED NODE';
  if (volume >= 400) return 'TIER-II // PRIORITY STREAM';
  return 'TIER-I // STANDARD FLOW';
}

function generateOrderId() {
  const existing = new Set(ordersStore.map((o) => o.id));
  for (let i = 0; i < 20; i++) {
    const num = crypto.randomInt(1000, 9999);
    const candidate = `#CLD-${num}`;
    if (!existing.has(candidate)) return candidate;
  }
  return `#CLD-${crypto.randomInt(10000, 99999)}`;
}

function generateSecurityHash(orderId, vertical, volume, ipHash) {
  const digest = crypto
    .createHash('sha256')
    .update(`${orderId}|${vertical}|${volume}|${ipHash}|${Date.now()}`)
    .digest('hex')
    .toUpperCase();
  return `0x${digest.slice(0, 4)}...${digest.slice(-4)}`;
}

// ---------------------------------------------------------
// CSRF & TIME-TRAP TOKEN ENGINE
// ---------------------------------------------------------
function issueSecurityToken() {
  const payloadObj = {
    iat: Date.now(),
    nonce: crypto.randomBytes(10).toString('hex')
  };
  const payloadB64 = Buffer.from(JSON.stringify(payloadObj)).toString('base64url');
  const sigB64 = crypto
    .createHmac('sha256', SESSION_SECRET)
    .update(payloadB64)
    .digest('base64url');
  return `${payloadB64}.${sigB64}`;
}

function verifySecurityToken(token) {
  if (typeof token !== 'string' || !token.includes('.')) {
    return { valid: false, status: 403, reason: 'MISSING OR MALFORMED SECURITY TOKEN.' };
  }

  const parts = token.split('.');
  if (parts.length !== 2) {
    return { valid: false, status: 403, reason: 'INVALID TOKEN STRUCTURE.' };
  }

  const [payloadB64, providedSig] = parts;
  const expectedSig = crypto
    .createHmac('sha256', SESSION_SECRET)
    .update(payloadB64)
    .digest('base64url');

  const a = Buffer.from(providedSig);
  const b = Buffer.from(expectedSig);
  if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) {
    return { valid: false, status: 403, reason: 'CSRF SIGNATURE MISMATCH.' };
  }

  let payload;
  try {
    payload = JSON.parse(Buffer.from(payloadB64, 'base64url').toString('utf8'));
  } catch {
    return { valid: false, status: 403, reason: 'UNPARSEABLE SECURITY PAYLOAD.' };
  }

  if (
    !payload ||
    typeof payload.iat !== 'number' ||
    typeof payload.nonce !== 'string'
  ) {
    return { valid: false, status: 403, reason: 'INVALID TOKEN CLAIMS.' };
  }

  const now = Date.now();
  if (usedNonces.has(payload.nonce)) {
    return {
      valid: false,
      status: 403,
      reason: 'REPLAY DETECTED // SECURITY NONCE ALREADY CONSUMED.'
    };
  }

  const elapsed = now - payload.iat;
  if (elapsed > TOKEN_TTL_MS) {
    return {
      valid: false,
      status: 403,
      reason: 'SESSION TOKEN EXPIRED // RELOAD PAGE OR SYNC HANDSHAKE.'
    };
  }

  if (elapsed < TIME_TRAP_MIN_MS) {
    return {
      valid: false,
      status: 403,
      reason: `SECURITY SHIELD // TIME-TRAP TRIGGERED (${elapsed}MS < ${TIME_TRAP_MIN_MS}MS).`
    };
  }

  return { valid: true, nonce: payload.nonce, elapsed };
}

function consumeTokenNonce(nonce) {
  usedNonces.set(nonce, Date.now() + TOKEN_TTL_MS);
}

// ---------------------------------------------------------
// RATE LIMITER (3 REQUESTS / 10 MIN PER IP)
// ---------------------------------------------------------
function checkRateLimit(ipHash) {
  const now = Date.now();
  const prev = rateLimitMap.get(ipHash) || [];
  const active = prev.filter((ts) => now - ts < RATE_LIMIT_WINDOW_MS);

  if (active.length >= RATE_LIMIT_MAX_REQUESTS) {
    const oldest = active[0];
    const retryAfterSec = Math.max(
      1,
      Math.ceil((RATE_LIMIT_WINDOW_MS - (now - oldest)) / 1000)
    );
    rateLimitMap.set(ipHash, active);
    return { allowed: false, retryAfterSec };
  }

  active.push(now);
  rateLimitMap.set(ipHash, active);
  return {
    allowed: true,
    remaining: RATE_LIMIT_MAX_REQUESTS - active.length
  };
}

// ---------------------------------------------------------
// JSON DATABASE PERSISTENCE
// ---------------------------------------------------------
function createSeedOrders() {
  const now = Date.now();
  return [
    {
      id: '#CLD-8492',
      timestamp: new Date(now - 18 * 60 * 1000).toISOString(),
      vertical: 'FinTech & Crypto',
      volume: 450,
      priorityTier: 'TIER-II // PRIORITY STREAM',
      clientMasked: 'Va***ld',
      contactMasked: '@va***92',
      securityHash: '0x8F4A...C91E',
      filtersCount: 3,
      status: '[DISPATCHED TO TG BOT]'
    },
    {
      id: '#CLD-8371',
      timestamp: new Date(now - 74 * 60 * 1000).toISOString(),
      vertical: 'Real Estate',
      volume: 1600,
      priorityTier: 'TIER-III // DEDICATED NODE',
      clientMasked: 'Em***te',
      contactMasked: '+971***44',
      securityHash: '0x3D1B...77A4',
      filtersCount: 3,
      status: '[DISPATCHED TO TG BOT]'
    },
    {
      id: '#CLD-8209',
      timestamp: new Date(now - 190 * 60 * 1000).toISOString(),
      vertical: 'B2B Enterprise',
      volume: 900,
      priorityTier: 'TIER-II // PRIORITY STREAM',
      clientMasked: 'Kr***ms',
      contactMasked: '@kr***op',
      securityHash: '0xA92C...18F0',
      filtersCount: 2,
      status: '[DISPATCHED TO TG BOT]'
    },
    {
      id: '#CLD-8044',
      timestamp: new Date(now - 340 * 60 * 1000).toISOString(),
      vertical: 'High-Ticket E-Com',
      volume: 3500,
      priorityTier: 'TIER-X // SOVEREIGN ALLOCATION',
      clientMasked: 'No***ux',
      contactMasked: '@no***es',
      securityHash: '0x5E77...D02B',
      filtersCount: 3,
      status: '[DISPATCHED TO TG BOT]'
    }
  ];
}

function persistOrdersToDisk() {
  const snapshot = JSON.stringify(ordersStore, null, 2);
  const tmpPath = `${ORDERS_DB_PATH}.tmp`;
  writeQueue = writeQueue
    .then(async () => {
      await fs.promises.writeFile(tmpPath, snapshot, 'utf8');
      await fs.promises.rename(tmpPath, ORDERS_DB_PATH);
    })
    .catch((err) => {
      console.error('[DB] Failed writing orders.json:', err.message);
    });
  return writeQueue;
}

function loadOrdersDatabase() {
  try {
    if (fs.existsSync(ORDERS_DB_PATH)) {
      const raw = fs.readFileSync(ORDERS_DB_PATH, 'utf8');
      const parsed = JSON.parse(raw);
      if (Array.isArray(parsed)) {
        ordersStore = parsed;
        console.log(`[DB] Loaded ${ordersStore.length} masked orders from orders.json`);
        return;
      }
    }
  } catch (err) {
    console.warn('[DB] Reinitializing orders.json after read error:', err.message);
  }
  ordersStore = createSeedOrders();
  persistOrdersToDisk();
  console.log(`[DB] Initialized orders.json with ${ordersStore.length} baseline records`);
}

// ---------------------------------------------------------
// TELEGRAM BOT INTEGRATION
// ---------------------------------------------------------
function telegramApiRequest(method, payloadObj = null) {
  return new Promise((resolve, reject) => {
    const bodyStr = payloadObj ? JSON.stringify(payloadObj) : '';
    const options = {
      hostname: 'api.telegram.org',
      port: 443,
      path: `/bot${TG_BOT_TOKEN}/${method}`,
      method: payloadObj ? 'POST' : 'GET',
      headers: payloadObj
        ? {
            'Content-Type': 'application/json',
            'Content-Length': Buffer.byteLength(bodyStr)
          }
        : {},
      timeout: 6500
    };

    const req = https.request(options, (res) => {
      let data = '';
      res.on('data', (chunk) => {
        data += chunk;
      });
      res.on('end', () => {
        try {
          const parsed = JSON.parse(data);
          resolve({ statusCode: res.statusCode, body: parsed });
        } catch (err) {
          reject(new Error(`Invalid JSON from Telegram API (${res.statusCode})`));
        }
      });
    });

    req.on('timeout', () => {
      req.destroy(new Error('Telegram API request timed out'));
    });

    req.on('error', (err) => {
      reject(err);
    });

    if (payloadObj) {
      req.write(bodyStr);
    }
    req.end();
  });
}

async function resolveAdminChatId(forceRefresh = false) {
  if (ENV_CHAT_ID) {
    cachedChatId = ENV_CHAT_ID;
    return cachedChatId;
  }
  if (cachedChatId && !forceRefresh) {
    return cachedChatId;
  }

  try {
    const res = await telegramApiRequest('getUpdates?limit=100');
    if (!res.body || !res.body.ok || !Array.isArray(res.body.result)) {
      console.warn('[TG] getUpdates returned non-OK:', res.body?.description || res.statusCode);
      return cachedChatId;
    }

    const updates = res.body.result;
    let targetMatch = null;
    let startAdminMatch = null;
    let latestPrivateMatch = null;

    for (let i = updates.length - 1; i >= 0; i--) {
      const upd = updates[i];
      const msg =
        upd.message ||
        upd.edited_message ||
        upd.callback_query?.message ||
        null;
      const from = upd.message?.from || upd.edited_message?.from || upd.callback_query?.from || null;
      const chat = msg?.chat || upd.my_chat_member?.chat || null;

      if (!chat || typeof chat.id === 'undefined') continue;

      const fromUsername = (from?.username || '').toLowerCase();
      const chatUsername = (chat?.username || '').toLowerCase();

      if (fromUsername === TG_ADMIN_USERNAME || chatUsername === TG_ADMIN_USERNAME) {
        targetMatch = String(chat.id);
        break;
      }

      const text = typeof msg?.text === 'string' ? msg.text.trim() : '';
      if (!startAdminMatch && chat.type === 'private' && text.startsWith('/start')) {
        startAdminMatch = String(chat.id);
      }

      if (!latestPrivateMatch && chat.type === 'private') {
        latestPrivateMatch = String(chat.id);
      }
    }

    const resolved = targetMatch || startAdminMatch || latestPrivateMatch || null;
    if (resolved) {
      cachedChatId = resolved;
      console.log(`[TG] Admin Chat ID resolved and cached: ${cachedChatId}`);
    } else {
      console.warn(
        `[TG] No active chat found in getUpdates yet. Have @${TG_ADMIN_USERNAME} send /start to the bot.`
      );
    }
    return cachedChatId;
  } catch (err) {
    console.warn('[TG] Failed to query getUpdates:', err.message);
    return cachedChatId;
  }
}

function buildTelegramMessageHtml(orderDetails) {
  const filtersStr =
    orderDetails.filters.length > 0
      ? orderDetails.filters.map((f) => escapeHtml(f)).join(', ')
      : 'Standard Baseline';
  const geoStr = orderDetails.geoCriteria
    ? escapeHtml(orderDetails.geoCriteria)
    : 'Not specified';

  return [
    '<b>CLAUDI LEAD // NEW ORDER DISPATCH</b>',
    '━━━━━━━━━━━━━━━━━━━━',
    `<b>Order ID:</b> <code>${escapeHtml(orderDetails.id)}</code>`,
    `<b>Client:</b> ${escapeHtml(orderDetails.clientName)}`,
    `<b>Vertical:</b> ${escapeHtml(orderDetails.vertical)}`,
    `<b>Volume:</b> <code>${escapeHtml(orderDetails.volume.toLocaleString('en-US'))} LEADS / MO</code>`,
    `<b>Priority Tier:</b> <code>${escapeHtml(orderDetails.priorityTier)}</code>`,
    `<b>Filters:</b> ${filtersStr}`,
    `<b>GEO &amp; Criteria:</b> ${geoStr}`,
    `<b>Direct Contact:</b> <code>${escapeHtml(orderDetails.contact)}</code>`,
    '━━━━━━━━━━━━━━━━━━━━',
    `<b>Security Hash:</b> <code>${escapeHtml(orderDetails.securityHash)}</code>`,
    `<b>IP Hash:</b> <code>${escapeHtml(orderDetails.ipHash)}</code>`,
    `<b>Timestamp:</b> <code>${escapeHtml(orderDetails.timestamp)}</code>`
  ].join('\n');
}

async function dispatchOrderToTelegram(orderDetails) {
  let chatId = await resolveAdminChatId(false);
  if (!chatId) {
    return { delivered: false, reason: 'Chat ID unresolved (send /start to bot)' };
  }

  const text = buildTelegramMessageHtml(orderDetails);

  try {
    let result = await telegramApiRequest('sendMessage', {
      chat_id: chatId,
      text,
      parse_mode: 'HTML',
      disable_web_page_preview: true
    });

    if (!result.body?.ok && (result.statusCode === 400 || result.statusCode === 403) && !ENV_CHAT_ID) {
      cachedChatId = null;
      chatId = await resolveAdminChatId(true);
      if (chatId) {
        result = await telegramApiRequest('sendMessage', {
          chat_id: chatId,
          text,
          parse_mode: 'HTML',
          disable_web_page_preview: true
        });
      }
    }

    if (result.body?.ok) {
      return { delivered: true };
    }
    console.warn('[TG] sendMessage rejected:', result.body?.description || result.statusCode);
    return { delivered: false, reason: result.body?.description || 'Telegram API error' };
  } catch (err) {
    console.warn('[TG] sendMessage error:', err.message);
    return { delivered: false, reason: err.message };
  }
}

// ---------------------------------------------------------
// HTTP HELPERS & REQUEST ROUTER
// ---------------------------------------------------------
function setSecurityHeaders(res) {
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('X-Frame-Options', 'DENY');
  res.setHeader('Referrer-Policy', 'no-referrer');
  res.setHeader('Permissions-Policy', 'camera=(), microphone=(), geolocation=()');
}

function sendJson(res, statusCode, data, extraHeaders = {}) {
  setSecurityHeaders(res);
  res.writeHead(statusCode, {
    'Content-Type': 'application/json; charset=utf-8',
    'Cache-Control': 'no-store',
    ...extraHeaders
  });
  res.end(JSON.stringify(data));
}

function readJsonBody(req) {
  return new Promise((resolve, reject) => {
    let totalBytes = 0;
    const chunks = [];

    req.on('data', (chunk) => {
      totalBytes += chunk.length;
      if (totalBytes > MAX_BODY_BYTES) {
        reject(Object.assign(new Error('PAYLOAD TOO LARGE'), { statusCode: 413 }));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });

    req.on('end', () => {
      const raw = Buffer.concat(chunks).toString('utf8');
      if (!raw) {
        resolve({});
        return;
      }
      try {
        resolve(JSON.parse(raw));
      } catch {
        reject(Object.assign(new Error('INVALID JSON PAYLOAD'), { statusCode: 400 }));
      }
    });

    req.on('error', (err) => reject(err));
  });
}

function verifySameOrigin(req) {
  const host = req.headers.host;
  if (!host) return true;
  const origin = req.headers.origin;
  if (origin) {
    try {
      const parsedOrigin = new URL(origin);
      if (parsedOrigin.host !== host) return false;
    } catch {
      return false;
    }
  }
  const referer = req.headers.referer;
  if (!origin && referer) {
    try {
      const parsedRef = new URL(referer);
      if (parsedRef.host !== host) return false;
    } catch {
      return false;
    }
  }
  return true;
}

async function handleRequest(req, res) {
  const parsedUrl = new URL(req.url || '/', `http://${req.headers.host || 'localhost'}`);
  const pathname = parsedUrl.pathname;

  // Serve Frontend (with embedded fresh HMAC CSRF/Time-Trap token)
  if (req.method === 'GET' && (pathname === '/' || pathname === '/index.html')) {
    try {
      const html = await fs.promises.readFile(INDEX_PATH, 'utf8');
      const token = issueSecurityToken();
      const injectedHtml = html.replace('__CSRF_TOKEN__', token);
      setSecurityHeaders(res);
      res.writeHead(200, {
        'Content-Type': 'text/html; charset=utf-8',
        'Cache-Control': 'no-store'
      });
      res.end(injectedHtml);
    } catch (err) {
      sendJson(res, 500, { ok: false, error: 'UNABLE TO SERVE FRONTEND.' });
    }
    return;
  }

  // Handshake endpoint to refresh CSRF/Time-Trap token
  if (req.method === 'GET' && pathname === '/api/handshake') {
    sendJson(res, 200, { ok: true, token: issueSecurityToken() });
    return;
  }

  // Status Check endpoint for a specific Order ID
  if (req.method === 'GET' && pathname === '/api/orders/status') {
    const orderQuery = (parsedUrl.searchParams.get('id') || '').trim();
    if (!orderQuery) {
      sendJson(res, 400, { ok: false, error: 'MISSING ORDER ID PARAMETER.' });
      return;
    }
    const match = ordersStore.find((o) => o.id.toUpperCase() === orderQuery.toUpperCase());
    if (match) {
      sendJson(res, 200, {
        ok: true,
        order: {
          id: match.id,
          timestamp: match.timestamp,
          vertical: match.vertical,
          volume: match.volume,
          priorityTier: match.priorityTier,
          clientMasked: match.clientMasked,
          securityHash: match.securityHash,
          status: 'DISPATCHED_TO_TELEGRAM_CORE',
          deliveryStatus: 'COMMITTED // SLA < 4H'
        }
      });
      return;
    }
    sendJson(res, 404, { ok: false, error: 'ORDER ID NOT FOUND IN ACTIVE LEDGER.' });
    return;
  }

  // Submit New Lead Order
  if (req.method === 'POST' && pathname === '/api/orders') {
    if (!verifySameOrigin(req)) {
      sendJson(res, 403, { ok: false, error: 'CROSS-ORIGIN REQUEST BLOCKED.' });
      return;
    }

    const clientIp = getClientIp(req);
    const ipHash = computeIpHash(clientIp);

    // 1. Rate Limit Check (3 req / 10 min per IP)
    const rateCheck = checkRateLimit(ipHash);
    if (!rateCheck.allowed) {
      sendJson(
        res,
        429,
        {
          ok: false,
          error: `RATE LIMIT EXCEEDED // MAX 3 ORDERS PER 10 MIN. RETRY IN ${rateCheck.retryAfterSec}S.`
        },
        { 'Retry-After': String(rateCheck.retryAfterSec) }
      );
      return;
    }

    let body;
    try {
      body = await readJsonBody(req);
    } catch (err) {
      sendJson(res, err.statusCode || 400, { ok: false, error: err.message });
      return;
    }

    // 2. Honeypot Check (Silent Drop if triggered)
    if (
      (typeof body.website_url === 'string' && body.website_url.trim().length > 0) ||
      (typeof body.hp === 'string' && body.hp.trim().length > 0)
    ) {
      console.warn(`[SECURITY] Honeypot triggered from IP hash ${ipHash} — silent drop.`);
      sendJson(res, 200, {
        ok: true,
        order: {
          id: '#CLD-0000',
          status: '[DISPATCHED TO TG BOT]'
        },
        nextToken: issueSecurityToken()
      });
      return;
    }

    // 3. CSRF + Time-Trap Verification (> 2.5s)
    const tokenCheck = verifySecurityToken(body.securityToken);
    if (!tokenCheck.valid) {
      console.warn(`[SECURITY] Token check failed (${ipHash}): ${tokenCheck.reason}`);
      sendJson(res, tokenCheck.status, {
        ok: false,
        error: tokenCheck.reason,
        nextToken: issueSecurityToken()
      });
      return;
    }

    // 4. Input Validation & Sanitization
    const clientName = stripControlChars(body.clientName).slice(0, 80);
    if (clientName.length < 2) {
      sendJson(res, 400, {
        ok: false,
        error: 'VALIDATION ERROR // CLIENT OR COMPANY NAME MUST BE AT LEAST 2 CHARS.'
      });
      return;
    }

    const rawNiche = stripControlChars(body.niche);
    if (!ALLOWED_NICHES.has(rawNiche)) {
      sendJson(res, 400, { ok: false, error: 'VALIDATION ERROR // INVALID TARGET VERTICAL.' });
      return;
    }

    let vertical = rawNiche;
    if (rawNiche === 'Custom') {
      const customNiche = stripControlChars(body.customNiche).slice(0, 50);
      if (customNiche.length < 2) {
        sendJson(res, 400, {
          ok: false,
          error: 'VALIDATION ERROR // SPECIFY CUSTOM VERTICAL (MIN 2 CHARS).'
        });
        return;
      }
      vertical = `Custom: ${customNiche}`;
    }

    const volumeNum = Number(body.volume);
    if (!Number.isFinite(volumeNum) || volumeNum < 50 || volumeNum > 5000) {
      sendJson(res, 400, {
        ok: false,
        error: 'VALIDATION ERROR // VOLUME MUST BE BETWEEN 50 AND 5000 LEADS.'
      });
      return;
    }
    const volume = Math.round(volumeNum);

    const rawFilters = Array.isArray(body.filters) ? body.filters : [];
    const filters = rawFilters
      .map((f) => stripControlChars(f))
      .filter((f) => ALLOWED_FILTERS.has(f));

    const contact = stripControlChars(body.contact).slice(0, 80);
    if (contact.length < 3) {
      sendJson(res, 400, {
        ok: false,
        error: 'VALIDATION ERROR // PROVIDE VALID TELEGRAM @USERNAME OR PHONE.'
      });
      return;
    }

    const geoCriteria = stripControlChars(body.geoCriteria, true).slice(0, 400);

    // Consume nonce now that payload passed all validations
    consumeTokenNonce(tokenCheck.nonce);

    // 5. Build Masked Record & Telegram Dispatch Payload
    const id = generateOrderId();
    const timestamp = new Date().toISOString();
    const priorityTier = calculatePriorityTier(volume);
    const securityHash = generateSecurityHash(id, vertical, volume, ipHash);

    const publicRecord = {
      id,
      timestamp,
      vertical,
      volume,
      priorityTier,
      clientMasked: maskClientName(clientName),
      contactMasked: maskContact(contact),
      securityHash,
      filtersCount: filters.length,
      status: '[DISPATCHED TO TG BOT]'
    };

    ordersStore.unshift(publicRecord);
    if (ordersStore.length > 200) {
      ordersStore = ordersStore.slice(0, 200);
    }
    await persistOrdersToDisk();

    const tgResult = await dispatchOrderToTelegram({
      id,
      timestamp,
      clientName,
      vertical,
      volume,
      priorityTier,
      filters,
      geoCriteria,
      contact,
      securityHash,
      ipHash
    });

    console.log(
      `[ORDER] ${id} | ${vertical} | ${volume} Leads | Hash ${securityHash} | TG: ${
        tgResult.delivered ? 'SENT' : `DEFERRED (${tgResult.reason})`
      }`
    );

    sendJson(res, 201, {
      ok: true,
      order: publicRecord,
      telegramDispatched: tgResult.delivered,
      nextToken: issueSecurityToken()
    });
    return;
  }

  sendJson(res, 404, { ok: false, error: 'ENDPOINT NOT FOUND.' });
}

// ---------------------------------------------------------
// SERVER BOOTSTRAP
// ---------------------------------------------------------
loadOrdersDatabase();

const server = http.createServer((req, res) => {
  handleRequest(req, res).catch((err) => {
    console.error('[HTTP] Unhandled error:', err);
    if (!res.headersSent) {
      sendJson(res, 500, { ok: false, error: 'INTERNAL CORE SERVER ERROR.' });
    }
  });
});

server.listen(PORT, HOST, () => {
  console.log('=======================================================');
  console.log(` CLAUDI LEAD // SYS.v4 BACKEND ONLINE`);
  console.log(` URL        : http://localhost:${PORT}`);
  console.log(` TG ADMIN   : @${TG_ADMIN_USERNAME}`);
  console.log(` SHIELD     : Rate-Limit(3/10m) + HMAC-CSRF + TimeTrap(2.5s) + Honeypot`);
  console.log('=======================================================');
  resolveAdminChatId(false);
});

function shutdown(signal) {
  console.log(`\n[SYS] Received ${signal}, shutting down cleanly...`);
  server.close(() => {
    process.exit(0);
  });
}

process.on('SIGINT', () => shutdown('SIGINT'));
process.on('SIGTERM', () => shutdown('SIGTERM'));
