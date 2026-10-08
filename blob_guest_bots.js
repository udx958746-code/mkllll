#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const https = require('https');
const WebSocket = require('ws');
const crypto = require('crypto');
const dgram = require('dgram');
const { SocksProxyAgent } = require('socks-proxy-agent');
const { SocksClient } = require('socks');

const VERSION_CODE = 367;
const VERSION_NAME = '3.0.0';
const LOCALE = 'en';
const PLATFORM = '1';
const S_HEADER = 'aRegs';

const D_START_MS = 500;
const FEED_INTERVAL_MS = 10;
const D_INTERVAL_MS = 50;
const MIN_RESPAWN_INTERVAL_MS = 2000;
const RESPAWN_CONFIRM_TIMEOUT_MS = 3500;
const MAX_RESPAWN_RETRIES = 3;
const MAP_MIN = -7071;
const MAP_MAX = 7071;
const TREND_DISTANCE = 6000;
const TREND_RETRY_MS = 2000;
const RECONNECT_MS = 0;
const HANDSHAKE_TIMEOUT_MS = 25000;
const TRACK_INTERVAL_MS = 20;
const TRACK_TARGET_TTL_MS = 1500;
const TRACK_BRIDGE_HOST = process.env.TRACK_BRIDGE_HOST || '127.0.0.1';
const TRACK_BRIDGE_PORT = Number(process.env.TRACK_BRIDGE_PORT || 48959);
const PROXY_CHECK_TIMEOUT_MS = 7000;
const MAX_BOTS_PER_PROXY = 5;
const FFA_RECONNECT_MS = 0;
const DEFAULT_MESSAGE_INTERVAL_MS = 5000;
const ZWNJ = '\u200c';

const TOKEN_FILE = path.join(process.cwd(), 'token.txt');
const PROXY_FILE = path.join(process.cwd(), 'proxy.txt');
const TELEGRAM_TOKEN_FILE = path.join(process.cwd(), 'tokentelgram.txt');

function readLines(file, required = false) {
  if (!fs.existsSync(file)) {
    if (required) throw new Error(`الملف غير موجود: ${path.basename(file)}`);
    return [];
  }
  return fs.readFileSync(file, 'utf8')
    .split(/\r?\n/)
    .map(v => v.trim())
    .filter(v => v.length && !v.startsWith('#'));
}

function readTokens() {
  if (!fs.existsSync(TOKEN_FILE)) throw new Error('الملف غير موجود: token.txt');
  const lines = readLines(TOKEN_FILE, true);
  if (!lines.length) throw new Error('token.txt فارغ.');
  if (lines.length > 1) console.log('[TOKEN] token.txt: using first token only; extra lines ignored.');
  const token = lines[0];
  console.log('[TOKEN] Loaded 1 shared token from token.txt; it will be reused for every bot.');
  return [{ file: 'token.txt', token }];
}

function readTelegramToken() {
  const lines = readLines(TELEGRAM_TOKEN_FILE, true);
  if (!lines.length) throw new Error('tokentelgram.txt فارغ.');
  return lines[0];
}

function parseProxy(line) {
  const raw = String(line || '').trim();
  if (!raw || raw === '-' || /^direct$/i.test(raw)) return null;

  let value = raw;
  if (!/^(socks4|socks5):\/\//i.test(value)) value = `socks5://${value}`;

  let u;
  try {
    u = new URL(value);
  } catch (_) {
    throw new Error(`بروكسي غير صالح: ${raw}`);
  }

  const scheme = u.protocol.toLowerCase().replace(':', '');
  if (scheme !== 'socks4' && scheme !== 'socks5') {
    throw new Error(`يسمح فقط SOCKS4/SOCKS5: ${raw}`);
  }
  if (!u.hostname) throw new Error(`بروكسي غير صالح: ${raw}`);
  const portText = u.port || (scheme === 'socks4' || scheme === 'socks5' ? '1080' : '');
  const port = Number(portText);
  if (!Number.isInteger(port) || port < 1 || port > 65535) {
    throw new Error(`منفذ بروكسي غير صالح: ${raw}`);
  }

  const username = u.username ? decodeURIComponent(u.username) : '';
  const password = u.password ? decodeURIComponent(u.password) : '';
  if (scheme === 'socks4' && password) {
    throw new Error(`SOCKS4 يدعم userId فقط، بدون password: ${raw}`);
  }

  return {
    scheme,
    type: scheme === 'socks4' ? 4 : 5,
    host: u.hostname,
    port,
    username,
    password,
    url: `${scheme}://${encodeURIComponent(username)}${username ? (password ? ':' + encodeURIComponent(password) : '') + '@' : ''}${u.hostname}:${port}`,
    display: `${u.hostname}:${port}${username ? ' (auth)' : ''}`,
    latency: null,
    healthy: false,
  };
}

function readProxies() {
  if (!fs.existsSync(PROXY_FILE)) return [];
  return readLines(PROXY_FILE, true).map(parseProxy).filter(Boolean);
}

function proxyConnectionOptions(proxy) {
  const options = {
    host: proxy.host,
    port: proxy.port,
    type: proxy.type,
  };
  if (proxy.type === 5 && proxy.username) {
    options.userId = proxy.username;
    options.password = proxy.password || '';
  } else if (proxy.type === 4 && proxy.username) {
    options.userId = proxy.username;
  }
  return options;
}

async function checkProxy(proxy, endpoint, timeoutMs = PROXY_CHECK_TIMEOUT_MS) {
  const started = Date.now();
  let result = null;
  try {
    result = await Promise.race([
      SocksClient.createConnection({
        proxy: proxyConnectionOptions(proxy),
        destination: { host: endpoint.hostname, port: Number(endpoint.port) },
        command: 'connect',
      }),
      new Promise((_, reject) => setTimeout(() => reject(new Error('timeout')), timeoutMs)),
    ]);
    const latency = Date.now() - started;
    proxy.latency = latency;
    proxy.healthy = true;
    try { result.socket.destroy(); } catch (_) {}
    return { proxy, ok: true, latency };
  } catch (err) {
    proxy.latency = null;
    proxy.healthy = false;
    try { result?.socket?.destroy(); } catch (_) {}
    return { proxy, ok: false, error: err?.message || 'failed' };
  }
}

async function selectFastProxies(proxies, endpoint, neededCount) {
  if (!proxies.length) return { selected: [], checks: [] };
  console.log(`[PROXY] Checking ${proxies.length} proxies...`);
  const checks = await Promise.all(proxies.map(p => checkProxy(p, endpoint)));
  for (const r of checks) {
    if (r.ok) console.log(`[PROXY] OK   ${r.proxy.display} ${r.latency}ms`);
    else console.log(`[PROXY] DEAD ${r.proxy.display}`);
  }
  const alive = checks.filter(r => r.ok).sort((a, b) => a.latency - b.latency).map(r => r.proxy);
  const selected = alive.slice(0, neededCount);
  console.log(`[PROXY] Selected ${selected.length}/${neededCount}; max ${MAX_BOTS_PER_PROXY} bots per proxy.`);
  return { selected, checks };
}

function parseEndpoint(input) {
  let value = String(input || '').trim();
  if (!value) throw new Error('IP:PORT فارغ.');
  if (!/^wss?:\/\//i.test(value)) value = `ws://${value}`;
  const u = new URL(value);
  if (!['ws:', 'wss:'].includes(u.protocol)) throw new Error('استخدم ws:// أو wss://.');
  if (!u.hostname || !u.port) {
    if (u.protocol === 'ws:' && u.hostname) u.port = '80';
    else if (u.protocol === 'wss:' && u.hostname) u.port = '443';
    else throw new Error('اكتب IP:PORT مثل 51.195.60.134:4807');
  }
  if (!u.pathname) u.pathname = '/';
  return u;
}

function javaStringHashCode(value) {
  let hash = 0;
  for (let i = 0; i < value.length; i++) {
    hash = Math.imul(hash, 31) + value.charCodeAt(i);
    hash |= 0;
  }
  return hash | 0;
}

function stableBotAndroidHash(id, token) {
  const digest = crypto.createHash('sha256').update(`${id}:${token}`).digest('hex').slice(0, 16);
  return javaStringHashCode(`bot-${id}-${digest}`);
}

function getBaseAndroidId() {
  try {
    const { execFileSync } = require('child_process');
    const out = execFileSync('settings', ['get', 'secure', 'android_id'], {
      encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'], timeout: 1500,
    }).trim();
    return out && out !== 'null' && out !== 'unknown' ? out : '';
  } catch (_) {
    return '';
  }
}

function buildClientState(androidIdHash) {
  const b = Buffer.alloc(26);
  b.writeUInt8(0x05, 0);
  b.writeInt32LE(VERSION_CODE, 1);
  b.writeInt32LE(0x3f, 5);
  b.writeDoubleLE(777.0, 9);
  b.writeInt32LE(0, 17);
  b.writeUInt8(0, 21);
  b.writeInt32LE(androidIdHash | 0, 22);
  return b;
}

function cleanName(name) {
  return String(name || '').replace(/<.*>/g, '').trim();
}

function buildNamePacket(name) {
  const clean = cleanName(name);
  const b = Buffer.alloc(1 + clean.length * 2);
  b[0] = 0x00;
  for (let i = 0; i < clean.length; i++) b.writeUInt16LE(clean.charCodeAt(i), 1 + i * 2);
  return b;
}

function buildLongMovement(x, y) {
  const b = Buffer.alloc(13);
  b.writeUInt8(0x10, 0);
  b.writeInt32LE(x | 0, 1);
  b.writeInt32LE(y | 0, 5);
  b.writeInt32LE(0, 9);
  return b;
}

function buildShortMovement(x, y) {
  const b = Buffer.alloc(5);
  b[0] = 0x0f;
  b.writeInt16LE(Math.max(-32768, Math.min(32767, Math.trunc(x))), 1);
  b.writeInt16LE(Math.max(-32768, Math.min(32767, Math.trunc(y))), 3);
  return b;
}

function buildFdReply(a, p, serverVersion) {
  let r;
  if (serverVersion >= 7) {
    const q = ((a >> p) ^ (p & a)) | 0;
    r = (q | a) | 0;
  } else {
    r = (Math.imul(p, Math.pow(2, a)) ^ a ^ (p & a)) | 0;
  }
  const out = Buffer.alloc(5);
  out[0] = 0xfd;
  out.writeInt32LE(r, 1);
  return out;
}

function buildDActionPacket() {
  return Buffer.from([0x11, 0x02]);
}

function buildChatPacket(text) {
  const value = String(text ?? '');
  const b = Buffer.alloc(2 + value.length * 2);
  b[0] = 0x63;
  b[1] = 0x00;
  for (let i = 0; i < value.length; i++) b.writeUInt16LE(value.charCodeAt(i), 2 + i * 2);
  return b;
}

function buildFeedActionPacket(serverVersion) {
  return serverVersion >= 10 ? Buffer.from([0x20]) : Buffer.from([0x15]);
}

function bufferHas(buf, off, size) {
  return off >= 0 && size >= 0 && off + size <= buf.length;
}

function readUtf16Z(buf, offset, maxChars = 64) {
  let p = offset;
  let out = '';
  for (let i = 0; i < maxChars && bufferHas(buf, p, 2); i++, p += 2) {
    const c = buf.readUInt16LE(p);
    if (c === 0) return { value: out, next: p + 2 };
    out += String.fromCharCode(c);
  }
  return { value: out, next: p };
}

function skipZeroTerminatedBytes(buf, p) {
  while (p < buf.length) {
    const b = buf.readUInt8(p++);
    if (b === 0) break;
  }
  return p;
}

function parseShortUpdate(buf, shortNamesPackets = false, serverVersion = 0) {
  const entities = [];
  const removedIds = [];
  if (!Buffer.isBuffer(buf) || buf.length < 5) return { entities, removedIds };

  try {
    let p = 1;
    const eaten = buf.readUInt16LE(p);
    p += 2;
    if (eaten > 4096 || !bufferHas(buf, p, eaten * 4)) return { entities, removedIds };

    for (let i = 0; i < eaten; i++) p += 4;

    while (bufferHas(buf, p, 2)) {
      const entityStart = p;
      const id = buf.readUInt16LE(p);
      p += 2;

      if (id === 0) {
        if (!bufferHas(buf, p, 2)) break;
        const count = buf.readUInt16LE(p);
        p += 2;
        if (count > 4096 || !bufferHas(buf, p, count * 2)) break;
        for (let i = 0; i < count; i++) {
          removedIds.push(buf.readUInt16LE(p));
          p += 2;
        }
        break;
      }

      if (!bufferHas(buf, p, 7)) break;
      const x = buf.readInt16LE(p);
      const y = buf.readInt16LE(p + 2);
      const size = buf.readUInt16LE(p + 4);
      const flags = buf.readUInt8(p + 6);
      p += 7;

      let skin = '';
      let skinId = 0;
      let nameId = 0;
      let colorId = 0;

      if (flags & 0x02) {
        if (!bufferHas(buf, p, 2)) break;
        colorId = buf.readUInt16LE(p);
        p += 2;
      }

      if (flags & 0x04) {
        if (shortNamesPackets) {
          if (!bufferHas(buf, p, 2)) break;
          skinId = buf.readUInt16LE(p);
          p += 2;
        } else {
          const skinStart = p;
          while (bufferHas(buf, p, 1)) {
            const b = buf.readUInt8(p++);
            if (b === 0) break;
          }
          if (p === buf.length && buf[buf.length - 1] !== 0) break;
          if (p > skinStart + 1) {
            try { skin = buf.subarray(skinStart, p - 1).toString('utf8'); } catch (_) {}
          }
        }
      }

      const nameInfo = readUtf16Z(buf, p, 256);
      if (nameInfo.next === p || nameInfo.next > buf.length) break;
      const name = nameInfo.value || '';
      p = nameInfo.next;

      if (flags & 0x08) {
        if (!bufferHas(buf, p, 2)) break;
        nameId = buf.readUInt16LE(p);
        p += 2;
      }

      let status = -1;
      let ownedHint = false;
      if (flags & 0x80) {
        if (!bufferHas(buf, p, 1)) break;
        status = buf.readUInt8(p++);
        ownedHint = serverVersion >= 9 ? (status & 0x80) !== 0 : ((flags & 0x40) !== 0);
      } else if (serverVersion === 8 && (flags & 0x40)) {
        ownedHint = true;
      }

      entities.push({
        id,
        x,
        y,
        size,
        flags,
        skin,
        skinId,
        colorId,
        nameId,
        name,
        status,
        ownedHint,
        offset: entityStart,
      });
    }
  } catch (_) {
    return { entities, removedIds };
  }

  return { entities, removedIds };
}

function parseLongUpdate(buf, shortNamesPackets = false, serverVersion = 0) {
  const entities = [];
  const removedIds = [];
  if (!Buffer.isBuffer(buf) || buf.length < 7) return { entities, removedIds };

  try {
    let p = 1;
    const eaten = buf.readUInt16LE(p);
    p += 2;
    if (eaten > 4096 || !bufferHas(buf, p, eaten * 8)) return { entities, removedIds };
    p += eaten * 8;

    while (bufferHas(buf, p, 4)) {
      const entityStart = p;
      const id = buf.readUInt32LE(p);
      p += 4;

      if (id === 0) {
        if (!bufferHas(buf, p, 4)) break;
        const count = buf.readUInt32LE(p);
        p += 4;
        if (count > 4096 || !bufferHas(buf, p, count * 4)) break;
        for (let i = 0; i < count; i++) {
          removedIds.push(buf.readUInt32LE(p));
          p += 4;
        }
        break;
      }

      if (!bufferHas(buf, p, 14)) break;
      const x = buf.readInt32LE(p);
      const y = buf.readInt32LE(p + 4);
      const size = buf.readUInt16LE(p + 8);
      const r = buf.readUInt8(p + 10);
      const g = buf.readUInt8(p + 11);
      const b = buf.readUInt8(p + 12);
      const flags = buf.readUInt8(p + 13);
      p += 14;

      if (flags & 0x02) {
        if (!bufferHas(buf, p, 4)) break;
        const extra = buf.readUInt32LE(p);
        const next = entityStart + 22 + extra;
        if (extra > 0x100000 || next < p + 4 || next > buf.length) break;
        p = next;
      }

      let skin = '';
      if (flags & 0x04) {
        const skinStart = p;
        while (bufferHas(buf, p, 1)) {
          const ch = buf.readUInt8(p++);
          if (ch === 0) break;
        }
        if (p === buf.length && buf[buf.length - 1] !== 0) break;
        if (p > skinStart + 1) {
          try { skin = buf.subarray(skinStart, p - 1).toString('utf8'); } catch (_) {}
        }
      }

      const nameInfo = readUtf16Z(buf, p, 256);
      if (nameInfo.next === p || nameInfo.next > buf.length) break;
      const name = nameInfo.value || '';
      p = nameInfo.next;

      let nameId = 0;
      if (flags & 0x08) {
        if (!bufferHas(buf, p, 4)) break;
        nameId = buf.readUInt32LE(p);
        p += 4;
      }

      let status = -1;
      if (flags & 0x80) {
        if (!bufferHas(buf, p, 1)) break;
        status = buf.readUInt8(p++);
      }

      entities.push({
        id,
        x,
        y,
        size,
        flags,
        skin,
        skinId: 0,
        colorId: ((r << 16) | (g << 8) | b) >>> 0,
        nameId,
        name,
        status,
        ownedHint: false,
        offset: entityStart,
      });
    }
  } catch (_) {
    return { entities, removedIds };
  }

  return { entities, removedIds };
}

class BlobBot {
  constructor({ id, token, proxy, name, androidIdHash, onState, onTrackTarget }) {
    this.id = id;
    this.token = token;
    this.proxy = proxy;
    this.name = name;
    this.androidIdHash = androidIdHash;
    this.onState = onState;
    this.onTrackTarget = onTrackTarget;
    this.endpoint = null;
    this.ws = null;
    this.stopped = true;
    this.generation = 0;
    this.serverVersion = 0;
    this.serverFlags = 0;
    this.shortPackets = false;
    this.shortMousePackets = false;
    this.shortNamesPackets = false;
    this.nameSent = false;
    this.alive = false;
    this.lastClose = '';
    this.autoRespawnEnabled = true;
    this.lastOwnSeenAt = 0;
    this.lastDeathAt = 0;
    this.deathHandled = false;
    this.ownedIds = new Set();
    this.ownPositions = new Map();
    this.sawOwnedEntity = false;
    this.lastRespawnAt = 0;
    this.respawnTimer = null;
    this.respawnWatchdog = null;
    this.respawnPending = false;
    this.respawnAttempts = 0;
    this.movementX = 0;
    this.movementY = 0;
    this.direction = null;
    this.selfFeedEnabled = false;
    this.splitSpamEnabled = false;
    this.feedEnabled = false;
    this.trackEnabled = false;
    this.trackSpectatorMode = false;
    this.trackTargetName = '';
    this.trackLastTarget = null;
    this.trackTargetId = 0;
    this.trackTargetIds = new Set();
    this.entityCache = new Map();
    this.externalTrackEnabled = false;
    this.externalTrackAlive = false;
    this.externalTrackAt = 0;
    this.movementTimer = null;
    this.feedTimer = null;
    this.dTimer = null;
    this.startFeedTimeout = null;
    this.startDTimeout = null;
    this.trackTimer = null;
    this.trackSpectatorReady = false;
    this.messageTimer = null;
    this.messageText = '';
    this.messageIntervalMs = DEFAULT_MESSAGE_INTERVAL_MS;
    this.messageEnabled = false;
    this.messagePhase = 0;
    this.reconnectTimer = null;
    this.ffaRecycleTimer = null;
    this.ffaLoopEnabled = false;
    this.ffaDelayMs = 1000;
    this.ffaFirstUpdateSeen = false;
    this.respawnUpdateSeen = false;
  }

  stateChanged() { try { this.onState?.(this); } catch (_) {} }

  clearTimer(name) {
    if (this[name]) clearTimeout(this[name]);
    this[name] = null;
  }

  clearIntervalTimer(name) {
    if (this[name]) clearInterval(this[name]);
    this[name] = null;
  }

  clearActionTimers() {
    for (const k of ['feedTimer', 'dTimer', 'messageTimer']) this.clearIntervalTimer(k);
    this.clearTimer('startDTimeout');
    this.clearTimer('startFeedTimeout');
  }

  clearFeedTimer() {
    this.clearIntervalTimer('feedTimer');
  }

  clearRespawnTimer() {
    this.clearTimer('respawnTimer');
    this.clearTimer('respawnWatchdog');
    this.respawnPending = false;
  }

  clearAutomationTimers() {
    this.clearActionTimers();
    this.clearIntervalTimer('trackTimer');
  }

  clearReconnect() { this.clearTimer('reconnectTimer'); }

  clearFfaRecycle() { this.clearTimer('ffaRecycleTimer'); }

  setFfaLoop(enabled, delayMs = this.ffaDelayMs) {
    this.ffaLoopEnabled = !!enabled;
    if (Number.isFinite(Number(delayMs))) this.ffaDelayMs = Math.max(0, Number(delayMs));
    if (!this.ffaLoopEnabled) {
      this.clearFfaRecycle();
      this.clearReconnect();
      this.ffaFirstUpdateSeen = false;
    }
    this.stateChanged();
  }

  send(buf) {
    if (!this.ws || this.ws.readyState !== WebSocket.OPEN) return false;
    try { this.ws.send(buf); return true; } catch (_) { return false; }
  }

  startNetworkMovementLoop() {
    this.clearIntervalTimer('movementTimer');
    this.movementTimer = setInterval(() => {
      if (!this.ws || this.ws.readyState !== WebSocket.OPEN) return;

      if (this.externalTrackEnabled) {
        const age = Date.now() - Number(this.externalTrackAt || 0);
        if (!this.externalTrackAlive || !this.alive || age > TRACK_TARGET_TTL_MS) return;
        if (this.trackLastTarget) {
          this.movementX = this.trackLastTarget.x;
          this.movementY = this.trackLastTarget.y;
        }
      } else if (this.trackEnabled && this.trackLastTarget) {
        const age = Date.now() - Number(this.trackLastTarget.at || 0);
        if (age <= TRACK_TARGET_TTL_MS) {
          this.movementX = this.trackLastTarget.x;
          this.movementY = this.trackLastTarget.y;
          const p = this.shortMousePackets ? buildShortMovement(this.movementX, this.movementY) : buildLongMovement(this.movementX, this.movementY);
          this.send(p);
          return;
        }
      }

      if (!this.externalTrackEnabled && this.direction && this.alive) this.updateDirectionTarget();
      const p = this.shortMousePackets ? buildShortMovement(this.movementX, this.movementY) : buildLongMovement(this.movementX, this.movementY);
      this.send(p);
    }, 10);
  }

  stopNetworkMovementLoop() { this.clearIntervalTimer('movementTimer'); }

  connect() {
    if (this.stopped || !this.endpoint) return;
    this.clearReconnect();
    this.clearFfaRecycle();
    this.clearAutomationTimers();
    this.clearRespawnTimer();
    this.stopNetworkMovementLoop();
    this.nameSent = false;
    this.alive = false;
    this.serverVersion = 0;
    this.serverFlags = 0;
    this.shortPackets = false;
    this.shortMousePackets = false;
    this.ffaFirstUpdateSeen = false;

    if (this.proxy) console.log(`[BOT ${this.id}] proxy=${this.proxy.display}`);

    const options = {
      perMessageDeflate: false,
      handshakeTimeout: HANDSHAKE_TIMEOUT_MS,
      followRedirects: true,
      headers: {
        v: String(VERSION_CODE),
        s: S_HEADER,
        pl: PLATFORM,
        lc: LOCALE,
        gt: this.token,
      },
    };

    if (this.proxy) options.agent = new SocksProxyAgent(this.proxy.url);

    try { this.ws = new WebSocket(this.endpoint.toString(), options); }
    catch (_) { this.scheduleReconnect(); return; }

    this.ws.binaryType = 'arraybuffer';
    this.ws.on('open', () => this.onOpen());
    this.ws.on('message', (data, isBinary) => this.onMessage(data, isBinary));
    this.ws.on('error', () => {});
    this.ws.on('close', (code, reason) => this.onClose(code, reason));
    this.ws.on('pong', () => {});
    this.stateChanged();
  }

  onOpen() {
    this.lastClose = '';
    this.send(Buffer.from([0xfe, 0x05, 0x00, 0x00, 0x00]));
    this.send(Buffer.from([0xff, 0x23, 0x12, 0x38, 0x09]));
    this.send(buildClientState(this.androidIdHash));
    this.send(Buffer.from([0x11]));
    this.send(Buffer.from([0x11]));
    this.send(Buffer.from([0x11]));
    this.trackSpectatorReady = false;
    this.startNetworkMovementLoop();
    if (this.trackSpectatorMode && this.id === 1 && this.trackTargetName) this.enterSpectatorMode();
    if (!this.ffaLoopEnabled) this.clearFfaRecycle();
    this.stateChanged();
  }

  onMessage(data, isBinary) {
    const buf = Buffer.from(data);
    if (!buf.length) return;
    if (!isBinary) return;
    this.handlePacket(buf[0], buf);
  }

  handlePacket(type, buf) {
    if (type === 0x65) return this.handle65(buf);
    if (type === 0xfd) return this.handleFd(buf);
    if (type === 0x10) return this.handleUpdate(buf);
    if (type === 0x01) return;
  }

  handle65(buf) {
    if (buf.length < 9) return;
    this.serverVersion = buf.readInt32LE(1);
    this.serverFlags = buf.readInt32LE(5);
    this.shortPackets = (this.serverFlags & 0x10) !== 0;
    this.shortMousePackets = (this.serverFlags & 0x20) !== 0;
    this.shortNamesPackets = (this.serverFlags & 0x40) !== 0;
    this.clearOwnedState();
    this.alive = false;
    this.deathHandled = false;
    if (this.trackSpectatorMode && this.id === 1 && this.trackTargetName) this.enterSpectatorMode();
    else this.sendNameNow();
    this.scheduleAutomation();
    this.scheduleTrack();
  }

  handleFd(buf) {
    if (buf.length < 9) return;
    const a = buf.readInt32LE(1);
    const p = buf.readInt32LE(5);
    this.send(buildFdReply(a, p, this.serverVersion));
  }

  handleUpdate(buf) {
    if (this.ffaLoopEnabled && !this.ffaFirstUpdateSeen) {
      this.ffaFirstUpdateSeen = true;
      this.clearFfaRecycle();
      const delay = Math.max(0, Number(this.ffaDelayMs) || 0);
      console.log(`[BOT ${this.id}] FFA first update received; reconnect in ${delay / 1000}s`);
      this.ffaRecycleTimer = setTimeout(() => {
        this.ffaRecycleTimer = null;
        if (!this.stopped && this.ffaLoopEnabled && this.ws && this.ws.readyState === WebSocket.OPEN) {
          console.log(`[BOT ${this.id}] FFA recycle: reconnecting session`);
          try { this.ws.close(1000, 'FFA first-update recycle'); } catch (_) {}
        }
      }, delay);
    }

    this.respawnUpdateSeen = true;
    const parsed = this.shortPackets
      ? parseShortUpdate(buf, this.shortNamesPackets, this.serverVersion)
      : parseLongUpdate(buf, this.shortNamesPackets, this.serverVersion);
    const entities = parsed.entities;

    for (const e of entities) {
      const cached = this.entityCache.get(e.id) || {};
      this.entityCache.set(e.id, {
        name: e.name ? cleanName(e.name) : (cached.name || ''),
        x: Number(e.x) || 0,
        y: Number(e.y) || 0,
        size: Number(e.size) || 0,
        at: Date.now(),
      });
    }
    for (const id of parsed.removedIds) this.entityCache.delete(id);

    const wasAlive = this.alive;
    let ownSeenInPacket = false;
    for (const e of entities) {
      if (e.ownedHint) {
        ownSeenInPacket = true;
        this.ownedIds.add(e.id);
        this.ownPositions.set(e.id, { x: e.x, y: e.y, size: e.size });
        this.sawOwnedEntity = true;
        this.alive = true;
        this.deathHandled = false;
        this.lastOwnSeenAt = Date.now();
        this.respawnAttempts = 0;
      }
    }

    let died = false;
    for (const id of parsed.removedIds) {
      if (this.ownedIds.delete(id)) {
        this.ownPositions.delete(id);
        died = true;
      }
    }

    if (died && this.sawOwnedEntity && this.ownedIds.size === 0) {
      this.markDeadAndRespawn('owned cells removed');
    }

    if (ownSeenInPacket && !wasAlive) {
      this.clearTimer('respawnWatchdog');
      this.respawnPending = false;
      this.respawnAttempts = 0;
      this.deathHandled = false;
      this.scheduleAutomation();
    }

    if (this.trackEnabled && this.id === 1) {
      const wanted = cleanName(this.trackTargetName)
        .normalize('NFKC')
        .replace(/[\u200B-\u200D\uFEFF]/g, '')
        .toLocaleLowerCase();
      if (wanted) {
        const now = Date.now();
        for (const e of entities) {
          const seenName = cleanName(e.name)
            .normalize('NFKC')
            .replace(/[\u200B-\u200D\uFEFF]/g, '')
            .toLocaleLowerCase();
          if (seenName === wanted) this.trackTargetIds.add(e.id);
        }

        for (const id of Array.from(this.trackTargetIds)) {
          const cached = this.entityCache.get(id);
          if (!cached || now - cached.at > TRACK_TARGET_TTL_MS) this.trackTargetIds.delete(id);
        }

        if (!this.trackTargetIds.size) {
          for (const [id, e] of this.entityCache.entries()) {
            const cachedName = cleanName(e.name)
              .normalize('NFKC')
              .replace(/[\u200B-\u200D\uFEFF]/g, '')
              .toLocaleLowerCase();
            if (cachedName === wanted && now - e.at <= TRACK_TARGET_TTL_MS) this.trackTargetIds.add(id);
          }
        }

        let sx = 0;
        let sy = 0;
        let total = 0;
        let largestSize = 0;
        let primaryId = 0;
        let cells = 0;
        for (const id of this.trackTargetIds) {
          const live = this.entityCache.get(id);
          if (!live || now - live.at > TRACK_TARGET_TTL_MS) continue;
          const weight = Math.max(1, Number(live.size) || 1);
          sx += live.x * weight;
          sy += live.y * weight;
          total += weight;
          if ((live.size || 0) >= largestSize) {
            largestSize = live.size || 0;
            primaryId = Number(id) || 0;
          }
          cells++;
        }

        if (cells > 0 && total > 0) {
          const target = {
            x: Math.max(MAP_MIN, Math.min(MAP_MAX, Math.round(sx / total))),
            y: Math.max(MAP_MIN, Math.min(MAP_MAX, Math.round(sy / total))),
            size: largestSize,
            cells,
            id: primaryId,
            at: now,
          };
          const previousId = this.trackTargetId;
          this.trackLastTarget = target;
          this.trackTargetId = primaryId;
          this.movementX = target.x;
          this.movementY = target.y;
          if (this.id === 1 && (previousId !== primaryId || Math.abs((this._lastLoggedTrackX ?? 0) - target.x) >= 250 || Math.abs((this._lastLoggedTrackY ?? 0) - target.y) >= 250)) {
            console.log(`[TRACK] Bot 1 target "${this.trackTargetName}" id=${primaryId} cells=${cells} x=${target.x} y=${target.y}`);
            this._lastLoggedTrackX = target.x;
            this._lastLoggedTrackY = target.y;
          }
          try { this.onTrackTarget?.(target); } catch (_) {}
        }
      }
    }

    if (this.selfFeedEnabled) {
      this.updateDirectionTarget();
    }
  }

  sendNameNow() {
    const ok = this.send(buildNamePacket(this.name));
    if (ok) {
      this.nameSent = true;
      this.stateChanged();
    }
    return ok;
  }

  updateDirectionTarget() {
    if (!this.direction) return;

    let sx = 0;
    let sy = 0;
    let total = 0;

    for (const pos of this.ownPositions.values()) {
      const weight = Math.max(1, Number(pos.size) || 1);
      sx += pos.x * weight;
      sy += pos.y * weight;
      total += weight;
    }

    const cx = total > 0 ? Math.round(sx / total) : 0;
    const cy = total > 0 ? Math.round(sy / total) : 0;

    // The DEX does not send MAP_MIN/MAP_MAX when a direction key is pressed.
    // It stores a screen-space target and q.d() converts that target around
    // the current camera center.  A direction is therefore represented by a
    // point on the same ray from the current owned-cell center.
    const target = (x, y) => {
      this.movementX = Math.max(MAP_MIN, Math.min(MAP_MAX, Math.round(x)));
      this.movementY = Math.max(MAP_MIN, Math.min(MAP_MAX, Math.round(y)));
    };

    switch (this.direction.key) {
      case 0:
        // Explicitly reproduce the requested 0,0 target.
        target(0, 0);
        break;
      case 8:
        target(cx, cy - TREND_DISTANCE);
        break;
      case 2:
        target(cx, cy + TREND_DISTANCE);
        break;
      case 4:
        target(cx - TREND_DISTANCE, cy);
        break;
      case 6:
        target(cx + TREND_DISTANCE, cy);
        break;
    }
  }

  clearOwnedState() {
    this.ownedIds.clear();
    this.ownPositions.clear();
    this.sawOwnedEntity = false;
  }

  enterSpectatorMode() {
    if (!this.ws || this.ws.readyState !== WebSocket.OPEN) return false;
    this.alive = false;
    this.clearOwnedState();
    this.send(Buffer.from([0x11]));
    this.send(Buffer.from([0x11]));
    this.send(Buffer.from([0x11]));
    const ok = this.send(Buffer.from([0x01]));
    if (ok) this.trackSpectatorReady = true;
    return ok;
  }

  sendDAction() {
    if (!this.ws || this.ws.readyState !== WebSocket.OPEN) return false;
    return this.send(buildDActionPacket());
  }

  sendFeedAction() {
    if (!this.ws || this.ws.readyState !== WebSocket.OPEN) return false;
    return this.send(buildFeedActionPacket(this.serverVersion));
  }

  startFeed() {
    this.clearFeedTimer();
    if (!this.ws || this.ws.readyState !== WebSocket.OPEN) return false;

    this.sendFeedAction();
    this.feedTimer = setInterval(() => {
      if (!this.ws || this.ws.readyState !== WebSocket.OPEN) return;
      this.sendFeedAction();
    }, FEED_INTERVAL_MS);
    return true;
  }

  stopFeed() {
    this.clearFeedTimer();
  }

  startDSpam() {
    this.clearIntervalTimer('dTimer');
    if (!this.ws || this.ws.readyState !== WebSocket.OPEN) return false;

    this.sendDAction();
    this.dTimer = setInterval(() => {
      if (!this.ws || this.ws.readyState !== WebSocket.OPEN || (!this.selfFeedEnabled && !this.splitSpamEnabled)) return;
      this.sendDAction();
    }, D_INTERVAL_MS);
    return true;
  }

  sendMessageNow(withMarker = false) {
    if (!this.ws || this.ws.readyState !== WebSocket.OPEN || !this.messageText) return false;
    const payload = withMarker ? `${this.messageText}${ZWNJ}` : this.messageText;
    return this.send(buildChatPacket(payload));
  }

  startMessageLoop() {
    this.clearIntervalTimer('messageTimer');
    this.messagePhase = 0;
    if (!this.messageEnabled || !this.messageText || !this.ws || this.ws.readyState !== WebSocket.OPEN) return false;
    this.sendMessageNow(false);
    this.messagePhase = 1;
    this.messageTimer = setInterval(() => {
      if (!this.messageEnabled || !this.ws || this.ws.readyState !== WebSocket.OPEN) return;
      this.sendMessageNow(this.messagePhase === 1);
      this.messagePhase = this.messagePhase === 1 ? 0 : 1;
    }, Math.max(100, this.messageIntervalMs));
    return true;
  }

  setMessage(enabled, intervalMs = this.messageIntervalMs, text = this.messageText) {
    this.messageEnabled = !!enabled;
    this.messageIntervalMs = Math.max(100, Number(intervalMs) || DEFAULT_MESSAGE_INTERVAL_MS);
    this.messageText = String(text ?? '');
    if (this.messageEnabled) this.startMessageLoop();
    else this.clearIntervalTimer('messageTimer');
    this.stateChanged();
  }

  markDeadAndRespawn(reason = '') {
    if (this.trackSpectatorMode && this.id === 1) {
      this.alive = false;
      this.deathHandled = true;
      this.clearOwnedState();
      this.clearRespawnTimer();
      this.clearTimer('respawnWatchdog');
      if (this.ws && this.ws.readyState === WebSocket.OPEN) this.enterSpectatorMode();
      this.stateChanged();
      return true;
    }
    if (this.deathHandled && this.respawnPending) return false;
    this.alive = false;
    this.lastDeathAt = Date.now();
    this.deathHandled = true;
    this.clearOwnedState();
    this.clearActionTimers();
    this.clearFfaRecycle();
    this.requestRespawn(reason);
    this.stateChanged();
    return true;
  }

  scheduleAutomation() {
    this.clearActionTimers();
    if (!this.ws || this.ws.readyState !== WebSocket.OPEN) return;

    if (this.direction) this.updateDirectionTarget();
    if (this.selfFeedEnabled || this.splitSpamEnabled) this.startDSpam();
    if (this.feedEnabled || this.selfFeedEnabled) this.startFeed();
    if (this.messageEnabled) this.startMessageLoop();
  }

  scheduleTrack() {
    this.clearIntervalTimer('trackTimer');
    if (!this.trackEnabled || !this.trackTargetName) return;
    this.trackTimer = setInterval(() => {
      if (!this.trackEnabled || !this.ws || this.ws.readyState !== WebSocket.OPEN) return;
      if (this.trackSpectatorMode && this.id === 1 && !this.trackSpectatorReady) this.enterSpectatorMode();
      if (this.trackLastTarget) {
        const age = Date.now() - Number(this.trackLastTarget.at || 0);
        if (age <= TRACK_TARGET_TTL_MS) {
          this.movementX = this.trackLastTarget.x;
          this.movementY = this.trackLastTarget.y;
          this.sendTrackTargetNow();
        }
      }
    }, TRACK_INTERVAL_MS);
  }

  performRespawn() {
    this.respawnPending = false;
    this.respawnTimer = null;
    this.lastRespawnAt = Date.now();
    this.respawnAttempts++;
    this.generation++;
    this.clearAutomationTimers();
    this.clearTimer('respawnWatchdog');
    this.alive = false;
    this.deathHandled = true;
    this.respawnUpdateSeen = false;
    this.clearOwnedState();

    if (this.stopped || !this.autoRespawnEnabled) return false;

    if (this.ws && this.ws.readyState === WebSocket.OPEN) {
      const resetOk = this.send(Buffer.from([0x11])) &&
        this.send(Buffer.from([0x11])) &&
        this.send(Buffer.from([0x11])) &&
        this.send(Buffer.from([0x01]));
      const nameOk = resetOk && this.send(buildNamePacket(this.name));
      if (nameOk) {
        this.nameSent = true;
        this.respawnWatchdog = setTimeout(() => {
          this.respawnWatchdog = null;
          if (this.stopped || !this.autoRespawnEnabled || this.alive || this.respawnPending) return;
          if (!this.ws || this.ws.readyState !== WebSocket.OPEN) {
            this.respawnAttempts = 0;
            this.scheduleReconnect(25);
            return;
          }
          if (this.respawnAttempts < MAX_RESPAWN_RETRIES) {
            this.requestRespawn('same-session spawn retry');
          } else {
            this.respawnAttempts = 0;
            this.scheduleReconnect(250);
          }
        }, RESPAWN_CONFIRM_TIMEOUT_MS);
        this.stateChanged();
        return true;
      }
    }

    if (!this.ws || this.ws.readyState === WebSocket.CLOSED || this.ws.readyState === WebSocket.CLOSING) {
      this.respawnAttempts = 0;
      this.clearReconnect();
      this.reconnectTimer = setTimeout(() => {
        this.reconnectTimer = null;
        if (!this.stopped && this.autoRespawnEnabled) this.connect();
      }, 25);
      this.stateChanged();
      return true;
    }

    this.respawnWatchdog = setTimeout(() => {
      this.respawnWatchdog = null;
      if (!this.stopped && this.autoRespawnEnabled && !this.alive && !this.respawnPending) {
        this.requestRespawn('same-session send retry');
      }
    }, RESPAWN_CONFIRM_TIMEOUT_MS);
    this.stateChanged();
    return false;
  }

  requestRespawn(reason = '') {
    if (!this.autoRespawnEnabled || this.stopped || this.alive) return false;
    if (this.respawnPending) return false;

    const elapsed = Date.now() - this.lastRespawnAt;
    const waitMs = this.lastRespawnAt > 0 ? Math.max(0, MIN_RESPAWN_INTERVAL_MS - elapsed) : 0;

    this.respawnPending = true;
    if (waitMs > 0) {
      this.respawnTimer = setTimeout(() => {
        this.respawnTimer = null;
        if (!this.stopped && this.autoRespawnEnabled) this.performRespawn();
        else this.respawnPending = false;
      }, waitMs);
      return true;
    }

    this.performRespawn();
    return true;
  }

  setSplitSpam(enabled = true) {
    this.splitSpamEnabled = !!enabled;
    this.generation++;
    if (this.splitSpamEnabled) this.startDSpam();
    else if (!this.selfFeedEnabled) this.clearIntervalTimer('dTimer');
    this.stateChanged();
  }

  setSelfFeed(enabled = true) {
    this.selfFeedEnabled = !!enabled;
    this.generation++;
    if (!this.selfFeedEnabled) this.clearIntervalTimer('dTimer');
    this.scheduleAutomation();
    this.stateChanged();
  }

  setTrendDirection(directionName) {
    const d = DIRECTIONS[String(directionName)];
    if (!d) throw new Error('اختر اتجاهًا من 0 أو 6 أو 2 أو 4 أو 8.');
    this.direction = d;
    this.generation++;
    this.updateDirectionTarget();
    this.stateChanged();
  }

  stopSelfFeed() {
    this.setSelfFeed(false);
  }

  setFeedEnabled(enabled) {
    this.feedEnabled = !!enabled;
    this.generation++;

    if (this.feedEnabled) this.startFeed();
    else this.stopFeed();

    if (this.selfFeedEnabled && this.feedEnabled) this.startDSpam();
    if (!this.selfFeedEnabled) this.clearIntervalTimer('dTimer');

    this.stateChanged();
  }

  setExternalTrack(enabled = true) {
    this.externalTrackEnabled = !!enabled;
    this.externalTrackAlive = false;
    this.externalTrackAt = 0;

    if (this.externalTrackEnabled) {
      this.trackEnabled = true;
      this.trackTargetName = '';
      this.trackLastTarget = null;
      this.trackTargetId = 0;
      this.trackTargetIds.clear();
      this.entityCache.clear();
      this.trackSpectatorMode = false;
      this.trackSpectatorReady = false;
      this.clearIntervalTimer('trackTimer');
    } else {
      this.trackEnabled = false;
      this.trackTargetName = '';
      this.trackLastTarget = null;
      this.trackTargetId = 0;
      this.trackTargetIds.clear();
      this.entityCache.clear();
    }
    this.stateChanged();
  }

  setExternalTrackTarget(target) {
    if (!this.externalTrackEnabled || !target) return false;

    const alive = target.alive !== false;
    this.externalTrackAlive = alive;
    this.externalTrackAt = Number(target.at) || Date.now();

    if (!alive) return false;

    const x = Number(target.x);
    const y = Number(target.y);
    if (!Number.isFinite(x) || !Number.isFinite(y)) return false;

    this.trackLastTarget = {
      x: Math.max(MAP_MIN, Math.min(MAP_MAX, Math.round(x))),
      y: Math.max(MAP_MIN, Math.min(MAP_MAX, Math.round(y))),
      at: this.externalTrackAt,
    };
    this.movementX = this.trackLastTarget.x;
    this.movementY = this.trackLastTarget.y;
    return true;
  }

  setTrackName(name) {
    const n = cleanName(name);
    if (!n) throw new Error('اسم التتبع فارغ.');
    this.externalTrackEnabled = false;
    this.externalTrackAlive = false;
    this.externalTrackAt = 0;
    this.trackTargetName = n;
    this.trackEnabled = true;
    this.trackSpectatorMode = this.id === 1;
    this.trackLastTarget = null;
    this.trackTargetId = 0;
    this.trackTargetIds.clear();
    this.entityCache.clear();
    this.trackSpectatorReady = false;
    if (this.trackSpectatorMode && this.ws && this.ws.readyState === WebSocket.OPEN) this.enterSpectatorMode();
    this.scheduleTrack();
    this.stateChanged();
  }

  setTrackTarget(target) {
    if (!target || !Number.isFinite(Number(target.x)) || !Number.isFinite(Number(target.y))) return false;
    this.trackLastTarget = {
      x: Math.max(MAP_MIN, Math.min(MAP_MAX, Math.round(Number(target.x)))),
      y: Math.max(MAP_MIN, Math.min(MAP_MAX, Math.round(Number(target.y)))),
      size: Number(target.size) || 0,
      cells: Number(target.cells) || 1,
      id: Number(target.id) || 0,
      at: Number(target.at) || Date.now(),
    };
    this.movementX = this.trackLastTarget.x;
    this.movementY = this.trackLastTarget.y;
    this.sendTrackTargetNow();
    return true;
  }

  sendTrackTargetNow() {
    if (!this.trackEnabled || !this.trackLastTarget || !this.ws || this.ws.readyState !== WebSocket.OPEN) return false;
    const age = Date.now() - Number(this.trackLastTarget.at || 0);
    if (age > TRACK_TARGET_TTL_MS) return false;
    this.movementX = this.trackLastTarget.x;
    this.movementY = this.trackLastTarget.y;
    const packet = this.shortMousePackets ? buildShortMovement(this.movementX, this.movementY) : buildLongMovement(this.movementX, this.movementY);
    return this.send(packet);
  }

  stopTrack() {
    const wasSpectator = this.trackSpectatorMode;
    this.trackEnabled = false;
    this.externalTrackEnabled = false;
    this.externalTrackAlive = false;
    this.externalTrackAt = 0;
    this.trackSpectatorMode = false;
    this.trackTargetName = '';
    this.trackLastTarget = null;
    this.trackTargetId = 0;
    this.trackTargetIds.clear();
    this.entityCache.clear();
    this.trackSpectatorReady = false;
    this.clearIntervalTimer('trackTimer');
    if (wasSpectator && this.id === 1 && this.ws && this.ws.readyState === WebSocket.OPEN && !this.alive) this.sendNameNow();
    this.stateChanged();
  }

  setAutoRespawn(enabled) {
    this.autoRespawnEnabled = !!enabled;
    if (!this.autoRespawnEnabled) this.clearRespawnTimer();
    else this.respawnAttempts = 0;
    this.stateChanged();
  }

  setName(name) {
    const n = cleanName(name);
    if (!n) throw new Error('الاسم فارغ.');
    this.name = n;
    if (this.ws && this.ws.readyState === WebSocket.OPEN) this.sendNameNow();
    this.stateChanged();
  }

  setProxy(proxy) {
    this.proxy = proxy || null;
    this.stateChanged();
  }

  setEndpoint(endpoint) {
    const same = this.endpoint && endpoint.toString() === this.endpoint.toString();
    this.endpoint = endpoint;
    if (!same && this.ws && [WebSocket.OPEN, WebSocket.CONNECTING].includes(this.ws.readyState)) {
      try { this.ws.close(1000, 'server changed'); } catch (_) {}
    }
    this.stateChanged();
  }

  onClose(code, reason) {
    this.stopNetworkMovementLoop();
    this.clearFfaRecycle();
    this.clearAutomationTimers();
    this.alive = false;
    this.lastClose = `${code}${reason ? ` ${Buffer.from(reason).toString('utf8')}` : ''}`;
    this.stateChanged();
    if (!this.stopped && !this.respawnPending && !this.reconnectTimer) {
      if (this.ffaLoopEnabled) this.scheduleReconnect(FFA_RECONNECT_MS);
      else if (code !== 4001 && code !== 1008) this.scheduleReconnect(RECONNECT_MS);
    }
  }

  scheduleReconnect(delayMs = RECONNECT_MS) {
    this.clearReconnect();
    this.reconnectTimer = setTimeout(() => {
      this.reconnectTimer = null;
      if (!this.stopped) this.connect();
    }, Math.max(0, Number(delayMs) || 0));
  }

  start(endpoint) {
    if (!this.stopped) return;
    this.stopped = false;
    this.endpoint = endpoint;
    this.connect();
  }

  stop() {
    this.stopped = true;
    this.generation++;
    this.clearReconnect();
    this.clearFfaRecycle();
    this.clearAutomationTimers();
    this.clearRespawnTimer();
    this.stopNetworkMovementLoop();
    if (this.ws && [WebSocket.OPEN, WebSocket.CONNECTING].includes(this.ws.readyState)) {
      try { this.ws.close(1000, 'manual stop'); } catch (_) {}
    }
    this.alive = false;
    this.stateChanged();
  }

  isOnline() { return !!(this.ws && this.ws.readyState === WebSocket.OPEN); }
}

const DIRECTIONS = Object.freeze({
  '0': { key: 0, name: '0', label: 'Center' },
  '6': { key: 6, name: '6', label: 'Right' },
  '2': { key: 2, name: '2', label: 'Down' },
  '4': { key: 4, name: '4', label: 'Left' },
  '8': { key: 8, name: '8', label: 'Up' },
});

class BotManager {
  constructor(tokens, proxies = []) {
    const baseAndroidId = getBaseAndroidId();
    this.baseAndroidId = baseAndroidId;
    this.sourceTokens = tokens.length ? tokens.map(v => ({ ...v })) : [];
    this.endpoint = null;
    this.name = 'ahmed';
    this.autoRespawnEnabled = true;
    this.proxies = proxies;
    this.selectedProxies = [];
    this.running = false;
    this.starting = false;
    this.botCount = 1;
    this.direction = DIRECTIONS['0'];
    this.selfFeedEnabled = false;
    this.feedEnabled = false;
    this.trackEnabled = false;
    this.trackTargetName = '';
    this.phoneTrackEnabled = false;
    this.externalTrackLast = null;
    this.trackBridgeSocket = null;
    this.splitSpamEnabled = false;
    this.messageEnabled = false;
    this.messageIntervalMs = DEFAULT_MESSAGE_INTERVAL_MS;
    this.messageText = '';
    this.listeners = new Set();
    this.createBots(this.botCount);
    this.startTrackBridge();
  }

  startTrackBridge() {
    if (this.trackBridgeSocket) return;

    const socket = dgram.createSocket('udp4');
    this.trackBridgeSocket = socket;

    socket.on('error', err => {
      console.log(`[TRACK] bridge error: ${err.message}`);
    });

    socket.on('message', msg => {
      let data;
      try { data = JSON.parse(msg.toString('utf8')); } catch (_) { return; }
      if (!data || data.type !== 'game_coords') return;
      if (!this.phoneTrackEnabled || !this.trackEnabled) return;

      if (data.alive === false) {
        this.externalTrackLast = { alive: false, at: Date.now() };
        for (const bot of this.bots) bot.setExternalTrackTarget({ alive: false });
        return;
      }

      const x = Number(data.x);
      const y = Number(data.y);
      if (!Number.isFinite(x) || !Number.isFinite(y)) return;

      const target = { x, y, alive: true, at: Date.now() };
      this.externalTrackLast = target;
      for (const bot of this.bots) bot.setExternalTrackTarget(target);
    });

    socket.bind(TRACK_BRIDGE_PORT, TRACK_BRIDGE_HOST, () => {
      console.log(`[TRACK] phone bridge listening on ${TRACK_BRIDGE_HOST}:${TRACK_BRIDGE_PORT}`);
    });
  }

  createBots(count) {
    if (!this.sourceTokens.length) throw new Error('لا يوجد token.txt صالح.');
    this.bots = Array.from({ length: count }, (_, i) => {
      const tokenEntry = this.sourceTokens[0];
      const token = tokenEntry.token;
      const bot = new BlobBot({
        id: i + 1,
        token,
        proxy: null,
        name: this.name,
        androidIdHash: this.baseAndroidId ? javaStringHashCode(`${this.baseAndroidId}-${i + 1}`) : stableBotAndroidHash(i + 1, token),
        onState: () => this.stateChanged(),
        onTrackTarget: (target) => this.publishTrackTarget(i + 1, target),
      });
      bot.autoRespawnEnabled = this.autoRespawnEnabled;
      bot.direction = this.direction;
      bot.feedEnabled = this.feedEnabled;
      bot.selfFeedEnabled = this.selfFeedEnabled;
      bot.trackEnabled = this.trackEnabled;
      bot.trackSpectatorMode = this.trackEnabled && !this.phoneTrackEnabled && i === 0;
      bot.trackTargetName = this.trackTargetName;
      bot.externalTrackEnabled = this.phoneTrackEnabled;
      bot.splitSpamEnabled = this.splitSpamEnabled;
      bot.messageEnabled = this.messageEnabled;
      bot.messageIntervalMs = this.messageIntervalMs;
      bot.messageText = this.messageText;
      bot.tokenFile = tokenEntry.file;
      return bot;
    });
    this.botCount = count;
  }

  onState(fn) { this.listeners.add(fn); return () => this.listeners.delete(fn); }
  stateChanged() { for (const fn of this.listeners) { try { fn(); } catch (_) {} } }

  setEndpoint(endpoint) {
    this.endpoint = endpoint;
    for (const bot of this.bots) bot.setEndpoint(endpoint);
    this.stateChanged();
  }

  setName(name) {
    this.name = cleanName(name);
    if (!this.name) throw new Error('الاسم فارغ.');
    for (const bot of this.bots) bot.setName(this.name);
    this.stateChanged();
  }

  setBotCount(count) {
    const n = Number(count);
    if (!Number.isInteger(n) || n < 1) throw new Error('عدد البوتات يجب أن يكون رقمًا صحيحًا أكبر من أو يساوي 1.');
    const wasRunning = this.running || this.starting;
    this.stopAll();
    this.createBots(n);
    if (wasRunning && this.endpoint) return this.startAll();
    this.stateChanged();
  }

  async startAll() {
    if (!this.endpoint) throw new Error('حدد Server أولًا.');
    if (this.running || this.starting) return;
    this.starting = true;
    try {
      let selected = [];
      let startCount = this.bots.length;

      if (this.proxies.length) {
        const needed = Math.ceil(this.bots.length / MAX_BOTS_PER_PROXY);
        const result = await selectFastProxies(this.proxies, this.endpoint, needed);
        selected = result.selected;
        if (!selected.length) throw new Error('لا يوجد SOCKS proxy حي للوصول إلى السيرفر.');
        startCount = Math.min(this.bots.length, selected.length * MAX_BOTS_PER_PROXY);
      }

      this.selectedProxies = selected;
      for (let i = 0; i < this.bots.length; i++) {
        const bot = this.bots[i];
        if (i >= startCount) {
          bot.stop();
          continue;
        }
        if (selected.length) bot.setProxy(selected[Math.floor(i / MAX_BOTS_PER_PROXY)]);
        else bot.setProxy(null);
        if (i === 0) {
          console.log(`[TOKEN] Shared token.txt assigned to bots 1-${this.bots.length}.`);
        }
        bot.setFfaLoop(this.ffaLoopEnabled);
        bot.start(this.endpoint);
      }
      this.running = true;
      this.stateChanged();
    } finally {
      this.starting = false;
      this.stateChanged();
    }
  }

  stopAll() {
    this.running = false;
    this.starting = false;
    this.ffaLoopEnabled = false;
    for (const bot of this.bots) bot.setFfaLoop(false);
    for (const bot of this.bots) bot.stop();
    this.stateChanged();
  }
  async setFfaLoop(enabled = true, delayMs = 1000) {
    const next = !!enabled;
    if (next && !this.endpoint) throw new Error('حدد Server أولًا.');
    if (next) {
      const delay = Number(delayMs);
      if (!Number.isFinite(delay) || delay < 0) throw new Error('اكتب عدد ثواني صحيح أو عشري أكبر من أو يساوي 0.');
      this.ffaDelayMs = delay;
    }
    this.ffaLoopEnabled = next;
    for (const bot of this.bots) bot.setFfaLoop(next, this.ffaDelayMs);
    if (next && !this.running && !this.starting) await this.startAll();
    this.stateChanged();
  }
  setSelfFeed(enabled = true) { this.selfFeedEnabled = !!enabled; for (const bot of this.bots) bot.setSelfFeed(this.selfFeedEnabled); }
  stopSelfFeed() { this.setSelfFeed(false); }
  setTrendDirection(directionName) { this.direction = DIRECTIONS[String(directionName)]; if (!this.direction) throw new Error('اختر اتجاهًا من 0 أو 6 أو 2 أو 4 أو 8.'); for (const bot of this.bots) bot.setTrendDirection(directionName); }
  setFeed(enabled) { this.feedEnabled = !!enabled; for (const bot of this.bots) bot.setFeedEnabled(this.feedEnabled); }
  setTrackName(name) {
    const n = cleanName(name);
    if (!n) throw new Error('اسم التتبع فارغ.');
    this.phoneTrackEnabled = false;
    this.trackEnabled = true;
    this.trackTargetName = n;
    this.trackLastTarget = null;
    for (const [idx, bot] of this.bots.entries()) {
      bot.setTrackName(n);
      if (idx !== 0) bot.trackSpectatorMode = false;
    }
  }
  setPhoneTrack(enabled = true) {
    this.phoneTrackEnabled = !!enabled;
    this.trackEnabled = this.phoneTrackEnabled;
    this.trackTargetName = '';
    this.trackLastTarget = null;
    this.externalTrackLast = null;

    for (const bot of this.bots) {
      bot.setExternalTrack(this.phoneTrackEnabled);
    }

    this.stateChanged();
    return this.phoneTrackEnabled;
  }

  publishTrackTarget(sourceBotId, target) {
    if (!this.trackEnabled || sourceBotId !== 1 || !target) return;
    this.trackLastTarget = { ...target };
    for (const bot of this.bots) {
      bot.setTrackTarget(target);
    }
  }
  stopTrack() {     this.phoneTrackEnabled = false;
this.trackEnabled = false; this.trackTargetName = ''; this.trackLastTarget = null; for (const bot of this.bots) bot.stopTrack(); }
  setSplitSpam(enabled = true) {
    this.splitSpamEnabled = !!enabled;
    for (const bot of this.bots) bot.setSplitSpam(this.splitSpamEnabled);
    this.stateChanged();
    return this.splitSpamEnabled;
  }
  splitAll() {
    const next = !this.splitSpamEnabled;
    this.setSplitSpam(next);
    return next;
  }
  setAutoRespawn(enabled) { this.autoRespawnEnabled = !!enabled; for (const bot of this.bots) bot.setAutoRespawn(this.autoRespawnEnabled); }
  setMessage(enabled, intervalMs, text) {
    this.messageEnabled = !!enabled;
    this.messageIntervalMs = Math.max(100, Number(intervalMs) || DEFAULT_MESSAGE_INTERVAL_MS);
    this.messageText = String(text ?? '');
    for (const bot of this.bots) bot.setMessage(this.messageEnabled, this.messageIntervalMs, this.messageText);
  }
  stopMessage() { this.setMessage(false, this.messageIntervalMs, this.messageText); }

  summary() {
    const working = this.bots.filter(b => b.isOnline()).length;
    const auto = this.autoRespawnEnabled ? 'ON' : 'OFF';
    const ffa = this.ffaLoopEnabled ? `ON / ${this.ffaDelayMs}s after first update` : 'OFF';
    const feedOn = this.bots.some(b => b.feedEnabled) ? 'ON' : 'OFF';
    const sf = this.bots.some(b => b.selfFeedEnabled);
    const trend = this.direction ? this.direction.name : '0';
    const msgOn = this.messageEnabled ? 'ON' : 'OFF';
    const proxyText = this.proxies.length ? `
Proxies selected: ${this.selectedProxies.length} (max ${MAX_BOTS_PER_PROXY}/proxy)` : '';
    const msgText = this.messageText ? `
MSG: ${msgOn} / ${this.messageIntervalMs / 1000}s` : `
MSG: ${msgOn}`;
    const tokenSummary = this.sourceTokens.length ? `token.txt (shared): ${this.bots.length}` : 'none';
    return `Bots: ${this.bots.length}
Tokens: ${tokenSummary}
Working: ${working}
FFA Loop: ${ffa}
AutoRespawn: ${auto}
Feed: ${feedOn}
SelfFeed: ${sf ? 'ON' : 'OFF'}
Trend: ${trend}
Track Me: ${this.phoneTrackEnabled ? 'ON' : 'OFF'}
Track Name: ${this.trackTargetName ? this.trackTargetName : 'OFF'}
SPLIT: ${this.splitSpamEnabled ? 'ON / 50ms' : 'OFF'}${msgText}${proxyText}`;
  }
}

const MAIN_KB = {
  reply_markup: { inline_keyboard: [
    [{ text: 'ON', callback_data: 'on' }, { text: 'OFF', callback_data: 'off' }],
    [{ text: 'Status', callback_data: 'status' }, { text: 'FFA', callback_data: 'ffa:toggle' }],
    [{ text: 'Feed', callback_data: 'feed:start' }, { text: 'Stop Feed', callback_data: 'feed:stop' }],
    [{ text: 'SelfFeed', callback_data: 'self_feed' }, { text: 'Stop SelfFeed', callback_data: 'self_feed:stop' }],
    [{ text: 'Trends', callback_data: 'trends' }, { text: 'msg', callback_data: 'msg' }],
    [{ text: 'إيقاف msg', callback_data: 'msg:stop' }, { text: 'عدد بوتات', callback_data: 'botcount' }],
    [{ text: 'Auto RSP', callback_data: 'autorespawn' }, { text: 'SPLIT', callback_data: 'split' }],
    [{ text: 'Set IP', callback_data: 'change_ip' }, { text: 'Set Name', callback_data: 'change_name' }],
    [{ text: 'Track Me', callback_data: 'track:me' }, { text: 'Track the name', callback_data: 'track' }],
  ]},
};

const TREND_KB = {
  reply_markup: { inline_keyboard: [
    [{ text: '6', callback_data: 'trend:6' }, { text: '2', callback_data: 'trend:2' }, { text: '0', callback_data: 'trend:0' }],
    [{ text: '4', callback_data: 'trend:4' }, { text: '8', callback_data: 'trend:8' }],
    [{ text: 'Back', callback_data: 'menu' }],
  ]},
};

const TRACK_KB = {
  reply_markup: { inline_keyboard: [
    [{ text: 'Stop Track', callback_data: 'track:stop' }],
    [{ text: 'Back', callback_data: 'menu' }],
  ]},
};

class TelegramController {
  constructor(token, manager) {
    this.token = token;
    this.manager = manager;
    this.offset = 0;
    this.pending = new Map();
    this.running = false;
  }

  url(method) { return `https://api.telegram.org/bot${this.token}/${method}`; }

  api(method, payload = {}, timeoutMs = 40000) {
    return new Promise((resolve, reject) => {
      const body = JSON.stringify(payload);
      const req = https.request(this.url(method), {
        method: 'POST',
        headers: { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(body) },
        timeout: timeoutMs,
      }, res => {
        let data = '';
        res.setEncoding('utf8');
        res.on('data', c => data += c);
        res.on('end', () => {
          try {
            const parsed = JSON.parse(data);
            if (!parsed.ok) return reject(new Error(parsed.description || `Telegram ${method} failed`));
            resolve(parsed.result);
          } catch (e) { reject(new Error(`Telegram response parse error: ${e.message}`)); }
        });
      });
      req.on('timeout', () => req.destroy(new Error('Telegram timeout')));
      req.on('error', reject);
      req.write(body);
      req.end();
    });
  }

  send(chatId, text, extra = {}) { return this.api('sendMessage', { chat_id: chatId, text, ...extra }); }

  async main(chatId) { await this.send(chatId, this.manager.summary(), MAIN_KB); }
  async trendMenu(chatId) { await this.send(chatId, 'اختار Trend: 6 أو 2 أو 4 أو 8، أو 0 للمنتصف 0,0', TREND_KB); }

  async handleMessage(msg) {
    const chatId = msg.chat?.id;
    if (chatId == null) return;
    const text = String(msg.text || '').trim();
    if (!text) return;

    const parts = text.split(/\s+/, 2);
    const command = parts[0].toLowerCase();
    const arg = parts[1] || '';

    if (command === '/start' || command === '/menu') {
      this.pending.delete(chatId);
      return this.main(chatId);
    }

    if (command === '/feed') {
      this.pending.delete(chatId);
      this.manager.setFeed(true);
      return this.main(chatId);
    }

    if (command === '/feedoff' || command === '/stopfeed') {
      this.pending.delete(chatId);
      this.manager.setFeed(false);
      return this.main(chatId);
    }

    if (command === '/selffeed') {
      this.pending.delete(chatId);
      this.manager.setSelfFeed(true);
      return this.main(chatId);
    }

    if (command === '/stopself' || command === '/stopselffeed') {
      this.pending.delete(chatId);
      this.manager.setSelfFeed(false);
      return this.main(chatId);
    }

    if (command === '/trends' || command === '/trend') {
      this.pending.delete(chatId);
      if (['0', '2', '4', '6', '8'].includes(arg)) {
        this.manager.setTrendDirection(arg);
        return this.main(chatId);
      }
      this.pending.set(chatId, 'trend');
      return this.trendMenu(chatId);
    }

    if (command === '/msg') {
      this.pending.delete(chatId);
      this.pending.set(chatId, 'msgInterval');
      return this.send(chatId, 'اكتب الفاصل بين كل رسالة بالثواني.');
    }

    if (command === '/msgoff' || command === '/stopmsg') {
      this.pending.delete(chatId);
      this.manager.stopMessage();
      return this.main(chatId);
    }

    if (command === '/bots' || command === '/botcount') {
      this.pending.delete(chatId);
      if (/^\d+$/.test(arg)) {
        await this.manager.setBotCount(Number(arg));
        return this.main(chatId);
      }
      this.pending.set(chatId, 'botCount');
      return this.send(chatId, 'اكتب عدد البوتات، مثلاً 5 أو 10.');
    }

    if (command === '/ffa') {
      this.pending.delete(chatId);
      if (arg) {
        const seconds = Number(arg.replace(',', '.'));
        if (!Number.isFinite(seconds) || seconds < 0) return this.send(chatId, 'اكتب ثواني صحيحة مثل 1 أو 0.5.');
        await this.manager.setFfaLoop(true, seconds);
        return this.main(chatId);
      }
      this.pending.set(chatId, 'ffaInterval');
      return this.send(chatId, 'FFA: اكتب مدة بقاء كل جلسة بالثواني قبل إعادة الاتصال. مثال: 1 = ثانية.');
    }

    if (command === '/ffaoff') {
      this.pending.delete(chatId);
      await this.manager.setFfaLoop(false);
      return this.main(chatId);
    }

    if (command === '/auto_rsp' || command === '/autorsp') {
      this.pending.delete(chatId);
      this.manager.setAutoRespawn(!this.manager.autoRespawnEnabled);
      return this.main(chatId);
    }

    if (command === '/split') {
      this.pending.delete(chatId);
      this.manager.splitAll();
      return this.send(chatId, `SPLIT: ${this.manager.splitSpamEnabled ? 'ON' : 'OFF'} / 50ms (${this.manager.bots.length} bots).`);
    }

    const pending = this.pending.get(chatId);
    if (!pending) return;

    try {
      if (pending === 'ffaInterval') {
        const seconds = Number(text.replace(',', '.'));
        if (!Number.isFinite(seconds) || seconds < 0) throw new Error('اكتب رقم ثواني صحيح مثل 1 أو 0.5.');
        await this.manager.setFfaLoop(true, seconds);
        this.pending.delete(chatId);
        return this.main(chatId);
      }
      if (pending === 'ip') {
        this.manager.setEndpoint(parseEndpoint(text));
        this.pending.delete(chatId);
        return this.main(chatId);
      }
      if (pending === 'name') {
        this.manager.setName(text);
        this.pending.delete(chatId);
        return this.main(chatId);
      }
      if (pending === 'track') {
        this.manager.setTrackName(text);
        this.pending.delete(chatId);
        return this.send(chatId, this.manager.summary(), TRACK_KB);
      }
      if (pending === 'trend') {
        if (!['0', '2', '4', '6', '8'].includes(text)) throw new Error('اختار فقط 0 أو 2 أو 4 أو 6 أو 8.');
        this.manager.setTrendDirection(text);
        this.pending.delete(chatId);
        return this.main(chatId);
      }
      if (pending === 'msgInterval') {
        const seconds = Number(text.replace(',', '.'));
        if (!Number.isFinite(seconds) || seconds <= 0) throw new Error('اكتب رقم ثواني أكبر من 0.');
        this.pending.set(chatId, { type: 'msgText', intervalMs: Math.max(100, seconds * 1000) });
        return this.send(chatId, 'الآن ارسل الرسالة.');
      }
      if (pending && pending.type === 'msgText') {
        if (!text) throw new Error('الرسالة فارغة.');
        this.manager.setMessage(true, pending.intervalMs, text);
        this.pending.delete(chatId);
        return this.main(chatId);
      }
      if (pending === 'botCount') {
        if (!/^\d+$/.test(text)) throw new Error('اكتب رقمًا صحيحًا لعدد البوتات.');
        await this.manager.setBotCount(Number(text));
        this.pending.delete(chatId);
        return this.main(chatId);
      }
    } catch (e) {
      await this.send(chatId, e.message);
    }
  }

  async handleCallback(q) {
    const chatId = q.message?.chat?.id;
    if (chatId == null) return;
    try { await this.api('answerCallbackQuery', { callback_query_id: q.id }); } catch (_) {}
    const data = String(q.data || '');

    try {
      if (data === 'menu') return this.main(chatId);
      if (data === 'status') return this.main(chatId);
      if (data === 'ffa:toggle') {
        if (this.manager.ffaLoopEnabled) {
          await this.manager.setFfaLoop(false);
          return this.main(chatId);
        }
        this.pending.set(chatId, 'ffaInterval');
        return this.send(chatId, 'FFA: اكتب مدة بقاء كل جلسة بالثواني قبل إعادة الاتصال. مثال: 1 = ثانية.');
      }
      if (data === 'on') { await this.manager.startAll(); return this.main(chatId); }
      if (data === 'off') { this.manager.stopAll(); return this.main(chatId); }
      if (data === 'autorespawn') { this.manager.setAutoRespawn(!this.manager.autoRespawnEnabled); return this.main(chatId); }
      if (data === 'split') { this.manager.splitAll(); return this.send(chatId, `SPLIT: ${this.manager.splitSpamEnabled ? 'ON' : 'OFF'} / 50ms (${this.manager.bots.length} bots).`); }
      if (data === 'feed:start') { this.manager.setFeed(true); return this.main(chatId); }
      if (data === 'feed:stop') { this.manager.setFeed(false); return this.main(chatId); }
      if (data === 'self_feed') { this.pending.delete(chatId); this.manager.setSelfFeed(true); return this.main(chatId); }
      if (data === 'self_feed:stop') { this.manager.stopSelfFeed(); return this.main(chatId); }
      if (data === 'trends') { this.pending.delete(chatId); return this.trendMenu(chatId); }
      if (data.startsWith('trend:')) {
        const direction = data.slice(6);
        this.manager.setTrendDirection(direction);
        this.pending.delete(chatId);
        return this.main(chatId);
      }
      if (data === 'msg') { this.pending.set(chatId, 'msgInterval'); return this.send(chatId, 'اكتب الفاصل بين كل رسالة بالثواني.'); }
      if (data === 'msg:stop') { this.pending.delete(chatId); this.manager.stopMessage(); return this.main(chatId); }
      if (data === 'botcount') { this.pending.set(chatId, 'botCount'); return this.send(chatId, 'اكتب عدد البوتات، مثلاً 5 أو 10.'); }
      if (data === 'change_ip') { this.pending.set(chatId, 'ip'); return this.send(chatId, 'Send IP:PORT'); }
      if (data === 'change_name') { this.pending.set(chatId, 'name'); return this.send(chatId, 'Send name'); }
      if (data === 'track:me') { this.pending.delete(chatId); this.manager.setPhoneTrack(true); return this.send(chatId, this.manager.summary(), TRACK_KB); }
      if (data === 'track') { this.pending.set(chatId, 'track'); return this.send(chatId, 'Send target name', TRACK_KB); }
      if (data === 'track:stop') { this.manager.stopTrack(); return this.main(chatId); }
    } catch (e) {
      await this.send(chatId, e.message);
    }
  }

  async poll() {
    if (!this.running) return;
    try {
      const updates = await this.api('getUpdates', {
        offset: this.offset,
        timeout: 25,
        allowed_updates: ['message', 'callback_query'],
      }, 35000);
      for (const u of updates) {
        this.offset = u.update_id + 1;
        if (u.message) await this.handleMessage(u.message);
        if (u.callback_query) await this.handleCallback(u.callback_query);
      }
    } catch (e) {
      await new Promise(r => setTimeout(r, 2000));
    }
    setImmediate(() => this.poll());
  }

  start() { if (!this.running) { this.running = true; this.poll(); console.log('Telegram ready'); } }
  stop() { this.running = false; }
}

async function main() {
  const tokens = readTokens();
  const telegramToken = readTelegramToken();
  const proxies = readProxies();
  console.log(`Node ready. Shared token loaded from token.txt. Proxy groups loaded: ${proxies.length}`);
  const manager = new BotManager(tokens, proxies);
  const telegram = new TelegramController(telegramToken, manager);
  telegram.start();

  const shutdown = () => {
    telegram.stop();
    manager.stopAll();
    setTimeout(() => process.exit(0), 300);
  };
  process.on('SIGINT', shutdown);
  process.on('SIGTERM', shutdown);
}

main().catch(e => { console.error(`Fatal: ${e.message}`); process.exit(1); });
