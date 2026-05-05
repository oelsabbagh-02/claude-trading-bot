/**
 * Claude Trading Bot — OKX
 * Strategy: EMA 20/50 Trend Following + Fear & Greed Sentiment Filter
 *
 * Run:     node bot.js
 * Summary: node bot.js --summary
 */

import "dotenv/config";
import { appendFileSync, existsSync, readFileSync, unlinkSync, writeFileSync } from "fs";
import crypto from "crypto";
import http from "http";

// ─── Config ───────────────────────────────────────────────────────────────────

const CONFIG = {
  // Tier 1 — core large-caps, full risk per trade
  symbols: (process.env.SYMBOLS || "BTC-USDC,ETH-USDC,SOL-USDC,XRP-USDC")
    .split(",").map(s => s.trim()).filter(Boolean),

  // Tier 2 — portfolio holdings + on-the-radar picks, 75% size
  radarSymbols: (process.env.RADAR_SYMBOLS || "ADA-USDC,LINK-USDC,ONDO-USDC,FET-USDC,SUI-USDC,NEAR-USDC")
    .split(",").map(s => s.trim()).filter(Boolean),

  // Tier 3 — meme coins, 50% size
  memeSymbols: (process.env.MEME_SYMBOLS || "PEPE-USDC,SHIB-USDC,DOGE-USDC,BONK-USDC,WIF-USDC,FLOKI-USDC,MOODENG-USDC,NEIRO-USDC,TURBO-USDC,DOGS-USDC")
    .split(",").map(s => s.trim()).filter(Boolean),

  timeframe: process.env.TIMEFRAME || "1H",
  portfolioValue: parseFloat(process.env.PORTFOLIO_VALUE_USD || "1000"),
  maxTradeSizeUSD: parseFloat(process.env.MAX_TRADE_SIZE_USD || "50"),
  riskPerTrade: parseFloat(process.env.RISK_PER_TRADE || "0.02"),  // fraction of portfolio per trade
  maxTradesPerDay: parseInt(process.env.MAX_TRADES_PER_DAY || "6", 10),
  paperTrading: process.env.PAPER_TRADING !== "false",
  okx: {
    apiKey: process.env.OKX_API_KEY || "",
    secretKey: process.env.OKX_SECRET_KEY || "",
    passphrase: process.env.OKX_PASSPHRASE || "",
    baseUrl: "https://www.okx.com",
  },
};

// Stop 2× ATR, target 4× ATR → 1:2 risk-reward
const STOP_ATR_MULT   = 2.0;
const TARGET_ATR_MULT = 4.0;

const DATA_DIR             = process.env.DATA_DIR || ".";
const CSV_FILE             = `${DATA_DIR}/trades.csv`;
const POSITIONS_FILE       = `${DATA_DIR}/paper-positions.json`;
const LIVE_POSITIONS_FILE  = `${DATA_DIR}/live-positions.json`;
const LOCK_FILE            = `${DATA_DIR}/bot.lock`;
const SENTIMENT_FILE       = `${DATA_DIR}/sentiment.json`;
const TRENDING_FILE        = `${DATA_DIR}/trending-watchlist.json`;

const MAX_TRENDING_POSITIONS = parseInt(process.env.MAX_TRENDING_POSITIONS || "2", 10);

// Extract base currency from OKX symbol e.g. "BTC-USDT" → "BTC"
function baseCcy(symbol) { return symbol.split("-")[0]; }

// ─── Process lock ─────────────────────────────────────────────────────────────

function acquireLock() {
  if (existsSync(LOCK_FILE)) {
    const pid = parseInt(readFileSync(LOCK_FILE, "utf8").trim(), 10);
    try {
      process.kill(pid, 0);
      console.error(`Bot already running (PID ${pid}). Exiting.`);
      process.exit(1);
    } catch {
      unlinkSync(LOCK_FILE);
    }
  }
  writeFileSync(LOCK_FILE, String(process.pid));
  const release = () => { try { unlinkSync(LOCK_FILE); } catch {} };
  process.on("exit", release);
  process.on("SIGINT",  () => { release(); process.exit(0); });
  process.on("SIGTERM", () => { release(); process.exit(0); });
}

// ─── Helpers ──────────────────────────────────────────────────────────────────

function loadJson(path, fallback) {
  if (!existsSync(path)) return fallback;
  try { return JSON.parse(readFileSync(path, "utf8")); } catch { return fallback; }
}

function saveJson(path, value) {
  writeFileSync(path, JSON.stringify(value, null, 2));
}

// ─── OKX market data ──────────────────────────────────────────────────────────

const BAR_MAP = { "1m":"1m","5m":"5m","15m":"15m","30m":"30m","1H":"1H","4H":"4H","1D":"1D" };

async function fetchCandles(symbol, interval, limit = 200) {
  const bar = BAR_MAP[interval] || "1H";
  const url = `${CONFIG.okx.baseUrl}/api/v5/market/candles?instId=${symbol}&bar=${bar}&limit=${limit}`;
  const res = await fetch(url);
  if (!res.ok) throw new Error(`OKX market API ${res.status}`);
  const data = await res.json();
  if (data.code !== "0") throw new Error(`OKX: ${data.msg}`);
  return data.data.slice().reverse().map(r => ({
    time:   parseInt(r[0], 10),
    open:   parseFloat(r[1]),
    high:   parseFloat(r[2]),
    low:    parseFloat(r[3]),
    close:  parseFloat(r[4]),
    volume: parseFloat(r[5]),
  }));
}

// ─── Indicators ───────────────────────────────────────────────────────────────

function calcEMA(closes, period) {
  if (closes.length < period) return null;
  const k = 2 / (period + 1);
  let ema = closes.slice(0, period).reduce((s, v) => s + v, 0) / period;
  for (let i = period; i < closes.length; i++) ema = closes[i] * k + ema * (1 - k);
  return ema;
}

function calcRSI(closes, period) {
  if (closes.length < period + 1) return null;
  let gains = 0, losses = 0;
  for (let i = closes.length - period; i < closes.length; i++) {
    const d = closes[i] - closes[i - 1];
    if (d > 0) gains += d; else losses -= d;
  }
  return 100 - 100 / (1 + (gains / period) / ((losses / period) || 0.001));
}

function calcATR(candles, period = 14) {
  if (candles.length < period + 1) return null;
  const recent = candles.slice(-(period + 1));
  const trs = recent.map((c, i) => {
    if (i === 0) return c.high - c.low;
    const p = recent[i - 1];
    return Math.max(c.high - c.low, Math.abs(c.high - p.close), Math.abs(c.low - p.close));
  });
  return trs.slice(1).reduce((s, v) => s + v, 0) / period;
}

// ─── Sentiment ────────────────────────────────────────────────────────────────

// Free API — no key needed. Returns 0 (extreme fear) to 100 (extreme greed).
async function fetchFearGreed() {
  try {
    const res = await fetch("https://api.alternative.me/fng/?limit=1");
    if (!res.ok) return null;
    const data = await res.json();
    const entry = data?.data?.[0];
    return entry ? { value: parseInt(entry.value, 10), label: entry.value_classification } : null;
  } catch {
    return null;
  }
}

// ─── Trending watchlist (CoinGecko, refreshed daily) ─────────────────────────

async function fetchTrending() {
  try {
    const res = await fetch("https://api.coingecko.com/api/v3/search/trending");
    if (!res.ok) return null;
    const data = await res.json();
    const coins = (data?.coins ?? []).map(c => c.item);
    return coins;
  } catch {
    return null;
  }
}

async function validateOkxPair(symbol) {
  try {
    const url = `${CONFIG.okx.baseUrl}/api/v5/market/ticker?instId=${symbol}`;
    const res = await fetch(url);
    if (!res.ok) return false;
    const data = await res.json();
    return data.code === "0" && data.data?.length > 0;
  } catch {
    return false;
  }
}

// Refreshes once per day. Returns array of { symbol, name, rank, geckoRank }
async function loadTrendingWatchlist(existingSymbols) {
  const cached = loadJson(TRENDING_FILE, null);
  const ageMs  = cached?.updatedAt ? Date.now() - new Date(cached.updatedAt).getTime() : Infinity;

  if (ageMs < 24 * 3_600_000 && cached?.coins?.length) {
    return cached.coins.filter(c => !existingSymbols.has(c.symbol));
  }

  console.log("\nRefreshing trending watchlist from CoinGecko...");
  const coins = await fetchTrending();
  if (!coins) { console.log("  Trending fetch failed — using cached list"); return cached?.coins ?? []; }

  const validated = [];
  for (const coin of coins) {
    const ccy    = coin.symbol.toUpperCase();
    const symbol = `${ccy}-USDC`;
    if (existingSymbols.has(symbol)) continue;
    const valid = await validateOkxPair(symbol);
    if (!valid) { console.log(`  ${symbol} — not on OKX, skipping`); continue; }
    validated.push({ symbol, name: coin.name, rank: coin.market_cap_rank ?? 9999, geckoRank: coin.score + 1 });
    console.log(`  ${symbol} ✓ (trending rank #${coin.score + 1}, market cap rank #${coin.market_cap_rank ?? "?"})`);
  }

  saveJson(TRENDING_FILE, { updatedAt: new Date().toISOString(), coins: validated });
  console.log(`  Saved ${validated.length} tradeable trending coins\n`);
  return validated.filter(c => !existingSymbols.has(c.symbol));
}

// Written by sentiment.js (optional weekly Apify scrape). Ignored if older than 8 days.
function loadWeeklySentiment() {
  const s = loadJson(SENTIMENT_FILE, null);
  if (!s?.updatedAt) return null;
  const ageMs = Date.now() - new Date(s.updatedAt).getTime();
  return ageMs < 8 * 24 * 3_600_000 ? s : null;
}

// ─── Signal ───────────────────────────────────────────────────────────────────

/**
 * Returns { side: "buy"|"sell"|null, reason: string, sizeMultiplier: number }
 *
 * Long  entry: 1H EMA20 > EMA50 AND RSI 38-70 AND F&G < 85 AND ATR filter AND volume filter
 *   4H aligned  → full size (1.0×)
 *   4H opposing → half size (0.5×), still enters
 * Short entry: 1H EMA20 < EMA50 AND RSI 30-62 AND F&G > 15
 *   (paper only — spot accounts cannot short)
 */
function generateSignal(candles, htfCloses, fearGreed, weeklySentiment) {
  const closes   = candles.map(c => c.close);
  const ema20    = calcEMA(closes, 20);
  const ema50    = calcEMA(closes, 50);
  const rsi14    = calcRSI(closes, 14);
  const htfEma20 = calcEMA(htfCloses, 20);
  const htfEma50 = calcEMA(htfCloses, 50);
  const atr      = calcATR(candles, 14);

  if (!ema20 || !ema50 || !rsi14 || !htfEma20 || !htfEma50 || !atr) {
    return { side: null, reason: "Not enough candle history yet", sizeMultiplier: 1 };
  }

  // ATR volatility filter — skip dead/choppy markets
  const price    = closes.at(-1);
  const atrRatio = atr / price;
  if (atrRatio < 0.0025) {
    return { side: null, reason: `Dead market — ATR/price ${(atrRatio * 100).toFixed(3)}% < 0.25%`, sizeMultiplier: 1 };
  }

  // Volume filter — last CLOSED candle (candles.at(-1) is in-progress) vs 20 prior bars
  const closedVol = candles.at(-2)?.volume ?? 0;
  const avgVol    = candles.slice(-22, -2).reduce((s, c) => s + c.volume, 0) / 20;
  if (avgVol > 0 && closedVol < avgVol * 1.0) {
    return { side: null, reason: `Low volume — ${closedVol.toFixed(0)} < avg ${avgVol.toFixed(0)}`, sizeMultiplier: 1 };
  }

  const trend1h  = ema20 > ema50 ? "up" : "down";
  const trend4h  = htfEma20 > htfEma50 ? "up" : "down";
  const aligned  = trend1h === trend4h;
  const fg       = fearGreed?.value ?? 50;
  const wBias    = weeklySentiment?.bias ?? "neutral";

  if (trend1h === "up" && rsi14 >= 38 && rsi14 <= 70 && fg < 85 && wBias !== "bearish") {
    const sizeMultiplier = aligned ? 1.0 : 0.5;
    const tfLabel = aligned ? "1H+4H" : "1H only (4H opposing — half size)";
    return {
      side: "buy",
      reason: `EMA20 ${ema20.toFixed(4)} > EMA50 ${ema50.toFixed(4)} on ${tfLabel} | RSI ${rsi14.toFixed(1)} | F&G ${fg}`,
      sizeMultiplier,
    };
  }

  // Shorts are paper-only — spot exchange cannot open short positions
  if (CONFIG.paperTrading && trend1h === "down" && rsi14 >= 30 && rsi14 <= 62 && fg > 15 && wBias !== "bullish") {
    const sizeMultiplier = aligned ? 1.0 : 0.5;
    const tfLabel = aligned ? "1H+4H" : "1H only (4H opposing — half size)";
    return {
      side: "sell",
      reason: `EMA20 ${ema20.toFixed(4)} < EMA50 ${ema50.toFixed(4)} on ${tfLabel} | RSI ${rsi14.toFixed(1)} | F&G ${fg}`,
      sizeMultiplier,
    };
  }

  if (trend1h === "up" && (rsi14 < 38 || rsi14 > 70)) {
    return { side: null, reason: `Uptrend but RSI ${rsi14.toFixed(1)} outside long window (38–70)`, sizeMultiplier: 1 };
  }
  if (trend1h === "down" && (rsi14 < 30 || rsi14 > 62)) {
    return { side: null, reason: `Downtrend but RSI ${rsi14.toFixed(1)} outside short window (30–62)`, sizeMultiplier: 1 };
  }
  if (fg >= 85) return { side: null, reason: `Extreme greed (F&G ${fg}) — waiting for pullback`, sizeMultiplier: 1 };
  if (fg <= 15) return { side: null, reason: `Extreme fear (F&G ${fg}) — waiting for stabilisation`, sizeMultiplier: 1 };
  return { side: null, reason: `No setup — trend ${trend1h}, RSI ${rsi14.toFixed(1)}, F&G ${fg}`, sizeMultiplier: 1 };
}

// ─── Paper position management ────────────────────────────────────────────────

function openPaperPosition(symbol, side, price, atr, size) {
  const isLong     = side === "buy";
  const stopLoss   = isLong ? price - STOP_ATR_MULT * atr   : price + STOP_ATR_MULT * atr;
  const takeProfit = isLong ? price + TARGET_ATR_MULT * atr : price - TARGET_ATR_MULT * atr;
  const position   = {
    id: `PAPER-${Date.now()}`,
    symbol, side,
    entryPrice: price, stopLoss, takeProfit,
    size, openedAt: new Date().toISOString(),
  };
  const positions = loadJson(POSITIONS_FILE, []);
  positions.push(position);
  saveJson(POSITIONS_FILE, positions);
  return position;
}

function checkExits(symbol, price, closes) {
  const positions = loadJson(POSITIONS_FILE, []);
  const ema20 = calcEMA(closes, 20);
  const ema50 = calcEMA(closes, 50);

  const remaining = positions.filter(pos => {
    if (pos.symbol !== symbol) return true;

    const isLong = pos.side === "buy";
    let exitReason = null;

    if (isLong  && price <= pos.stopLoss)  exitReason = `Stop loss $${pos.stopLoss.toFixed(4)}`;
    if (!isLong && price >= pos.stopLoss)  exitReason = `Stop loss $${pos.stopLoss.toFixed(4)}`;
    if (!exitReason) {
      if (isLong  && price >= pos.takeProfit) exitReason = `Take profit $${pos.takeProfit.toFixed(4)}`;
      if (!isLong && price <= pos.takeProfit) exitReason = `Take profit $${pos.takeProfit.toFixed(4)}`;
    }
    // EMA crossback = early trend reversal exit
    if (!exitReason && ema20 && ema50) {
      if (isLong  && ema20 < ema50) exitReason = "EMA20 crossed below EMA50";
      if (!isLong && ema20 > ema50) exitReason = "EMA20 crossed above EMA50";
    }

    if (exitReason) {
      const pnlUSD = isLong
        ? ((price - pos.entryPrice) / pos.entryPrice) * pos.size
        : ((pos.entryPrice - price) / pos.entryPrice) * pos.size;
      const pnlPct = isLong
        ? ((price - pos.entryPrice) / pos.entryPrice) * 100
        : ((pos.entryPrice - price) / pos.entryPrice) * 100;
      const holdH = ((Date.now() - new Date(pos.openedAt).getTime()) / 3_600_000).toFixed(1);
      const won = pnlUSD >= 0;

      console.log(`  ${won ? "WIN " : "LOSS"} CLOSED ${pos.side.toUpperCase()} ${symbol}`);
      console.log(`       Entry $${pos.entryPrice.toFixed(4)} → $${price.toFixed(4)} | ${exitReason}`);
      console.log(`       P&L: ${won ? "+" : ""}$${pnlUSD.toFixed(2)} (${won ? "+" : ""}${pnlPct.toFixed(2)}%) | Held ${holdH}h`);

      logClosedTrade(pos, price, pnlUSD, pnlPct, holdH, exitReason);
      return false;
    }

    const isLongPos = pos.side === "buy";
    const openPnlPct = isLongPos
      ? ((price - pos.entryPrice) / pos.entryPrice) * 100
      : ((pos.entryPrice - price) / pos.entryPrice) * 100;
    console.log(`  OPEN ${pos.side.toUpperCase()} ${symbol} @ $${pos.entryPrice.toFixed(4)} → ${openPnlPct >= 0 ? "+" : ""}${openPnlPct.toFixed(2)}%`);
    return true;
  });

  saveJson(POSITIONS_FILE, remaining);
}

// ─── OKX live trading ─────────────────────────────────────────────────────────

function signOKX(ts, method, path, body = "") {
  return crypto.createHmac("sha256", CONFIG.okx.secretKey)
    .update(ts + method + path + body).digest("base64");
}

async function okxRequest(method, path, bodyObj = null) {
  const ts   = new Date().toISOString();
  const body = bodyObj ? JSON.stringify(bodyObj) : "";
  const sign = signOKX(ts, method, path, body);
  const res  = await fetch(`${CONFIG.okx.baseUrl}${path}`, {
    method,
    headers: {
      "Content-Type": "application/json",
      "OK-ACCESS-KEY": CONFIG.okx.apiKey,
      "OK-ACCESS-SIGN": sign,
      "OK-ACCESS-TIMESTAMP": ts,
      "OK-ACCESS-PASSPHRASE": CONFIG.okx.passphrase,
    },
    ...(body ? { body } : {}),
  });
  const data = await res.json();
  if (data.code !== "0") throw new Error(`OKX ${method} ${path}: ${data.msg}`);
  return data;
}

async function placeLiveOrder(symbol, side, sizeUSD, price, atr) {
  const isLong     = side === "buy";
  const sz         = (sizeUSD / price).toFixed(8);
  const stopLoss   = isLong ? price - STOP_ATR_MULT * atr   : price + STOP_ATR_MULT * atr;
  const takeProfit = isLong ? price + TARGET_ATR_MULT * atr : price - TARGET_ATR_MULT * atr;

  const order   = await okxRequest("POST", "/api/v5/trade/order", {
    instId: symbol, tdMode: "cash", side, ordType: "market", sz,
  });
  const orderId = order.data[0].ordId;

  let algoId = null;
  try {
    const algo = await okxRequest("POST", "/api/v5/trade/order-algo", {
      instId: symbol, tdMode: "cash",
      side: isLong ? "sell" : "buy",
      ordType: "oco", sz,
      tpTriggerPx: takeProfit.toFixed(4), tpOrdPx: "-1",
      slTriggerPx: stopLoss.toFixed(4),   slOrdPx: "-1",
    });
    algoId = algo.data?.[0]?.algoId ?? null;
  } catch (err) {
    console.log(`  OCO failed (set stop/target manually on OKX): ${err.message}`);
  }

  return { orderId, algoId, stopLoss, takeProfit };
}

// Returns all spot balances as { CCY: { qty, usdValue } }
// usdValue is OKX's own USD equivalent estimate
async function fetchSpotBalances() {
  try {
    const data = await okxRequest("GET", "/api/v5/account/balance");
    const details = data.data?.[0]?.details ?? [];
    const result = {};
    for (const d of details) {
      const qty = parseFloat(d.availBal ?? 0) + parseFloat(d.frozenBal ?? 0);
      const usdValue = parseFloat(d.eqUsd ?? 0);
      if (qty > 0) result[d.ccy] = { qty, usdValue };
    }
    return result;
  } catch { return {}; }
}

// Returns USD value of a specific currency in spot wallet
async function fetchHoldingUSD(symbol) {
  const balances = await fetchSpotBalances();
  return balances[baseCcy(symbol)]?.usdValue ?? 0;
}

// Check if bot-opened live positions have been closed by their OCO orders
async function checkLiveExits() {
  const positions = loadJson(LIVE_POSITIONS_FILE, []);
  if (!positions.length) return;

  let pending;
  try {
    const res = await okxRequest("GET", "/api/v5/trade/orders-algo-pending?ordType=oco&limit=100");
    pending = new Set((res.data ?? []).map(o => o.algoId));
  } catch {
    return; // can't check — leave positions as-is
  }

  const remaining = [];
  for (const pos of positions) {
    const stillOpen = !pos.algoId || pending.has(pos.algoId);
    if (stillOpen) {
      remaining.push(pos);
      continue;
    }

    // OCO was triggered — try to get the fill price from order history
    let exitPrice = null;
    try {
      const hist = await okxRequest(
        "GET",
        `/api/v5/trade/orders-history?instId=${pos.symbol}&ordType=market&state=filled&limit=5`
      );
      const fill = (hist.data ?? []).find(o => o.side !== pos.side && Date.now() - parseInt(o.cTime) < 48 * 3_600_000);
      if (fill) exitPrice = parseFloat(fill.avgPx);
    } catch {}

    const price   = exitPrice ?? pos.entryPrice;
    const isLong  = pos.side === "buy";
    const pnlUSD  = isLong
      ? ((price - pos.entryPrice) / pos.entryPrice) * pos.size
      : ((pos.entryPrice - price) / pos.entryPrice) * pos.size;
    const pnlPct  = isLong
      ? ((price - pos.entryPrice) / pos.entryPrice) * 100
      : ((pos.entryPrice - price) / pos.entryPrice) * 100;
    const holdH   = ((Date.now() - new Date(pos.openedAt).getTime()) / 3_600_000).toFixed(1);

    console.log(`  ${pnlUSD >= 0 ? "WIN " : "LOSS"} LIVE CLOSED ${pos.side.toUpperCase()} ${pos.symbol}`);
    console.log(`       Entry $${pos.entryPrice.toFixed(4)} → Exit $${price.toFixed(4)} | OCO triggered`);
    console.log(`       P&L: ${pnlUSD >= 0 ? "+" : ""}$${pnlUSD.toFixed(2)} (${pnlPct >= 0 ? "+" : ""}${pnlPct.toFixed(2)}%) | Held ${holdH}h`);
    logClosedTrade(pos, price, pnlUSD, pnlPct, holdH, "OCO triggered");
  }

  saveJson(LIVE_POSITIONS_FILE, remaining);
}

// ─── CSV logging ──────────────────────────────────────────────────────────────

const CSV_HEADER = "Date,Time (UTC),Exchange,Symbol,Side,Qty,Entry,Exit,Size USD,Fee est.,P&L USD,P&L %,Hold (h),Order ID,Mode,Note\n";

function initCsv() {
  if (!existsSync(CSV_FILE)) writeFileSync(CSV_FILE, CSV_HEADER);
}

function csvRow(fields) {
  appendFileSync(CSV_FILE, fields.join(",") + "\n");
}

function logOpenTrade({ symbol, side, price, size, orderId, paperTrading }) {
  const now = new Date();
  const fee = (size * 0.001).toFixed(4);
  csvRow([
    now.toISOString().slice(0, 10), now.toISOString().slice(11, 19),
    "OKX", symbol, side.toUpperCase(), (size / price).toFixed(8),
    price.toFixed(4), "", size.toFixed(2), fee,
    "", "", "", orderId, paperTrading ? "PAPER" : "LIVE", "Opened",
  ]);
}

function logBlockedTrade({ symbol, reason, paperTrading }) {
  const now = new Date();
  csvRow([
    now.toISOString().slice(0, 10), now.toISOString().slice(11, 19),
    "OKX", symbol, "-", "", "", "", "", "", "", "", "",
    "BLOCKED", paperTrading ? "PAPER" : "LIVE", `"${reason}"`,
  ]);
}

function logClosedTrade(pos, exitPrice, pnlUSD, pnlPct, holdH, exitReason) {
  const now  = new Date();
  const sign = pnlUSD >= 0 ? "+" : "";
  const fee  = (pos.size * 0.001).toFixed(4);
  csvRow([
    now.toISOString().slice(0, 10), now.toISOString().slice(11, 19),
    "OKX", pos.symbol, pos.side.toUpperCase(), (pos.size / pos.entryPrice).toFixed(8),
    pos.entryPrice.toFixed(4), exitPrice.toFixed(4), pos.size.toFixed(2), fee,
    `${sign}${pnlUSD.toFixed(2)}`, `${sign}${pnlPct.toFixed(2)}%`,
    holdH, pos.id, "PAPER", `"${exitReason}"`,
  ]);
}

// ─── Summary ──────────────────────────────────────────────────────────────────

function computeStats() {
  if (!existsSync(CSV_FILE)) {
    return { closed: [], wins: [], losses: [], blocked: [], totalPnl: 0, winRate: null, avgWin: 0, avgLoss: 0 };
  }
  const rows = readFileSync(CSV_FILE, "utf8").trim().split("\n").slice(1)
    .filter(Boolean).map(l => l.split(","));
  const blocked = rows.filter(r => r[13]?.trim() === "BLOCKED");
  const closed  = rows.filter(r => {
    const note = r[15]?.replace(/"/g, "").trim() ?? "";
    return note !== "Opened" && note !== "" && r[13]?.trim() !== "BLOCKED";
  });
  const wins   = closed.filter(r => parseFloat(r[10] || 0) > 0);
  const losses = closed.filter(r => parseFloat(r[10] || 0) <= 0);
  const totalPnl = closed.reduce((s, r) => s + parseFloat(r[10] || 0), 0);
  const winRate  = closed.length ? (wins.length / closed.length) * 100 : null;
  const avgWin   = wins.length   ? wins.reduce((s, r) => s + parseFloat(r[10] || 0), 0) / wins.length : 0;
  const avgLoss  = losses.length ? losses.reduce((s, r) => s + parseFloat(r[10] || 0), 0) / losses.length : 0;
  return { rows, closed, wins, losses, blocked, totalPnl, winRate, avgWin, avgLoss };
}

async function showSummary() {
  if (!existsSync(CSV_FILE)) { console.log("No trades yet."); return; }

  const { closed, wins, losses, blocked, totalPnl, winRate, avgWin, avgLoss } = computeStats();
  const openPos  = loadJson(POSITIONS_FILE, []);
  const winRateStr = winRate !== null ? winRate.toFixed(1) : "—";

  console.log("\n═══════════════════════════════════════════");
  console.log("  Trading Summary — OKX");
  console.log("═══════════════════════════════════════════");
  console.log(`  Open positions : ${openPos.length}`);
  console.log(`  Closed trades  : ${closed.length}  (${wins.length}W / ${losses.length}L)`);
  console.log(`  Blocked        : ${blocked.length}`);
  console.log(`  Win rate       : ${winRateStr}%`);
  console.log(`  Total P&L      : ${totalPnl >= 0 ? "+" : ""}$${totalPnl.toFixed(2)}`);
  if (wins.length)   console.log(`  Avg win        : +$${avgWin.toFixed(2)}`);
  if (losses.length) console.log(`  Avg loss       : $${avgLoss.toFixed(2)}`);
  if (wins.length && losses.length) {
    console.log(`  Avg R:R        : 1:${Math.abs(avgWin / avgLoss).toFixed(2)}`);
  }
  if (openPos.length) {
    console.log("\n  Open paper positions:");
    openPos.filter(p => p.side && p.symbol).forEach(p => console.log(`    ${p.side.toUpperCase()} ${p.symbol} @ $${p.entryPrice?.toFixed(4)} (opened ${p.openedAt?.slice(0, 10)})`));
  }

  const livePos = loadJson(LIVE_POSITIONS_FILE, []);
  if (livePos.length) {
    console.log("\n  Open live positions (bot-opened):");
    livePos.forEach(p => console.log(`    ${p.side.toUpperCase()} ${p.symbol} @ $${p.entryPrice.toFixed(4)} | SL $${p.stopLoss.toFixed(4)} | TP $${p.takeProfit.toFixed(4)}`));
  }

  // Show full OKX spot wallet (live mode only)
  if (!CONFIG.paperTrading && CONFIG.okx.apiKey) {
    console.log("\n  OKX spot wallet:");
    const balances = await fetchSpotBalances();
    const coins = Object.entries(balances).filter(([, v]) => v.usdValue >= 1);
    if (coins.length) {
      coins.forEach(([ccy, v]) => console.log(`    ${ccy}: ${v.qty.toFixed(6)} (~$${v.usdValue.toFixed(2)})`));
    } else {
      console.log("    (no significant holdings)");
    }
  }

  console.log("═══════════════════════════════════════════\n");
}

// ─── Daily trade counter ──────────────────────────────────────────────────────

function countTodaysTrades() {
  if (!existsSync(CSV_FILE)) return 0;
  const today = new Date().toISOString().slice(0, 10);
  return readFileSync(CSV_FILE, "utf8").split("\n")
    .filter(l => l.startsWith(today) && l.includes(",Opened")).length;
}

// ─── Analyse one symbol ───────────────────────────────────────────────────────

async function analyzeSymbol(symbol, todayCount, fearGreed, weeklySentiment, tierMultiplier = 1.0) {
  console.log(`\n── ${symbol} ${"─".repeat(Math.max(0, 44 - symbol.length))}`);
  if (tierMultiplier < 1) console.log(`  Tier multiplier: ${tierMultiplier}× size`);

  const [candles, htfCandles] = await Promise.all([
    fetchCandles(symbol, CONFIG.timeframe, 200),
    fetchCandles(symbol, "4H", 100),
  ]);

  const closes    = candles.map(c => c.close);
  const htfCloses = htfCandles.map(c => c.close);
  const price     = closes.at(-1);
  const atr       = calcATR(candles, 14);
  const rsi14     = calcRSI(closes, 14);
  const ema20     = calcEMA(closes, 20);
  const ema50     = calcEMA(closes, 50);

  const pd = price >= 100 ? 2 : price >= 1 ? 4 : 6;
  console.log(`  Price $${price.toFixed(pd)} | RSI(14) ${rsi14?.toFixed(1)} | EMA20 ${ema20?.toFixed(pd)} / EMA50 ${ema50?.toFixed(pd)} | ATR $${atr?.toFixed(pd)}`);

  // Check & close any existing paper positions for this symbol
  if (CONFIG.paperTrading) checkExits(symbol, price, closes);

  if (todayCount >= CONFIG.maxTradesPerDay) {
    console.log(`  Daily cap reached (${todayCount}/${CONFIG.maxTradesPerDay}) — skipping entry`);
    return false;
  }

  // One position per symbol max
  const positions = loadJson(POSITIONS_FILE, []);
  if (positions.some(p => p.symbol === symbol)) return false;

  const signal = generateSignal(candles, htfCloses, fearGreed, weeklySentiment);
  console.log(`  Signal: ${signal.side ? signal.side.toUpperCase() : "NONE"} — ${signal.reason}`);

  if (!signal.side) {
    logBlockedTrade({ symbol, reason: signal.reason, paperTrading: CONFIG.paperTrading });
    return false;
  }

  const tradeSize = Math.min(CONFIG.portfolioValue * CONFIG.riskPerTrade, CONFIG.maxTradeSizeUSD) * (signal.sizeMultiplier ?? 1) * tierMultiplier;

  if (CONFIG.paperTrading) {
    const pos = openPaperPosition(symbol, signal.side, price, atr, tradeSize);
    console.log(`  PAPER ${signal.side.toUpperCase()} $${tradeSize.toFixed(2)} @ $${price.toFixed(4)}`);
    console.log(`        SL $${pos.stopLoss.toFixed(4)} | TP $${pos.takeProfit.toFixed(4)}`);
    logOpenTrade({ symbol, side: signal.side, price, size: tradeSize, orderId: pos.id, paperTrading: true });
    return true;
  }

  // ── Live trading (spot — long only) ──────────────────────────────────────
  if (signal.side !== "buy") {
    console.log("  Shorting skipped — spot account only supports long positions");
    return false;
  }

  if (!CONFIG.okx.apiKey) { console.log("  Missing OKX credentials"); return false; }

  // Check if any bot-opened positions were closed by their OCO orders
  await checkLiveExits();

  // Guard 1: bot already tracking an open position for this symbol
  const livePositions = loadJson(LIVE_POSITIONS_FILE, []);
  if (livePositions.some(p => p.symbol === symbol)) {
    console.log(`  Bot already has a live position in ${symbol} — skipping`);
    return false;
  }

  // Guard 2: user already holds a meaningful amount of this coin
  const holdingUSD = await fetchHoldingUSD(symbol);
  console.log(`  Existing ${baseCcy(symbol)} balance: ~$${holdingUSD.toFixed(0)}`);
  if (holdingUSD > tradeSize * 0.5) {
    console.log(`  Already holding $${holdingUSD.toFixed(0)} of ${baseCcy(symbol)} — no new entry needed`);
    return false;
  }

  try {
    const { orderId, algoId, stopLoss, takeProfit } = await placeLiveOrder(symbol, "buy", tradeSize, price, atr);
    console.log(`  LIVE BUY $${tradeSize.toFixed(2)} @ $${price.toFixed(4)} | Order ${orderId}`);
    console.log(`        SL $${stopLoss.toFixed(4)} | TP $${takeProfit.toFixed(4)}`);

    // Track so we can detect OCO fills on future runs
    const newPos = {
      id: orderId, symbol, side: "buy",
      entryPrice: price, stopLoss, takeProfit,
      size: tradeSize, algoId: algoId ?? null,
      openedAt: new Date().toISOString(),
    };
    const all = loadJson(LIVE_POSITIONS_FILE, []);
    all.push(newPos);
    saveJson(LIVE_POSITIONS_FILE, all);

    logOpenTrade({ symbol, side: "buy", price, size: tradeSize, orderId, paperTrading: false });
    return true;
  } catch (err) {
    console.log(`  Order failed: ${err.message}`);
    logBlockedTrade({ symbol, reason: err.message, paperTrading: false });
    return false;
  }
}

// ─── Main ─────────────────────────────────────────────────────────────────────

async function run() {
  initCsv();

  // Build set of all static watchlist symbols for dedup
  const staticSymbols = new Set([
    ...CONFIG.symbols,
    ...CONFIG.radarSymbols,
    ...CONFIG.memeSymbols,
  ]);

  // Load trending watchlist (refreshes from CoinGecko once per day)
  const trendingCoins = await loadTrendingWatchlist(staticSymbols).catch(() => []);

  console.log("═══════════════════════════════════════════");
  console.log("  Claude Trading Bot — OKX");
  console.log(`  ${new Date().toISOString()}`);
  console.log(`  Mode    : ${CONFIG.paperTrading ? "PAPER TRADING" : "LIVE TRADING"}`);
  console.log(`  Tier 1  : ${CONFIG.symbols.join(", ")}`);
  console.log(`  Radar   : ${CONFIG.radarSymbols.join(", ")}`);
  console.log(`  Meme    : ${CONFIG.memeSymbols.join(", ")}`);
  console.log(`  Trending: ${trendingCoins.map(c => c.symbol).join(", ") || "none"}`);
  console.log(`  Strategy: EMA 20/50 Trend + Fear & Greed + ATR + Volume`);
  console.log("═══════════════════════════════════════════");

  const [fearGreed] = await Promise.all([fetchFearGreed()]);
  const weeklySentiment = loadWeeklySentiment();

  if (fearGreed) console.log(`\nFear & Greed Index: ${fearGreed.value}/100 (${fearGreed.label})`);
  if (weeklySentiment) console.log(`Weekly sentiment  : ${weeklySentiment.bias} (score ${weeklySentiment.score})`);

  let todayCount = countTodaysTrades();
  console.log(`Trades today: ${todayCount}/${CONFIG.maxTradesPerDay}`);

  const tiers = [
    { label: "── TIER 1: Core ──────────────────────────", symbols: CONFIG.symbols,                    mult: 1.00 },
    { label: "── TIER 2: On the Radar ──────────────────", symbols: CONFIG.radarSymbols,               mult: 0.75 },
    { label: "── TIER 3: Meme Coins ────────────────────", symbols: CONFIG.memeSymbols,                mult: 0.50 },
    { label: "── TIER 4: Trending (CoinGecko) ──────────", symbols: trendingCoins.map(c => c.symbol), mult: 0.30 },
  ];

  for (const tier of tiers) {
    todayCount = countTodaysTrades();
    if (todayCount >= CONFIG.maxTradesPerDay) {
      console.log(`\nDaily cap hit — done for today.`);
      break;
    }

    // Tier 4: cap at MAX_TRENDING_POSITIONS open at once
    if (tier.label.includes("TIER 4")) {
      const openTrending = loadJson(POSITIONS_FILE, [])
        .filter(p => trendingCoins.some(c => c.symbol === p.symbol)).length;
      if (openTrending >= MAX_TRENDING_POSITIONS) {
        console.log(`\n${tier.label}`);
        console.log(`  Max trending positions (${MAX_TRENDING_POSITIONS}) already open — skipping`);
        continue;
      }
    }

    console.log(`\n${tier.label}`);
    for (const symbol of tier.symbols) {
      todayCount = countTodaysTrades();
      if (todayCount >= CONFIG.maxTradesPerDay) break;

      // Re-check trending cap per symbol
      if (tier.label.includes("TIER 4")) {
        const openTrending = loadJson(POSITIONS_FILE, [])
          .filter(p => trendingCoins.some(c => c.symbol === p.symbol)).length;
        if (openTrending >= MAX_TRENDING_POSITIONS) break;
        console.log(`  [TRENDING] ${trendingCoins.find(c => c.symbol === symbol)?.name} — CoinGecko rank #${trendingCoins.find(c => c.symbol === symbol)?.geckoRank}`);
      }

      await analyzeSymbol(symbol, todayCount, fearGreed, weeklySentiment, tier.mult).catch(err =>
        console.log(`  ${symbol} error: ${err.message}`)
      );
    }
  }

  console.log("\n═══════════════════════════════════════════\n");
}

async function loop() {
  acquireLock();
  while (true) {
    await run().catch(err => console.error("Bot error:", err.message));
    const next = new Date(Date.now() + 60 * 60 * 1000);
    console.log(`Next run: ${next.toISOString()}\n`);
    await new Promise(r => setTimeout(r, 60 * 60 * 1000));
  }
}

// ─── HTTP status server ───────────────────────────────────────────────────────

let lastRunState = null;

async function buildStatus() {
  const positions = loadJson(POSITIONS_FILE, []);
  const livePositions = loadJson(LIVE_POSITIONS_FILE, []);
  const fearGreed = await fetchFearGreed().catch(() => null);
  const todayCount = countTodaysTrades();

  const positionsWithPnl = await Promise.all(positions.map(async p => {
    try {
      const candles = await fetchCandles(p.symbol, CONFIG.timeframe, 2);
      const price = candles.at(-1)?.close ?? p.entryPrice;
      const pnlUSD = p.side === "buy" ? (price - p.entryPrice) / p.entryPrice * p.size
                                      : (p.entryPrice - price) / p.entryPrice * p.size;
      return { ...p, currentPrice: price, pnlUSD: parseFloat(pnlUSD.toFixed(2)), pnlPct: parseFloat((pnlUSD / p.size * 100).toFixed(2)) };
    } catch { return p; }
  }));

  return {
    time: new Date().toISOString(),
    mode: CONFIG.paperTrading ? "PAPER" : "LIVE",
    symbols: CONFIG.symbols,
    fearGreed: fearGreed ? { value: fearGreed.value, label: fearGreed.label } : null,
    tradesToday: todayCount,
    maxTradesPerDay: CONFIG.maxTradesPerDay,
    paperPositions: positionsWithPnl,
    livePositions,
  };
}

function buildSummaryJson() {
  const { closed, wins, losses, blocked, totalPnl, winRate, avgWin, avgLoss } = computeStats();
  const openPaper = loadJson(POSITIONS_FILE, []);
  const openLive  = loadJson(LIVE_POSITIONS_FILE, []);
  return {
    time: new Date().toISOString(),
    mode: CONFIG.paperTrading ? "PAPER" : "LIVE",
    closedTrades: closed.length,
    wins:   wins.length,
    losses: losses.length,
    blocked: blocked.length,
    winRatePct: winRate !== null ? parseFloat(winRate.toFixed(1)) : null,
    totalPnlUSD: parseFloat(totalPnl.toFixed(2)),
    avgWinUSD:  parseFloat(avgWin.toFixed(2)),
    avgLossUSD: parseFloat(avgLoss.toFixed(2)),
    avgRR: wins.length && losses.length ? parseFloat(Math.abs(avgWin / avgLoss).toFixed(2)) : null,
    openPaperPositions: openPaper.length,
    openLivePositions:  openLive.length,
    paperPositions: openPaper,
    livePositions:  openLive,
  };
}

function startStatusServer() {
  const port = parseInt(process.env.PORT || "3000", 10);
  http.createServer(async (req, res) => {
    if (req.url === "/health") {
      res.writeHead(200, { "Content-Type": "text/plain" });
      res.end("ok");
      return;
    }
    if (req.url === "/summary") {
      try {
        res.writeHead(200, { "Content-Type": "application/json" });
        res.end(JSON.stringify(buildSummaryJson(), null, 2));
      } catch (err) {
        res.writeHead(500, { "Content-Type": "application/json" });
        res.end(JSON.stringify({ error: err.message }));
      }
      return;
    }
    try {
      const status = await buildStatus();
      res.writeHead(200, { "Content-Type": "application/json" });
      res.end(JSON.stringify(status, null, 2));
    } catch (err) {
      res.writeHead(500, { "Content-Type": "application/json" });
      res.end(JSON.stringify({ error: err.message }));
    }
  }).listen(port, () => console.log(`Status server: http://localhost:${port}`));
}

if (process.argv.includes("--summary")) {
  showSummary().catch(err => console.error(err.message));
} else {
  startStatusServer();
  loop();
}
