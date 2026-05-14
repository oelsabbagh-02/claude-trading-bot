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

// ─── Fetch with timeout ───────────────────────────────────────────────────────
// FETCH_TIMEOUT_MS env var (default 10 000 ms). Prevents a hung OKX/CoinGecko
// socket from freezing the main loop indefinitely.
const FETCH_TIMEOUT_MS = parseInt(process.env.FETCH_TIMEOUT_MS || "10000", 10);

function timedFetch(url, opts = {}) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), FETCH_TIMEOUT_MS);
  return fetch(url, { ...opts, signal: controller.signal })
    .finally(() => clearTimeout(timer));
}

// ─── Config ───────────────────────────────────────────────────────────────────

const CONFIG = {
  // Tier 1 — core large-caps, full risk per trade
  // Owner authorized trading anything in the portfolio. BTC, ETH, SOL, XRP required.
  symbols: (process.env.SYMBOLS || "BTC-USDC,ETH-USDC,SOL-USDC,XRP-USDC")
    .split(",").map(s => s.trim()).filter(Boolean),

  // Tier 2 — portfolio holdings + on-the-radar picks, 75% size
  // LINK is a portfolio holding (see 06-portfolio-plan.md). All USDC pairs only.
  radarSymbols: (process.env.RADAR_SYMBOLS || "LINK-USDC,ADA-USDC,ONDO-USDC,FET-USDC,SUI-USDC,NEAR-USDC")
    .split(",").map(s => s.trim()).filter(Boolean),

  // Tier 3 — meme coins, 50% size
  memeSymbols: (process.env.MEME_SYMBOLS || "PEPE-USDC,SHIB-USDC,DOGE-USDC,BONK-USDC,WIF-USDC,FLOKI-USDC,MOODENG-USDC,NEIRO-USDC,TURBO-USDC,DOGS-USDC")
    .split(",").map(s => s.trim()).filter(Boolean),

  timeframe: process.env.TIMEFRAME || "1H",
  // PORTFOLIO_VALUE_USD: static fallback if live balance fetch fails.
  // In live mode the bot queries OKX at cycle start and overrides this dynamically.
  // Set this env var as a sensible floor (total equity ~$4617 as of 2026-05-14).
  portfolioValue: parseFloat(process.env.PORTFOLIO_VALUE_USD || "4617"),
  maxTradeSizeUSD: parseFloat(process.env.MAX_TRADE_SIZE_USD || "50"),
  // OKX rejects algo (OCO/conditional) orders below ~$10-20 notional, so any
  // entry below this threshold ships as an orphan position with no stop. Skip
  // entries that fall below it after tier + conviction multipliers are applied.
  minTradeSizeUSD: parseFloat(process.env.MIN_TRADE_SIZE_USD || "20"),
  riskPerTrade: parseFloat(process.env.RISK_PER_TRADE || "0.02"),  // fraction of portfolio per trade
  maxTradesPerDay: parseInt(process.env.MAX_TRADES_PER_DAY || "6", 10),
  paperTrading: process.env.PAPER_TRADING !== "false",
  // "longs" = spot, buys only (safe for €500 launch)
  // "perps" = USDC-margined swaps, longs + shorts with leverage (NOT YET IMPLEMENTED)
  tradeMode: (process.env.TRADE_MODE || "longs").toLowerCase(),
  // Cron cadence in minutes (Railway-mounted process loops itself).
  // Default: 15 (quarter-hour). Override with CYCLE_MINUTES env var.
  // Example: CYCLE_MINUTES=60 for hourly. CYCLE_MINUTES=5 for 5-minute.
  cycleMinutes: parseInt(process.env.CYCLE_MINUTES || "15", 10),
  // Skip Asian-session thin liquidity (00:00–06:00 UTC).
  // Set "false" to disable. Reduces ACE-style top-buying on wide spreads.
  skipAsianSession: process.env.SKIP_ASIAN_SESSION !== "false",
  // Auto-move stops to breakeven after 1.5× ATR favorable move on live positions.
  // Locks in the "free trade" — worst case 0, lets winners run unbounded with TP intact.
  breakevenStopEnabled: process.env.BREAKEVEN_STOP !== "false",
  okx: {
    apiKey: process.env.OKX_API_KEY || "",
    secretKey: process.env.OKX_SECRET_KEY || "",
    passphrase: process.env.OKX_PASSPHRASE || "",
    baseUrl: process.env.OKX_BASE_URL || "https://my.okx.com",
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
const WATCHLISTS_FILE      = `${DATA_DIR}/watchlists.json`;
const PEAK_EQUITY_FILE     = `${DATA_DIR}/peak-equity.json`;
const RISK_STATE_FILE      = `${DATA_DIR}/risk-state.json`;

const MAX_TRENDING_POSITIONS = parseInt(process.env.MAX_TRENDING_POSITIONS || "2", 10);

// ─── Global position cap (Group B) ────────────────────────────────────────────
// Max 5 concurrent open positions; max 40% of portfolio deployed at once.
const MAX_OPEN_POSITIONS   = parseInt(process.env.MAX_OPEN_POSITIONS   || "5",    10);
const MAX_DEPLOYED_FRAC    = parseFloat(process.env.MAX_DEPLOYED_FRAC  || "0.40");

// ─── Circuit breaker state ────────────────────────────────────────────────────
// Persisted to RISK_STATE_FILE so restarts don't reset the peak or daily/weekly
// reference equity — a kill switch that evaporates on redeploy is useless.
const RISK_STATE = (() => {
  const saved = (() => {
    try {
      if (existsSync(RISK_STATE_FILE)) return JSON.parse(readFileSync(RISK_STATE_FILE, "utf8"));
    } catch {}
    return {};
  })();
  return {
    peakEquity:       parseFloat(saved.peakEquity       ?? process.env.PEAK_EQUITY_USD ?? "4617"),
    dailyStartEquity: saved.dailyStartEquity ? parseFloat(saved.dailyStartEquity) : null,
    dailyStartDate:   saved.dailyStartDate   ?? null,
    weeklyStartEquity:saved.weeklyStartEquity ? parseFloat(saved.weeklyStartEquity) : null,
    weeklyStartDate:  saved.weeklyStartDate  ?? null,
    consecutiveLosses:parseInt(saved.consecutiveLosses ?? "0", 10),
    tradingHalted:    saved.tradingHalted    ?? false,
    newEntriesBlocked:saved.newEntriesBlocked ?? false,
    positionSizeMult: parseFloat(saved.positionSizeMult ?? "1.0"),
    pauseUntil:       saved.pauseUntil       ?? null,
  };
})();

function persistRiskState() {
  try { writeFileSync(RISK_STATE_FILE, JSON.stringify(RISK_STATE, null, 2)); } catch {}
}

// Called at the start of every cycle. Returns true if trading should proceed.
async function checkCircuitBreakers(currentEquity) {
  const now     = new Date();
  const todayStr = now.toISOString().slice(0, 10);
  const monStr   = (() => {
    const d = new Date(now);
    d.setUTCDate(d.getUTCDate() - d.getUTCDay() + 1); // Monday
    return d.toISOString().slice(0, 10);
  })();

  // Reset daily reference on new UTC day
  if (RISK_STATE.dailyStartDate !== todayStr) {
    RISK_STATE.dailyStartDate   = todayStr;
    RISK_STATE.dailyStartEquity = currentEquity;
    RISK_STATE.newEntriesBlocked = false; // reset daily block only; peak/weekly persist
  }
  // Reset weekly reference on Monday
  if (RISK_STATE.weeklyStartDate !== monStr) {
    RISK_STATE.weeklyStartDate    = monStr;
    RISK_STATE.weeklyStartEquity  = currentEquity;
    RISK_STATE.positionSizeMult   = 1.0;
  }

  // Update peak
  if (currentEquity > RISK_STATE.peakEquity) {
    RISK_STATE.peakEquity = currentEquity;
  }

  const drawdownFromPeak = (RISK_STATE.peakEquity - currentEquity) / RISK_STATE.peakEquity;

  // Kill-switch: -25% from peak
  if (drawdownFromPeak >= 0.25) {
    RISK_STATE.tradingHalted = true;
    console.error(`KILL-SWITCH: equity $${currentEquity.toFixed(0)} is ${(drawdownFromPeak*100).toFixed(1)}% below peak $${RISK_STATE.peakEquity.toFixed(0)}. All trading halted.`);
    persistRiskState();
    return false;
  }

  // Position-pause: -15% from peak
  if (drawdownFromPeak >= 0.15) {
    RISK_STATE.newEntriesBlocked = true;
    console.warn(`POSITION-PAUSE: equity $${currentEquity.toFixed(0)}, drawdown ${(drawdownFromPeak*100).toFixed(1)}% from peak. No new entries.`);
  }

  // Daily loss limit: -3% from day-open equity
  if (RISK_STATE.dailyStartEquity) {
    const dailyLoss = (RISK_STATE.dailyStartEquity - currentEquity) / RISK_STATE.dailyStartEquity;
    if (dailyLoss >= 0.03) {
      RISK_STATE.newEntriesBlocked = true;
      console.warn(`DAILY LOSS LIMIT: -${(dailyLoss*100).toFixed(1)}% today ($${(RISK_STATE.dailyStartEquity - currentEquity).toFixed(0)} lost). Blocking new entries.`);
    }
  }

  // Weekly drawdown: -5% from Monday open → halve position sizes
  if (RISK_STATE.weeklyStartEquity) {
    const weeklyLoss = (RISK_STATE.weeklyStartEquity - currentEquity) / RISK_STATE.weeklyStartEquity;
    if (weeklyLoss >= 0.05 && RISK_STATE.positionSizeMult === 1.0) {
      RISK_STATE.positionSizeMult = 0.5;
      console.warn(`WEEKLY DRAWDOWN: -${(weeklyLoss*100).toFixed(1)}% this week. Position sizes halved for remainder of week.`);
    }
  }

  // Consecutive loss pause (4 in a row → 24h cooldown)
  if (RISK_STATE.pauseUntil && now < new Date(RISK_STATE.pauseUntil)) {
    RISK_STATE.newEntriesBlocked = true;
    console.warn(`CONSECUTIVE LOSS PAUSE until ${RISK_STATE.pauseUntil}. No new entries.`);
  }

  persistRiskState();
  return !RISK_STATE.tradingHalted;
}

// Increment consecutive loss counter; called after each confirmed loss
function recordTradeLoss() {
  RISK_STATE.consecutiveLosses++;
  if (RISK_STATE.consecutiveLosses >= 4) {
    const until = new Date(Date.now() + 24 * 3_600_000);
    RISK_STATE.pauseUntil = until.toISOString();
    RISK_STATE.consecutiveLosses = 0;
    console.warn(`4 consecutive losses — 24h entry pause until ${RISK_STATE.pauseUntil}`);
  }
  persistRiskState();
}

function recordTradeWin() {
  RISK_STATE.consecutiveLosses = 0;
  persistRiskState();
}

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
  const res = await timedFetch(url);
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
    const res = await timedFetch("https://api.alternative.me/fng/?limit=1");
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
    const res = await timedFetch("https://api.coingecko.com/api/v3/search/trending");
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
    const res = await timedFetch(url);
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

// ─── Auto-refresh static watchlists (weekly from CoinGecko) ──────────────────

const STABLES_AND_WRAPPED = new Set([
  "USDT", "USDC", "DAI", "TUSD", "USDS", "FDUSD", "PYUSD", "USDE", "USD1",
  "WBTC", "WETH", "WBETH", "WSTETH", "STETH", "CBBTC", "CBETH", "RETH",
  "STETHWBETH", "WEETH", "WSOL", "JUPSOL", "JITOSOL",
]);

async function fetchCoinGeckoMarkets({ category = null, perPage = 50, page = 1 } = {}) {
  try {
    const cat = category ? `&category=${category}` : "";
    const url = `https://api.coingecko.com/api/v3/coins/markets?vs_currency=usd&order=market_cap_desc&per_page=${perPage}&page=${page}${cat}`;
    const res = await timedFetch(url);
    if (!res.ok) return null;
    return await res.json();
  } catch { return null; }
}

// Returns first N coins from `coins` that have a tradeable OKX-USDC pair and aren't stablecoins
async function pickTradeableUsdc(coins, n) {
  const picks = [];
  for (const c of coins) {
    if (picks.length >= n) break;
    const ccy = c.symbol.toUpperCase();
    if (STABLES_AND_WRAPPED.has(ccy)) continue;
    const symbol = `${ccy}-USDC`;
    const ok = await validateOkxPair(symbol);
    if (ok) picks.push(symbol);
  }
  return picks;
}

// Refreshes once per week. Returns { core, radar, meme } arrays of OKX-USDC symbols.
async function loadDynamicWatchlists() {
  const cached = loadJson(WATCHLISTS_FILE, null);
  const ageMs  = cached?.updatedAt ? Date.now() - new Date(cached.updatedAt).getTime() : Infinity;
  const TTL    = 7 * 24 * 3_600_000;

  if (ageMs < TTL && cached?.core?.length) return cached;

  console.log("\nRefreshing static watchlists from CoinGecko (weekly)...");
  const [topMarket, memes] = await Promise.all([
    fetchCoinGeckoMarkets({ perPage: 100 }),
    fetchCoinGeckoMarkets({ category: "meme-token", perPage: 50 }),
  ]);

  if (!topMarket || !memes) {
    console.log("  CoinGecko fetch failed — using cached/default lists");
    return cached ?? null;
  }

  // Tier 1: top 4 by market cap (excluding stables/wrapped)
  const core  = await pickTradeableUsdc(topMarket, 4);
  // Tier 2: ranks 5-50 by market cap, top 6 with OKX-USDC pairs
  const radar = await pickTradeableUsdc(topMarket.slice(4, 50), 6);
  // Tier 3: top 10 memes by market cap with OKX-USDC pairs
  const meme  = await pickTradeableUsdc(memes, 10);

  console.log(`  Core (T1) : ${core.join(", ")}`);
  console.log(`  Radar (T2): ${radar.join(", ")}`);
  console.log(`  Meme (T3) : ${meme.join(", ")}`);

  const result = { updatedAt: new Date().toISOString(), core, radar, meme };
  saveJson(WATCHLISTS_FILE, result);
  return result;
}

// Written by sentiment.js (optional weekly Apify scrape). Ignored if older than 8 days.
function loadWeeklySentiment() {
  const s = loadJson(SENTIMENT_FILE, null);
  if (!s?.updatedAt) return null;
  const ageMs = Date.now() - new Date(s.updatedAt).getTime();
  return ageMs < 8 * 24 * 3_600_000 ? s : null;
}

// ─── Chop filter ─────────────────────────────────────────────────────────────
// Returns true if the market is in chop regime on both 1H and 4H.
// Chop = EMA(20)/EMA(50) spread < 1.5% on the given timeframe closes.
// When isChop returns true, new entries are blocked (strategy-pause, not mode-switch).
const CHOP_EMA_SPREAD_MIN_PCT = parseFloat(process.env.CHOP_EMA_SPREAD_PCT || "1.5");

function emaPctSpread(closes) {
  const ema20 = calcEMA(closes, 20);
  const ema50 = calcEMA(closes, 50);
  if (!ema20 || !ema50 || ema50 === 0) return null;
  return Math.abs(ema20 - ema50) / ema50 * 100;
}

function isChopRegime(closes1h, closes4h) {
  const spread1h = emaPctSpread(closes1h);
  const spread4h = emaPctSpread(closes4h);
  if (spread1h === null || spread4h === null) return false; // not enough data — allow entry
  return spread1h < CHOP_EMA_SPREAD_MIN_PCT && spread4h < CHOP_EMA_SPREAD_MIN_PCT;
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
function generateSignal(candles, htfCloses, fearGreed, weeklySentiment, mode = "trend") {
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

  // Chop filter (Group C): block new entries when both 1H and 4H EMA20/50 spread < 1.5%
  // This is regime classifier in its lightest form — pause only, no mode switch.
  if (isChopRegime(closes, htfCloses)) {
    const s1h = emaPctSpread(closes)?.toFixed(2);
    const s4h = emaPctSpread(htfCloses)?.toFixed(2);
    return { side: null, reason: `CHOP filter: EMA spread 1H=${s1h}% 4H=${s4h}% both < ${CHOP_EMA_SPREAD_MIN_PCT}% — no entry`, sizeMultiplier: 1 };
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

  // ── Momentum mode (Tier 4 trending) — breakout entry, no RSI ceiling ────────
  if (mode === "momentum") {
    if (trend1h !== "up") {
      return { side: null, reason: `Momentum: trend not up (EMA20<EMA50)`, sizeMultiplier: 1 };
    }
    if (fg >= 90) {
      return { side: null, reason: `Momentum: extreme greed (F&G ${fg})`, sizeMultiplier: 1 };
    }
    if (wBias === "bearish") {
      return { side: null, reason: `Momentum: weekly sentiment bearish`, sizeMultiplier: 1 };
    }
    // Breakout: last closed candle's close must exceed prior 20-bar high
    const prior20High = Math.max(...candles.slice(-22, -2).map(c => c.high));
    const closedHigh  = candles.at(-2)?.close ?? 0;
    if (closedHigh <= prior20High) {
      return { side: null, reason: `Momentum: no breakout (close ${closedHigh.toFixed(6)} ≤ 20-bar high ${prior20High.toFixed(6)})`, sizeMultiplier: 1 };
    }
    return {
      side: "buy",
      reason: `Momentum BREAKOUT — close ${closedHigh.toFixed(6)} > 20-bar high ${prior20High.toFixed(6)} | RSI ${rsi14.toFixed(1)} | F&G ${fg}`,
      sizeMultiplier: 1.0,
      stopMult: 1.5,    // tighter stop for pump plays
      targetMult: 3.0,  // 1:2 R:R preserved at the tighter stop
    };
  }

  // ── Trend mode (default for Tiers 1-3) ──────────────────────────────────────
  // Conviction scoring: count confluence factors → scale size up/down.
  // Each factor adds independent edge; more factors = higher EV setup.
  function scoreConviction(side) {
    let n = 0;
    if (aligned) n++;                                       // 1H+4H trend match
    if (side === "buy"  && rsi14 >= 45 && rsi14 <= 65) n++; // RSI sweet spot for longs
    if (side === "sell" && rsi14 >= 35 && rsi14 <= 55) n++; // RSI sweet spot for shorts
    if (fg >= 35 && fg <= 65) n++;                          // F&G not at extremes
    if (avgVol > 0 && closedVol > avgVol * 1.5) n++;        // strong volume confirmation
    if (side === "buy"  && wBias === "bullish") n++;
    if (side === "sell" && wBias === "bearish") n++;
    return n;
  }
  function convictionMultiplier(score) {
    if (score <= 0) return 0.5;       // weak (1H only, no bonuses)  — half size
    if (score === 1) return 1.0;      // baseline (one factor)        — normal
    if (score <= 3) return 1.5;       // good (2-3 factors)           — 1.5× boost
    return 2.0;                       // A+ setup (4-5 factors)       — double down
  }

  if (trend1h === "up" && rsi14 >= 38 && rsi14 <= 70 && fg < 85 && wBias !== "bearish") {
    const score = scoreConviction("buy");
    const sizeMultiplier = convictionMultiplier(score);
    const tfLabel = aligned ? "1H+4H" : "1H only";
    return {
      side: "buy",
      reason: `EMA20>${ema50.toFixed(4)} on ${tfLabel} | RSI ${rsi14.toFixed(1)} | F&G ${fg} | conviction ${score}/5 → ${sizeMultiplier}× size`,
      sizeMultiplier,
    };
  }

  // Shorts are paper-only — spot exchange cannot open short positions
  if (CONFIG.paperTrading && trend1h === "down" && rsi14 >= 30 && rsi14 <= 62 && fg > 15 && wBias !== "bullish") {
    const score = scoreConviction("sell");
    const sizeMultiplier = convictionMultiplier(score);
    const tfLabel = aligned ? "1H+4H" : "1H only";
    return {
      side: "sell",
      reason: `EMA20<${ema50.toFixed(4)} on ${tfLabel} | RSI ${rsi14.toFixed(1)} | F&G ${fg} | conviction ${score}/5 → ${sizeMultiplier}× size`,
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

function openPaperPosition(symbol, side, price, atr, size, opts = {}) {
  if (!symbol.endsWith("-USDC")) {
    throw new Error(`Refusing to open non-USDC paper position: ${symbol}`);
  }
  const stopMult   = opts.stopMult   ?? STOP_ATR_MULT;
  const targetMult = opts.targetMult ?? TARGET_ATR_MULT;
  const isLong     = side === "buy";
  const stopLoss   = isLong ? price - stopMult * atr   : price + stopMult * atr;
  const takeProfit = isLong ? price + targetMult * atr : price - targetMult * atr;
  const position   = {
    id: `PAPER-${Date.now()}`,
    symbol, side, mode: "PAPER",
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
    // EMA crossback = early trend reversal exit.
    // Require >0.5% spread to avoid whipsaw exits in chop (Group C item 9).
    if (!exitReason && ema20 && ema50) {
      const crossSpreadPct = Math.abs(ema20 - ema50) / ema50 * 100;
      if (crossSpreadPct > 0.5) {
        if (isLong  && ema20 < ema50) exitReason = "EMA20 crossed below EMA50";
        if (!isLong && ema20 > ema50) exitReason = "EMA20 crossed above EMA50";
      }
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
  const res  = await timedFetch(`${CONFIG.okx.baseUrl}${path}`, {
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
  if (data.code !== "0") {
    const detail = data.data?.[0]?.sMsg ?? data.data?.[0]?.msg ?? "";
    const code   = data.data?.[0]?.sCode ?? data.code;
    throw new Error(`OKX ${method} ${path}: ${data.msg || detail || "no message"} (code=${code})`);
  }
  return data;
}

async function placeLiveOrder(symbol, side, sizeUSD, price, atr, opts = {}) {
  if (!symbol.endsWith("-USDC")) {
    throw new Error(`Refusing to place non-USDC live order: ${symbol}`);
  }
  const stopMult   = opts.stopMult   ?? STOP_ATR_MULT;
  const targetMult = opts.targetMult ?? TARGET_ATR_MULT;
  const isLong     = side === "buy";
  const sz         = (sizeUSD / price).toFixed(8);
  const stopLoss   = isLong ? price - stopMult * atr   : price + stopMult * atr;
  const takeProfit = isLong ? price + targetMult * atr : price - targetMult * atr;

  const order   = await okxRequest("POST", "/api/v5/trade/order", {
    instId: symbol, tdMode: "cash", side, ordType: "market", sz,
    tgtCcy: "base_ccy",
  });
  const orderId = order.data[0].ordId;

  let algoId = null;
  try {
    const algo = await okxRequest("POST", "/api/v5/trade/order-algo", {
      instId: symbol, tdMode: "cash",
      side: isLong ? "sell" : "buy",
      ordType: "oco", sz, tgtCcy: "base_ccy",
      tpTriggerPx: takeProfit.toFixed(4), tpOrdPx: "-1",
      slTriggerPx: stopLoss.toFixed(4),   slOrdPx: "-1",
    });
    algoId = algo.data?.[0]?.algoId ?? null;
  } catch (err) {
    console.log(`  OCO failed: ${err.message}`);
    // Fallback: stop-only conditional algo. Better than nothing.
    try {
      const sl = await okxRequest("POST", "/api/v5/trade/order-algo", {
        instId: symbol, tdMode: "cash",
        side: isLong ? "sell" : "buy",
        ordType: "conditional", sz, tgtCcy: "base_ccy",
        slTriggerPx: stopLoss.toFixed(4), slOrdPx: "-1",
      });
      algoId = sl.data?.[0]?.algoId ?? null;
      if (algoId) console.log(`  Fallback: stop-only conditional placed (no take-profit)`);
    } catch (err2) {
      console.log(`  Fallback stop also failed: ${err2.message}`);
      console.log(`  ⚠ Position has NO automatic exit — will be reconciled via balance check`);
    }
  }

  return { orderId, algoId, stopLoss, takeProfit };
}

// Returns total account equity in USD by summing all asset eqUsd values.
// Used to set CONFIG.portfolioValue dynamically each cycle.
async function fetchAccountEquityUSD() {
  try {
    const data = await okxRequest("GET", "/api/v5/account/balance");
    const details = data.data?.[0]?.details ?? [];
    const total = details.reduce((s, d) => s + parseFloat(d.eqUsd ?? 0), 0);
    return total > 0 ? total : null;
  } catch { return null; }
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

// Active exits: signal-reversal and time-decay liquidation, plus orphan retry.
// Runs each cycle on every open live position. Closes positions at market when:
//   1. 1H EMA20 has crossed below EMA50 (trend flipped against a long) — opposite for shorts
//   2. Position is older than 48h AND not in profit (don't marry the bag)
//   3. Position is an orphan (algoId null) AND down more than 5% (no OCO will save it)
// Also tries to (re-)place OCO on orphan positions before deciding to close.
async function activeExitChecks() {
  if (CONFIG.paperTrading) return;
  const positions = loadJson(LIVE_POSITIONS_FILE, []);
  if (!positions.length) return;

  const remaining = [];
  let changed    = false;

  for (const pos of positions) {
    const isLong = pos.side === "buy";

    // Fetch current candles + price for this symbol
    let candles, price;
    try {
      candles = await fetchCandles(pos.symbol, CONFIG.timeframe, 100);
      price   = candles.at(-1)?.close;
    } catch {
      remaining.push(pos);
      continue;
    }
    if (!price) { remaining.push(pos); continue; }

    const closes = candles.map(c => c.close);
    const ema20  = calcEMA(closes, 20);
    const ema50  = calcEMA(closes, 50);

    // — Orphan retry: if no algo attached, try OCO once before deciding to close
    if (!pos.algoId) {
      const sz = (pos.size / pos.entryPrice).toFixed(8);
      try {
        const algo = await okxRequest("POST", "/api/v5/trade/order-algo", {
          instId: pos.symbol, tdMode: "cash",
          side: isLong ? "sell" : "buy",
          ordType: "oco", sz, tgtCcy: "base_ccy",
          tpTriggerPx: pos.takeProfit.toFixed(4), tpOrdPx: "-1",
          slTriggerPx: pos.stopLoss.toFixed(4),   slOrdPx: "-1",
        });
        const newAlgoId = algo.data?.[0]?.algoId ?? null;
        if (newAlgoId) {
          console.log(`  ✓ ${pos.symbol} orphan retroactively protected with OCO`);
          pos.algoId = newAlgoId;
          changed = true;
        }
      } catch { /* still orphan; carry on to active-exit checks */ }
    }

    // — Active exit conditions
    const ageH      = (Date.now() - new Date(pos.openedAt).getTime()) / 3_600_000;
    const pnlPct    = isLong ? ((price - pos.entryPrice) / pos.entryPrice) : ((pos.entryPrice - price) / pos.entryPrice);
    const trendDown = (ema20 && ema50) ? ema20 < ema50 : false;
    const trendUp   = (ema20 && ema50) ? ema20 > ema50 : false;

    // EMA crossback exit requires >0.5% spread to avoid whipsaw exits in chop (Group C item 9).
    const emaCrossSpreadPct = (ema20 && ema50) ? Math.abs(ema20 - ema50) / ema50 * 100 : 0;
    const committedTrendDown = trendDown && emaCrossSpreadPct > 0.5;
    const committedTrendUp   = trendUp   && emaCrossSpreadPct > 0.5;

    let exitReason = null;
    if (isLong && committedTrendDown) exitReason = `trend reversed (EMA20 < EMA50, spread ${emaCrossSpreadPct.toFixed(2)}%)`;
    else if (!isLong && committedTrendUp) exitReason = `trend reversed (EMA20 > EMA50, spread ${emaCrossSpreadPct.toFixed(2)}%)`;
    else if (ageH > 48 && pnlPct <= 0) exitReason = `time-decay (${ageH.toFixed(1)}h, ${(pnlPct*100).toFixed(1)}%)`;
    else if (!pos.algoId && pnlPct <= -0.05) exitReason = `orphan stop-loss (no OCO, ${(pnlPct*100).toFixed(1)}%)`;

    if (!exitReason) {
      remaining.push(pos);
      continue;
    }

    // Cancel any algo first to free the size, then market-sell
    if (pos.algoId) {
      try {
        await okxRequest("POST", "/api/v5/trade/cancel-algos", [{ algoId: pos.algoId, instId: pos.symbol }]);
      } catch { /* if cancel fails the algo will simply expire when balance is gone */ }
    }

    // Place market close (sell for long, buy for short — but we're spot-longs-only currently)
    try {
      const sz = (pos.size / pos.entryPrice).toFixed(8);
      await okxRequest("POST", "/api/v5/trade/order", {
        instId: pos.symbol, tdMode: "cash",
        side: isLong ? "sell" : "buy", ordType: "market", sz,
        tgtCcy: "base_ccy",
      });
      const holdH = ageH.toFixed(1);
      const pnlUSD = pnlPct * pos.size;
      console.log(`  ⚡ ACTIVE EXIT ${pos.symbol} @ $${price.toFixed(6)} | ${exitReason}`);
      console.log(`       P&L: ${pnlUSD >= 0 ? "+" : ""}$${pnlUSD.toFixed(2)} (${(pnlPct*100).toFixed(2)}%) | Held ${holdH}h`);
      logClosedTrade(pos, price, pnlUSD, pnlPct * 100, holdH, `Active exit: ${exitReason}`);
      changed = true;
      // Don't push to remaining — position closed
    } catch (err) {
      console.log(`  Active exit failed for ${pos.symbol}: ${err.message} — keeping in tracker`);
      remaining.push(pos);
    }
  }

  if (changed) saveJson(LIVE_POSITIONS_FILE, remaining);
}

// After 1.5× ATR favorable move, swap the OCO so stop = entry price.
// Worst case becomes "free trade" (0% loss); upside via TP is unchanged.
// Captures the asymmetric "winners run, losers cap at 0" pattern.
async function tryBreakevenStops() {
  if (!CONFIG.breakevenStopEnabled || CONFIG.paperTrading) return;
  const positions = loadJson(LIVE_POSITIONS_FILE, []);
  if (!positions.length) return;

  const updated = [];
  let changed   = false;

  for (const pos of positions) {
    if (pos.breakevenSet || !pos.algoId) {
      updated.push(pos);
      continue;
    }
    const isLong = pos.side === "buy";
    // Recover ATR-at-entry from the original stop distance (was 2× ATR or 1.5× for momentum)
    const stopDist = Math.abs(pos.entryPrice - pos.stopLoss);
    const atrAtEntry = stopDist / 2; // best-effort; tier-4 momentum uses 1.5× but 2× is conservative

    let price;
    try {
      const t = await okxRequest("GET", `/api/v5/market/ticker?instId=${pos.symbol}`);
      price = parseFloat(t.data?.[0]?.last);
    } catch {
      updated.push(pos);
      continue;
    }
    const move = isLong ? price - pos.entryPrice : pos.entryPrice - price;
    if (move < atrAtEntry * 1.5) {
      updated.push(pos);
      continue;
    }

    // Place NEW OCO first, then cancel old one — eliminates the naked-position race window.
    const sz = (pos.size / pos.entryPrice).toFixed(8);
    let newAlgoId = null;
    try {
      const algo = await okxRequest("POST", "/api/v5/trade/order-algo", {
        instId: pos.symbol, tdMode: "cash",
        side: isLong ? "sell" : "buy",
        ordType: "oco", sz, tgtCcy: "base_ccy",
        tpTriggerPx: pos.takeProfit.toFixed(4), tpOrdPx: "-1",
        slTriggerPx: pos.entryPrice.toFixed(4),  slOrdPx: "-1",
      });
      newAlgoId = algo.data?.[0]?.algoId ?? null;
    } catch (err) {
      console.log(`  Breakeven OCO failed for ${pos.symbol}: ${err.message} — retrying with stop-only`);
      try {
        const sl = await okxRequest("POST", "/api/v5/trade/order-algo", {
          instId: pos.symbol, tdMode: "cash",
          side: isLong ? "sell" : "buy",
          ordType: "conditional", sz, tgtCcy: "base_ccy",
          slTriggerPx: pos.entryPrice.toFixed(4), slOrdPx: "-1",
        });
        newAlgoId = sl.data?.[0]?.algoId ?? null;
      } catch (err2) {
        console.log(`  Breakeven fallback also failed: ${err2.message}`);
      }
    }

    if (!newAlgoId) {
      // New order failed — do NOT cancel old OCO. Position stays protected at original stop.
      console.log(`  Breakeven skipped for ${pos.symbol} — new OCO failed; keeping original protection.`);
      updated.push(pos);
      changed = false; // undo changed flag for this pos since we kept it
      // still mark changed true below to persist state for other positions
    } else {
      // New OCO confirmed. Now safe to cancel the old one.
      try {
        await okxRequest("POST", "/api/v5/trade/cancel-algos", [{ algoId: pos.algoId, instId: pos.symbol }]);
      } catch (err) {
        console.log(`  Old OCO cancel failed for ${pos.symbol}: ${err.message} — two OCOs briefly active; OKX will reject the first to fill`);
      }
      console.log(`  ${pos.symbol} stop moved to breakeven @ $${pos.entryPrice.toFixed(4)} (price $${price.toFixed(6)}, +${move.toFixed(6)})`);
      updated.push({ ...pos, algoId: newAlgoId, stopLoss: pos.entryPrice, breakevenSet: true });
    }
    changed = true;
  }

  if (changed) saveJson(LIVE_POSITIONS_FILE, updated);
}

// Check if bot-opened live positions have been closed by their OCO orders
// or by external/manual action (reconciles tracked positions vs actual balance)
async function checkLiveExits() {
  const positions = loadJson(LIVE_POSITIONS_FILE, []);
  if (!positions.length) return;

  let pending;
  let spotBalances = {};
  try {
    const [res, balances] = await Promise.all([
      okxRequest("GET", "/api/v5/trade/orders-algo-pending?ordType=oco,conditional&limit=100"),
      fetchSpotBalances(),
    ]);
    pending = new Set((res.data ?? []).map(o => o.algoId));
    spotBalances = balances;
  } catch {
    return; // can't check — leave positions as-is
  }

  const remaining = [];
  for (const pos of positions) {
    // Reconciliation: if actual balance is < 10% of expected, position was closed
    // externally (OCO fired, manual sell, etc.). Mark closed regardless of algoId state.
    const expectedQty = pos.size / pos.entryPrice;
    const heldQty     = spotBalances[baseCcy(pos.symbol)]?.qty ?? 0;
    const isClosed    = heldQty < expectedQty * 0.1;
    const algoStillOpen = pos.algoId && pending.has(pos.algoId);

    // Still open: bot has algo pending AND balance still holds the asset
    if (!isClosed && algoStillOpen) {
      remaining.push(pos);
      continue;
    }
    // Edge case: no algoId attached but balance still there → orphaned; flag and keep
    if (!isClosed && !pos.algoId) {
      console.log(`  ⚠ ${pos.symbol} held without algo protection — manual action needed`);
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
  // Use mode stored on position record (set at open time), fallback to current config
  const mode = pos.mode ?? (CONFIG.paperTrading ? "PAPER" : "LIVE");
  csvRow([
    now.toISOString().slice(0, 10), now.toISOString().slice(11, 19),
    "OKX", pos.symbol, pos.side.toUpperCase(), (pos.size / pos.entryPrice).toFixed(8),
    pos.entryPrice.toFixed(4), exitPrice.toFixed(4), pos.size.toFixed(2), fee,
    `${sign}${pnlUSD.toFixed(2)}`, `${sign}${pnlPct.toFixed(2)}%`,
    holdH, pos.id, mode, `"${exitReason}"`,
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

async function analyzeSymbol(symbol, todayCount, fearGreed, weeklySentiment, tierMultiplier = 1.0, mode = "trend") {
  // Hard guard — bot will never trade non-USDC pairs
  if (!symbol.endsWith("-USDC")) {
    console.log(`\n  Skipping ${symbol} — only USDC pairs allowed`);
    return false;
  }
  console.log(`\n── ${symbol} ${"─".repeat(Math.max(0, 44 - symbol.length))}`);
  if (tierMultiplier < 1) console.log(`  Tier multiplier: ${tierMultiplier}× size`);
  if (mode !== "trend")   console.log(`  Mode: ${mode.toUpperCase()}`);

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

  // Check & close any existing paper positions for this symbol (paper only)
  if (CONFIG.paperTrading) checkExits(symbol, price, closes);

  if (todayCount >= CONFIG.maxTradesPerDay) {
    console.log(`  Daily cap reached (${todayCount}/${CONFIG.maxTradesPerDay}) — skipping entry`);
    return false;
  }

  // One position per symbol max (paper)
  const positions = loadJson(POSITIONS_FILE, []);
  if (positions.some(p => p.symbol === symbol)) return false;

  // Global position cap (live): max 5 concurrent, max 40% deployed (Group B)
  if (!CONFIG.paperTrading) {
    const livePosAll = loadJson(LIVE_POSITIONS_FILE, []);
    if (livePosAll.length >= MAX_OPEN_POSITIONS) {
      console.log(`  Global position cap (${MAX_OPEN_POSITIONS}) reached — skipping`);
      return false;
    }
    const deployed = livePosAll.reduce((s, p) => s + (p.size ?? 0), 0);
    if (deployed > CONFIG.portfolioValue * MAX_DEPLOYED_FRAC) {
      console.log(`  Deployed capital cap (${(MAX_DEPLOYED_FRAC*100).toFixed(0)}%) reached ($${deployed.toFixed(0)}/$${(CONFIG.portfolioValue * MAX_DEPLOYED_FRAC).toFixed(0)}) — skipping`);
      return false;
    }
    // Circuit breaker gate: block new entries if flag is set
    if (RISK_STATE.newEntriesBlocked) {
      console.log(`  New entries blocked by circuit breaker — skipping`);
      return false;
    }
  }

  const signal = generateSignal(candles, htfCloses, fearGreed, weeklySentiment, mode);
  console.log(`  Signal: ${signal.side ? signal.side.toUpperCase() : "NONE"} — ${signal.reason}`);

  if (!signal.side) {
    logBlockedTrade({ symbol, reason: signal.reason, paperTrading: CONFIG.paperTrading });
    return false;
  }

  // Mode gate: in longs mode, drop short signals before they reach paper or live.
  // Keeps paper stats representative of what live (spot) will actually take.
  if (CONFIG.tradeMode === "longs" && signal.side === "sell") {
    console.log("  Short signal skipped — TRADE_MODE=longs");
    logBlockedTrade({ symbol, reason: "short skipped (longs-only mode)", paperTrading: CONFIG.paperTrading });
    return false;
  }

  const riskMult  = CONFIG.paperTrading ? 1.0 : (RISK_STATE.positionSizeMult ?? 1.0);
  const hardCap   = parseFloat(process.env.HARD_TRADE_CAP_USD || "1e9");
  const tradeSize = Math.min(
    Math.min(CONFIG.portfolioValue * CONFIG.riskPerTrade, CONFIG.maxTradeSizeUSD) * (signal.sizeMultiplier ?? 1) * tierMultiplier * riskMult,
    hardCap
  );

  // Min-size guard: live entries below the algo-order minimum become orphans.
  // Paper trades are unaffected (no algo orders involved).
  if (!CONFIG.paperTrading && tradeSize < CONFIG.minTradeSizeUSD) {
    console.log(`  Skip: $${tradeSize.toFixed(2)} below MIN_TRADE_SIZE_USD ($${CONFIG.minTradeSizeUSD}) — would orphan without stop`);
    logBlockedTrade({ symbol, reason: `size $${tradeSize.toFixed(2)} below algo minimum`, paperTrading: false });
    return false;
  }

  const stopOpts = { stopMult: signal.stopMult, targetMult: signal.targetMult };

  if (CONFIG.paperTrading) {
    const pos = openPaperPosition(symbol, signal.side, price, atr, tradeSize, stopOpts);
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

  // Guard 1: bot already tracking an open position for this symbol
  // (Exit checks are hoisted to run() — executed once per cycle, not per-symbol)
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
    const { orderId, algoId, stopLoss, takeProfit } = await placeLiveOrder(symbol, "buy", tradeSize, price, atr, stopOpts);
    console.log(`  LIVE BUY $${tradeSize.toFixed(2)} @ $${price.toFixed(4)} | Order ${orderId}`);
    console.log(`        SL $${stopLoss.toFixed(4)} | TP $${takeProfit.toFixed(4)}`);

    // Track so we can detect OCO fills on future runs
    const newPos = {
      id: orderId, symbol, side: "buy", mode: "LIVE",
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

// Mark-to-market close any stored positions whose symbol isn't -USDC.
// Handles legacy USDT entries from before the USDC-only rule.
async function purgeStaleNonUsdcPositions() {
  for (const [file, label] of [[POSITIONS_FILE, "PAPER"], [LIVE_POSITIONS_FILE, "LIVE"]]) {
    const positions = loadJson(file, []);
    const stale     = positions.filter(p => p.symbol && !p.symbol.endsWith("-USDC"));
    if (!stale.length) continue;

    console.log(`\nPurging ${stale.length} stale non-USDC ${label} position(s):`);
    for (const pos of stale) {
      let exitPrice = pos.entryPrice;
      try {
        const candles = await fetchCandles(pos.symbol, "1H", 2);
        exitPrice = candles.at(-1)?.close ?? pos.entryPrice;
      } catch {}
      const isLong = pos.side === "buy";
      const pnlUSD = isLong
        ? ((exitPrice - pos.entryPrice) / pos.entryPrice) * pos.size
        : ((pos.entryPrice - exitPrice) / pos.entryPrice) * pos.size;
      const pnlPct = (pnlUSD / pos.size) * 100;
      const holdH  = ((Date.now() - new Date(pos.openedAt).getTime()) / 3_600_000).toFixed(1);
      console.log(`  ${pos.side.toUpperCase()} ${pos.symbol} @ $${pos.entryPrice} → $${exitPrice.toFixed(4)} | P&L ${pnlUSD >= 0 ? "+" : ""}$${pnlUSD.toFixed(2)} (${pnlPct.toFixed(2)}%)`);
      if (label === "PAPER") logClosedTrade(pos, exitPrice, pnlUSD, pnlPct, holdH, "Purged: non-USDC pair no longer supported");
    }
    saveJson(file, positions.filter(p => p.symbol && p.symbol.endsWith("-USDC")));
  }
}

async function run() {
  initCsv();

  // Validate trade mode before doing anything else
  if (!["longs", "perps"].includes(CONFIG.tradeMode)) {
    console.error(`Invalid TRADE_MODE="${CONFIG.tradeMode}". Must be "longs" or "perps".`);
    process.exit(1);
  }
  if (CONFIG.tradeMode === "perps" && !CONFIG.paperTrading) {
    console.error("TRADE_MODE=perps not yet implemented for live. Set TRADE_MODE=longs or PAPER_TRADING=true.");
    process.exit(1);
  }

  // Clean out any legacy USDT/other-quote positions before doing anything
  await purgeStaleNonUsdcPositions();

  // Auto-refresh static tiers weekly from CoinGecko (env vars still override)
  const dynamic = await loadDynamicWatchlists().catch(() => null);
  const tier1 = process.env.SYMBOLS         ? CONFIG.symbols      : (dynamic?.core  ?? CONFIG.symbols);
  const tier2 = process.env.RADAR_SYMBOLS   ? CONFIG.radarSymbols : (dynamic?.radar ?? CONFIG.radarSymbols);
  const tier3 = process.env.MEME_SYMBOLS    ? CONFIG.memeSymbols  : (dynamic?.meme  ?? CONFIG.memeSymbols);

  // Build set of all static watchlist symbols for dedup
  const staticSymbols = new Set([...tier1, ...tier2, ...tier3]);

  // Load trending watchlist (refreshes from CoinGecko once per day)
  const trendingCoins = await loadTrendingWatchlist(staticSymbols).catch(() => []);

  console.log("═══════════════════════════════════════════");
  console.log("  Claude Trading Bot — OKX");
  console.log(`  ${new Date().toISOString()}`);
  console.log(`  Mode    : ${CONFIG.paperTrading ? "PAPER TRADING" : "LIVE TRADING"} (${CONFIG.tradeMode.toUpperCase()})`);
  console.log(`  Tier 1  : ${tier1.join(", ")}`);
  console.log(`  Radar   : ${tier2.join(", ")}`);
  console.log(`  Meme    : ${tier3.join(", ")}`);
  console.log(`  Trending: ${trendingCoins.map(c => c.symbol).join(", ") || "none"}`);
  console.log(`  Strategy: EMA 20/50 Trend + Fear & Greed + ATR + Volume`);
  console.log(`  Cadence : every ${CONFIG.cycleMinutes} min`);
  console.log("═══════════════════════════════════════════");

  // Dynamic portfolio value — query actual account balance each cycle.
  // Falls back to env var PORTFOLIO_VALUE_USD, then to in-memory default ($4617).
  if (!CONFIG.paperTrading && CONFIG.okx.apiKey) {
    const equity = await fetchAccountEquityUSD();
    if (equity && equity > 0) {
      CONFIG.portfolioValue = equity;
      console.log(`Portfolio value (live): $${equity.toFixed(2)}`);

      // Circuit breaker check — may block entries or halt trading entirely
      const canTrade = await checkCircuitBreakers(equity);
      if (!canTrade) {
        console.log("\nTrading halted by circuit breaker. Exiting cycle.\n");
        return;
      }
    }
  } else if (process.env.PORTFOLIO_VALUE_USD) {
    CONFIG.portfolioValue = parseFloat(process.env.PORTFOLIO_VALUE_USD);
  }
  console.log(`Sizing against: $${CONFIG.portfolioValue.toFixed(0)} portfolio`);

  // Hoist exit checks: run once per cycle before any symbol analysis,
  // not once per symbol (fixes H1 audit finding — redundant API calls + race condition).
  if (!CONFIG.paperTrading) {
    await checkLiveExits();
    await tryBreakevenStops();
    await activeExitChecks();
  }

  // Time filter — skip Asian thin-liquidity session unless explicitly disabled.
  // Live entries: 06:00–24:00 UTC. Exits/breakeven still run continuously
  // (we never want to skip protective logic on open positions).
  const utcHour = new Date().getUTCHours();
  const isAsianThin = CONFIG.skipAsianSession && utcHour >= 0 && utcHour < 6;
  if (isAsianThin && !CONFIG.paperTrading) {
    console.log(`\nAsian session (${utcHour}:00 UTC) — exit/breakeven checks done, skipping new entries`);
    console.log("\n═══════════════════════════════════════════\n");
    return;
  }

  const [fearGreed] = await Promise.all([fetchFearGreed()]);
  const weeklySentiment = loadWeeklySentiment();

  if (fearGreed) console.log(`\nFear & Greed Index: ${fearGreed.value}/100 (${fearGreed.label})`);
  if (weeklySentiment) console.log(`Weekly sentiment  : ${weeklySentiment.bias} (score ${weeklySentiment.score})`);

  let todayCount = countTodaysTrades();
  console.log(`Trades today: ${todayCount}/${CONFIG.maxTradesPerDay}`);

  const tiers = [
    { label: "── TIER 1: Core ──────────────────────────", symbols: tier1,                            mult: 1.00 },
    { label: "── TIER 2: On the Radar ──────────────────", symbols: tier2,                            mult: 0.75 },
    { label: "── TIER 3: Meme Coins ────────────────────", symbols: tier3,                            mult: 0.50 },
    { label: "── TIER 4: Trending (CoinGecko) ──────────", symbols: trendingCoins.map(c => c.symbol), mult: 0.30 },
  ];

  for (const tier of tiers) {
    todayCount = countTodaysTrades();
    if (todayCount >= CONFIG.maxTradesPerDay) {
      console.log(`\nDaily cap hit — done for today.`);
      break;
    }

    // Tier 4: cap at MAX_TRENDING_POSITIONS open at once
    // Use correct positions file depending on live vs paper mode (fixes audit M2)
    if (tier.label.includes("TIER 4")) {
      const trendingPosFile = CONFIG.paperTrading ? POSITIONS_FILE : LIVE_POSITIONS_FILE;
      const openTrending = loadJson(trendingPosFile, [])
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

      // Re-check trending cap per symbol (live vs paper fix, audit M2)
      if (tier.label.includes("TIER 4")) {
        const trendingPosFile = CONFIG.paperTrading ? POSITIONS_FILE : LIVE_POSITIONS_FILE;
        const openTrending = loadJson(trendingPosFile, [])
          .filter(p => trendingCoins.some(c => c.symbol === p.symbol)).length;
        if (openTrending >= MAX_TRENDING_POSITIONS) break;
        console.log(`  [TRENDING] ${trendingCoins.find(c => c.symbol === symbol)?.name} — CoinGecko rank #${trendingCoins.find(c => c.symbol === symbol)?.geckoRank}`);
      }

      const mode = tier.label.includes("TIER 4") ? "momentum" : "trend";
      await analyzeSymbol(symbol, todayCount, fearGreed, weeklySentiment, tier.mult, mode).catch(err =>
        console.log(`  ${symbol} error: ${err.message}`)
      );
    }
  }

  console.log("\n═══════════════════════════════════════════\n");
}

async function loop() {
  acquireLock();
  const cycleMs = CONFIG.cycleMinutes * 60 * 1000;
  while (true) {
    await run().catch(err => console.error("Bot error:", err.message));
    const next = new Date(Date.now() + cycleMs);
    console.log(`Next run: ${next.toISOString()} (in ${CONFIG.cycleMinutes} min)\n`);
    await new Promise(r => setTimeout(r, cycleMs));
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
    tradeMode: CONFIG.tradeMode,
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
