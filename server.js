// =====================================================
// 한국투자증권 OpenAPI 프록시 서버
// 브라우저 CORS 문제를 Node.js 서버가 대신 API 호출
// =====================================================
const express = require('express');
const cors    = require('cors');
const path    = require('path');
const fs      = require('fs');
const axios   = require('axios');
const cheerio = require('cheerio');
const iconv = require('iconv-lite');

// Prevent occasional upstream hangs from stalling background refresh queues.
// Can be overridden via env.
const fnGuideClient = axios.create({
  baseURL: 'https://comp.fnguide.com',
  timeout: 20_000,
  headers: {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
    'Accept-Language': 'ko-KR,ko;q=0.9,en;q=0.8',
    Referer: 'https://comp.fnguide.com/',
  },
});
axios.defaults.timeout = Math.max(1_000, Math.min(120_000, Number(process.env.HTTP_TIMEOUT_MS ?? 15_000)));

require('dotenv').config({ path: path.join(__dirname, 'config.env') });

const app  = express();
const PORT = 3000;

// 주가 5,000원 이하 종목은 수집/표시에서 제외
const LOW_PRICE_CUTOFF_KRW = 5000;

// 네이버 시가총액(시장합계) 페이지는 보통 1페이지에 50개 종목이 노출됩니다.
// 일부 환경에서 마지막 페이지(lastPage) 파싱이 과소추정되거나, 뒤쪽 페이지가 반복/빈 페이지로 들어오는 경우가 있어
// “충분한 수(기본 2000개)”를 안정적으로 확보하도록 목표 개수 기반으로 페이지를 더 긁습니다.
const NAVER_MARKET_SUM_ITEMS_PER_PAGE = 50;
const NAVER_MARKET_SUM_MAX_PAGES = 60;
const NAVER_MARKET_SUM_TARGET_ITEMS_DEFAULT = 2000;

app.use(cors());
app.use(express.json({ limit: '100kb' }));
app.use(express.static(path.join(__dirname)));  // index.html 서빙

// 브라우저/프록시 HTTP 캐시로 인해 값이 갱신되지 않는 문제 방지
// - 서버 내부 캐시(TTL)는 유지하되, 클라이언트는 매 요청마다 서버에 재조회하도록 유도
app.use('/api', (req, res, next) => {
  res.set('Cache-Control', 'no-store, no-cache, must-revalidate, proxy-revalidate');
  res.set('Pragma', 'no-cache');
  res.set('Expires', '0');
  res.set('Surrogate-Control', 'no-store');
  next();
});

// ── 관심종목 저장(서버 파일) ────────────────────────────
// GET  /api/favorites  -> { codes: string[], updatedAt: string|null }
// POST /api/favorites  body: { codes: string[] }
const FAVORITES_FILE_PATH = path.join(__dirname, '관심종목.json');

function normalizeStockCode(value) {
  const raw = String(value ?? '').trim();
  if (!raw) return null;
  const digits = raw.replace(/[^0-9]/g, '');
  if (!digits) return null;
  const code = digits.padStart(6, '0').slice(-6);
  return /^[0-9]{6}$/.test(code) ? code : null;
}

function readFavoritesFile() {
  try {
    if (!fs.existsSync(FAVORITES_FILE_PATH)) return { codes: [], updatedAt: null };
    const text = fs.readFileSync(FAVORITES_FILE_PATH, 'utf8');
    const obj = JSON.parse(text);
    const codesRaw = Array.isArray(obj?.codes) ? obj.codes : [];
    const codes = Array.from(new Set(codesRaw.map(normalizeStockCode).filter(Boolean)));
    return { codes, updatedAt: typeof obj?.updatedAt === 'string' ? obj.updatedAt : null };
  } catch {
    return { codes: [], updatedAt: null };
  }
}

function writeFavoritesFile(codes) {
  const uniqueCodes = Array.from(new Set((codes || []).map(normalizeStockCode).filter(Boolean)));
  const payload = {
    updatedAt: new Date().toISOString(),
    codes: uniqueCodes,
  };
  fs.writeFileSync(FAVORITES_FILE_PATH, JSON.stringify(payload, null, 2), 'utf8');
  return payload;
}


app.get('/api/favorites', (req, res) => {
  const data = readFavoritesFile();
  res.json(data);
});

app.post('/api/favorites', (req, res) => {
  try {
    const codes = Array.isArray(req.body?.codes) ? req.body.codes : [];
    const saved = writeFavoritesFile(codes);
    res.json({ ok: true, ...saved });
  } catch (e) {
    res.status(500).json({ ok: false, error: e?.message || String(e) });
  }
});

// ── 한국투자증권 시세 프록시 엔드포인트 ───────────────
// 브라우저 → localhost:3000/api/price?code=005930
//          → Node.js → 한국투자증권 OpenAPI (서버끼리 통신, CORS 없음)
//          → 결과 반환 → 브라우저
let cachedAccessToken = null;
let cachedAccessTokenExpiresAtMs = 0;
let accessTokenInFlight = null;

// decliners는 market/필터 조합이 다양해 단일 전역 캐시로 두면 서로 덮어씁니다.
// effectiveKey별로 캐시/인플라이트를 분리합니다.
const declinersCacheByKey = new Map();

const priceCache = new Map();

const NAVER_BROKER_TARGET_PRICE_TTL_MS_DEFAULT = 6 * 60 * 60 * 1000; // 6h
const naverResearchCache = new Map();

// ── /api/targets 버퍼(캐시) + 백그라운드 리프레시 큐 ─────────
// 목표가/증권사 목표가는 네이버 파싱이 느릴 수 있어,
// API는 가능한 빨리(캐시/스테일) 반환하고 백그라운드에서 갱신합니다.
// 보수적(서버부하↓) 기본값: 자주 갱신하지 않음
const TARGETS_API_PER_TTL_MS_DEFAULT = 10 * 60_000;      // 10m
const TARGETS_API_BROKER_TTL_MS_DEFAULT = 30 * 60_000;   // 30m

const targetsApiPerCache = new Map();    // key -> { value, fetchedAtMs }
const targetsApiBrokerCache = new Map(); // code -> { value, fetchedAtMs }

const targetsApiPerQueue = [];
const targetsApiPerQueued = new Set();
let targetsApiPerRunning = 0;
const TARGETS_API_PER_REFRESH_CONCURRENCY = Math.max(1, Math.min(4, Number(process.env.TARGETS_API_PER_REFRESH_CONCURRENCY ?? 3)));

const targetsApiBrokerQueue = [];
const targetsApiBrokerQueued = new Set();
let targetsApiBrokerRunning = 0;
const TARGETS_API_BROKER_REFRESH_CONCURRENCY = Math.max(1, Math.min(4, Number(process.env.TARGETS_API_BROKER_REFRESH_CONCURRENCY ?? 3)));

function parseEnvBool(value, defaultValue) {
  if (value === undefined || value === null || value === '') return defaultValue;
  const s = String(value).trim().toLowerCase();
  if (s === '1' || s === 'true' || s === 'yes' || s === 'y' || s === 'on') return true;
  if (s === '0' || s === 'false' || s === 'no' || s === 'n' || s === 'off') return false;
  return defaultValue;
}

// ── /api/targets 백그라운드 상시 갱신(로드밸런싱) ─────────
// 프런트가 주기적으로 cacheOnly=1로 캐시만 조회해도,
// 백엔드는 최근 요청된(=hot) 종목을 큐에 넣어 계속 갱신합니다.
const TARGETS_BG_ENABLED = parseEnvBool(process.env.TARGETS_BG_ENABLED, true);
const TARGETS_BG_ACTIVE_WINDOW_MS = Math.max(60_000, Math.min(2 * 60 * 60_000, Number(process.env.TARGETS_BG_ACTIVE_WINDOW_MS ?? 20 * 60_000)));
const TARGETS_BG_TICK_MS = Math.max(250, Math.min(30_000, Number(process.env.TARGETS_BG_TICK_MS ?? 2_000)));
const TARGETS_BG_MAX_ENQUEUE_PER_TICK = Math.max(1, Math.min(120, Number(process.env.TARGETS_BG_MAX_ENQUEUE_PER_TICK ?? 12)));
const TARGETS_BG_PER_TTL_MS = Math.max(10_000, Math.min(6 * 60 * 60_000, Number(process.env.TARGETS_BG_PER_TTL_MS ?? TARGETS_API_PER_TTL_MS_DEFAULT)));
const TARGETS_BG_BROKER_TTL_MS = Math.max(10_000, Math.min(24 * 60 * 60_000, Number(process.env.TARGETS_BG_BROKER_TTL_MS ?? TARGETS_API_BROKER_TTL_MS_DEFAULT)));

const targetsHotByCode = new Map(); // code -> lastSeenMs

function noteTargetsHotCodes(codes) {
  const now = Date.now();
  for (const c of (codes || [])) {
    const code = String(c || '').trim().padStart(6, '0');
    if (!/^[0-9]{6}$/.test(code)) continue;
    targetsHotByCode.set(code, now);
  }
}

function startTargetsBackgroundRefresher() {
  if (!TARGETS_BG_ENABLED) return;

  setInterval(() => {
    try {
      const now = Date.now();
      if (targetsHotByCode.size === 0) return;

      // prune inactive
      for (const [code, lastSeenMs] of targetsHotByCode.entries()) {
        if (!Number.isFinite(lastSeenMs) || (now - lastSeenMs) > TARGETS_BG_ACTIVE_WINDOW_MS) {
          targetsHotByCode.delete(code);
        }
      }
      if (targetsHotByCode.size === 0) return;

      // pick stale-first for brokers (KB/NH/KIS)
      const brokerCandidates = Array.from(targetsHotByCode.keys()).map(code => {
        const entry = targetsApiBrokerCache.get(code);
        const fetchedAtMs = Number(entry?.fetchedAtMs ?? 0);
        const ageMs = fetchedAtMs > 0 ? Math.max(0, now - fetchedAtMs) : Infinity;
        return { code, ageMs };
      }).sort((a, b) => (b.ageMs - a.ageMs)); // oldest first (Infinity first)

      let enqueued = 0;
      for (const it of brokerCandidates) {
        if (enqueued >= TARGETS_BG_MAX_ENQUEUE_PER_TICK) break;
        if (!Number.isFinite(it.ageMs) || it.ageMs > TARGETS_BG_BROKER_TTL_MS) {
          enqueueTargetsApiBrokerRefresh(it.code, {
            brokerTargetPriceTtlMs: NAVER_BROKER_TARGET_PRICE_TTL_MS_DEFAULT,
            brokerMaxPages: Math.max(1, Math.min(30, Number(process.env.NAVER_BROKER_MAX_PAGES ?? 10))),
            brokerMaxNidsPerBroker: Math.max(1, Math.min(10, Number(process.env.NAVER_BROKER_MAX_NIDS_PER_BROKER ?? 5))),
            brokerAllowFallbackAnyBroker: parseEnvBool(process.env.NAVER_BROKER_ALLOW_FALLBACK_ANY_BROKER, true),
          });
          enqueued += 1;
        }
      }

      // PER/PBR도 필요한 경우에만(부하 큰 편) 느슨하게 갱신
      const perTarget = Number(process.env.TARGET_PER ?? 15);
      const pbrTarget = Number(process.env.TARGET_PBR ?? 1);
      const perCandidates = Array.from(targetsHotByCode.keys()).map(code => {
        const key = buildTargetsPerCacheKey(code, perTarget, pbrTarget);
        const entry = targetsApiPerCache.get(key);
        const fetchedAtMs = Number(entry?.fetchedAtMs ?? 0);
        const ageMs = fetchedAtMs > 0 ? Math.max(0, now - fetchedAtMs) : Infinity;
        return { code, key, ageMs };
      }).sort((a, b) => (b.ageMs - a.ageMs));

      for (const it of perCandidates) {
        if (enqueued >= TARGETS_BG_MAX_ENQUEUE_PER_TICK) break;
        if (!Number.isFinite(it.ageMs) || it.ageMs > TARGETS_BG_PER_TTL_MS) {
          enqueueTargetsApiPerRefresh(it.code, {
            targetPer: perTarget,
            targetPbr: pbrTarget,
            priceTtlMs: 120_000,
            salesTtlMs: 6 * 60 * 60 * 1000,
          });
          enqueued += 1;
        }
      }
    } catch {
      // never crash server due to background refresher
    }
  }, TARGETS_BG_TICK_MS);
}

startTargetsBackgroundRefresher();

function buildTargetsPerCacheKey(code, targetPer, targetPbr) {
  const c = String(code || '').trim().padStart(6, '0');
  const per = Number.isFinite(Number(targetPer)) ? Number(targetPer) : 'na';
  const pbr = Number.isFinite(Number(targetPbr)) ? Number(targetPbr) : 'na';
  return `${c}|per${per}|pbr${pbr}`;
}

function getCachedValueSWR(cacheMap, key, ttlMs) {
  const now = Date.now();
  const entry = cacheMap.get(key);
  if (!entry?.value || !Number.isFinite(entry.fetchedAtMs)) {
    return { value: null, fresh: false, ageMs: null };
  }
  const ageMs = Math.max(0, now - entry.fetchedAtMs);
  const fresh = ageMs <= ttlMs;
  return { value: entry.value, fresh, ageMs };
}

function withTimeout(promise, timeoutMs, label) {
  const ms = Math.max(100, Math.min(120_000, Number(timeoutMs) || 0));
  if (!Number.isFinite(ms) || ms <= 0) return promise;
  let t = null;
  const timeout = new Promise((_, reject) => {
    t = setTimeout(() => {
      const err = new Error(`${label || 'job'} timeout after ${ms}ms`);
      err.code = 'TIMEOUT';
      reject(err);
    }, ms);
  });
  return Promise.race([promise, timeout]).finally(() => {
    if (t) clearTimeout(t);
  });
}

function drainTargetsApiPerQueue() {
  while (targetsApiPerRunning < TARGETS_API_PER_REFRESH_CONCURRENCY && targetsApiPerQueue.length > 0) {
    const job = targetsApiPerQueue.shift();
    if (!job) break;
    targetsApiPerRunning += 1;
    (async () => {
      try {
        const timeoutMs = Number(process.env.TARGETS_API_PER_JOB_TIMEOUT_MS ?? 25_000);
        const value = await withTimeout(computePerPbrTargetsForCode(job.code, {
          targetPer: job.targetPer,
          targetPbr: job.targetPbr,
          priceTtlMs: job.priceTtlMs,
          epsTtlMs: job.epsTtlMs ?? job.salesTtlMs,
          salesTtlMs: job.salesTtlMs,
        }), timeoutMs, 'targets-per');
        targetsApiPerCache.set(job.cacheKey, { value, fetchedAtMs: Date.now() });
      } catch (e) {
        if (String(process.env.DEBUG_TARGETS_QUEUE ?? '0') === '1') {
          console.warn('[targets-per] refresh failed:', {
            code: job?.code,
            cacheKey: job?.cacheKey,
            message: e?.message || String(e),
            errCode: e?.code,
          });
        }
      }
    })().finally(() => {
      targetsApiPerRunning -= 1;
      targetsApiPerQueued.delete(job.cacheKey);
      setTimeout(drainTargetsApiPerQueue, 0);
    });
  }
}

function enqueueTargetsApiPerRefresh(code, params) {
  const cacheKey = buildTargetsPerCacheKey(code, params?.targetPer, params?.targetPbr);
  if (targetsApiPerQueued.has(cacheKey)) return;
  targetsApiPerQueued.add(cacheKey);
  targetsApiPerQueue.push({
    code: String(code || '').trim().padStart(6, '0'),
    cacheKey,
    targetPer: params?.targetPer,
    targetPbr: params?.targetPbr,
    priceTtlMs: params?.priceTtlMs,
    // 과거 호환(salesTtlMs) + 신규(epsTtlMs)
    epsTtlMs: params?.epsTtlMs ?? params?.salesTtlMs,
    salesTtlMs: params?.salesTtlMs ?? params?.epsTtlMs,
  });
  // 큐가 너무 커지는 경우(짧은 시간에 과도한 갱신요청) 폭주를 완화
  if (targetsApiPerQueue.length > 2000) targetsApiPerQueue.splice(0, targetsApiPerQueue.length - 2000);
  drainTargetsApiPerQueue();
}

function drainTargetsApiBrokerQueue() {
  while (targetsApiBrokerRunning < TARGETS_API_BROKER_REFRESH_CONCURRENCY && targetsApiBrokerQueue.length > 0) {
    const job = targetsApiBrokerQueue.shift();
    if (!job) break;
    targetsApiBrokerRunning += 1;
    (async () => {
      try {
        const timeoutMs = Number(process.env.TARGETS_API_BROKER_JOB_TIMEOUT_MS ?? 25_000);
        const value = await withTimeout(computeBrokerTargetsForCode(job.code, {
          brokerTargetPriceTtlMs: job.brokerTargetPriceTtlMs,
          brokerMaxPages: job.brokerMaxPages,
          brokerMaxNidsPerBroker: job.brokerMaxNidsPerBroker,
          brokerAllowFallbackAnyBroker: job.brokerAllowFallbackAnyBroker,
        }), timeoutMs, 'targets-brokers');
        targetsApiBrokerCache.set(job.code, { value, fetchedAtMs: Date.now() });
      } catch (e) {
        if (String(process.env.DEBUG_TARGETS_QUEUE ?? '0') === '1') {
          console.warn('[targets-brokers] refresh failed:', {
            code: job?.code,
            message: e?.message || String(e),
            errCode: e?.code,
          });
        }
      }
    })().finally(() => {
      targetsApiBrokerRunning -= 1;
      targetsApiBrokerQueued.delete(job.code);
      setTimeout(drainTargetsApiBrokerQueue, 0);
    });
  }
}

// ── targets 큐/캐시 디버그(로컬용) ───────────────────
// GET /api/_debug/targets-queues
app.get('/api/_debug/targets-queues', (req, res) => {
  if (String(process.env.DEBUG_TARGETS_QUEUE ?? '0') !== '1') {
    return res.status(404).json({ error: 'not found' });
  }
  const perQueuePreview = targetsApiPerQueue.slice(0, 12).map(j => ({
    code: j?.code,
    cacheKey: j?.cacheKey,
  }));
  const brokerQueuePreview = targetsApiBrokerQueue.slice(0, 12).map(j => ({
    code: j?.code,
  }));
  res.json({
    now: new Date().toISOString(),
    per: {
      running: targetsApiPerRunning,
      queuedKeys: targetsApiPerQueued.size,
      queueLen: targetsApiPerQueue.length,
      cacheSize: targetsApiPerCache.size,
      queuePreview: perQueuePreview,
    },
    brokers: {
      running: targetsApiBrokerRunning,
      queuedCodes: targetsApiBrokerQueued.size,
      queueLen: targetsApiBrokerQueue.length,
      cacheSize: targetsApiBrokerCache.size,
      queuePreview: brokerQueuePreview,
    },
    hotCodes: {
      size: targetsHotByCode.size,
    },
    config: {
      perConcurrency: TARGETS_API_PER_REFRESH_CONCURRENCY,
      brokerConcurrency: TARGETS_API_BROKER_REFRESH_CONCURRENCY,
      httpTimeoutMs: axios.defaults.timeout,
      perJobTimeoutMs: Number(process.env.TARGETS_API_PER_JOB_TIMEOUT_MS ?? 25_000),
      brokerJobTimeoutMs: Number(process.env.TARGETS_API_BROKER_JOB_TIMEOUT_MS ?? 25_000),
    },
  });
});

function enqueueTargetsApiBrokerRefresh(code, params) {
  const c = String(code || '').trim().padStart(6, '0');
  if (targetsApiBrokerQueued.has(c)) return;
  targetsApiBrokerQueued.add(c);
  targetsApiBrokerQueue.push({
    code: c,
    brokerTargetPriceTtlMs: params?.brokerTargetPriceTtlMs,
    brokerMaxPages: params?.brokerMaxPages,
    brokerMaxNidsPerBroker: params?.brokerMaxNidsPerBroker,
    brokerAllowFallbackAnyBroker: params?.brokerAllowFallbackAnyBroker,
  });
  if (targetsApiBrokerQueue.length > 2000) targetsApiBrokerQueue.splice(0, targetsApiBrokerQueue.length - 2000);
  drainTargetsApiBrokerQueue();
}

// 미국 10년물 금리는 장중에도 변동하므로, 너무 긴 TTL이면 값이 "멈춘 것처럼" 보일 수 있습니다.
// 실시간에 가까운 소스(Yahoo ^TNX)를 우선 사용하고, 실패 시 FRED(DGS10, 일별)로 fallback 합니다.
const US10Y_TTL_MS_DEFAULT = 60 * 1000; // 60s
const us10yCache = {
  value: null,
  expiresAtMs: 0,
  inFlight: null,
};

const US10Y_SERIES_TTL_MS_DEFAULT = 6 * 60 * 60 * 1000; // 6h
const us10ySeriesCacheByKey = new Map();

// ✅ 미국 기준금리(대용: NY Fed EFFR 타겟 밴드 중간값) 시계열 캐시
const FEDFUNDS_SERIES_TTL_MS_DEFAULT = 6 * 60 * 60 * 1000; // 6h
const fedFundsSeriesCacheByKey = new Map();

// ✅ VIX(공포지수) 시계열 캐시 (Stooq ^VIX, 일별)
const VIX_SERIES_TTL_MS_DEFAULT = 6 * 60 * 60 * 1000; // 6h
const vixSeriesCacheByKey = new Map();

// ✅ 미국 CPI(소비자물가지수) 캐시 (FRED: CPIAUCSL, 월별)
const US_CPI_TTL_MS_DEFAULT = 6 * 60 * 60 * 1000; // 6h
const usCpiCacheByKey = new Map();

// WTI는 장중 갱신이 필요해 실시간(선물) 기준으로 자주 새로고침합니다.
const OIL_WTI_TTL_MS_DEFAULT = 60 * 1000; // 60s
const oilWtiCache = {
  value: null,
  expiresAtMs: 0,
  inFlight: null,
};

const KOSPI_TTL_MS_DEFAULT = 30 * 1000; // 30s
const kospiCache = {
  value: null,
  expiresAtMs: 0,
  inFlight: null,
};

const KOSPI200_SPOT_TTL_MS_DEFAULT = 30 * 1000; // 30s
const kospi200SpotCache = {
  value: null,
  expiresAtMs: 0,
  inFlight: null,
};

// ✅ VKOSPI (한국증시 공포지수) 캐시 추가
const VKOSPI_TTL_MS_DEFAULT = 30 * 1000; // 30s
const vkospiCache = {
  value: null,
  expiresAtMs: 0,
  inFlight: null,
};

// ✅ 공포탐욕지수(Fear & Greed Index) 캐시
// - Data source: alternative.me (public JSON)
// - UI는 코스피200 야간선물과 동일 주기로 갱신합니다.
const FEAR_GREED_TTL_MS_DEFAULT = 30 * 1000; // 30s
const fearGreedCache = {
  value: null,
  expiresAtMs: 0,
  inFlight: null,
};

const MARKET_DEPOSIT_TTL_MS_DEFAULT = 5 * 60 * 1000; // 5m
const marketDepositCache = {
  value: null,
  expiresAtMs: 0,
  inFlight: null,
};

// ✅ 미국 지수 선물 (나스닥100, S&P500) 캐시
const US_FUTURES_TTL_MS_DEFAULT = 30 * 1000; // 30s
const usFuturesCacheBySymbol = new Map();

// ✅ 환율(USD/KRW) 캐시 (Yahoo Finance: KRW=X)
const FX_USDKRW_TTL_MS_DEFAULT = 30 * 1000; // 30s
const fxCacheBySymbol = new Map();

// ✅ 달러인덱스(DXY) 캐시 (Yahoo Finance: DX-Y.NYB)
const DXY_TTL_MS_DEFAULT = 30 * 1000; // 30s

const dxyCache = {
  value: null,
  expiresAtMs: 0,
  inFlight: null,
};

// ✅ 코스피200 야간선물(네이버 KRX 주요시세 > 선물 code=FUT) 캐시
// - 네이버 페이지에는 "선물(2606)"로 표기되며, 야간에도 최근 체결가를 확인할 수 있어
//   UI 상에서는 "코스피200 야간선물"로 표기합니다.
const KOSPI200_NIGHT_FUTURES_TTL_MS_DEFAULT = 30 * 1000; // 30s
const kospi200NightFuturesCache = {
  value: null,
  expiresAtMs: 0,
  inFlight: null,
};

const NAVER_FCHART_OHLC_TTL_MS_DEFAULT = 60 * 60 * 1000; // 1h
const naverFchartOhlcCache = new Map();

const NAVER_OP_PROFIT_TTL_MS_DEFAULT = 12 * 60 * 60 * 1000; // 12h
const operatingProfitCacheByCode = new Map();
const expectedSalesCacheByCode = new Map();

// ✅ 네이버 컨센서스 EPS(추정치) 파싱/캐시
// - PER배수(current_per) 계산에 사용: current_per = 현재가 / 컨센서스 EPS
const naverConsensusEpsCacheByCode = new Map();

// ✅ 네이버 업종(섹터) 파싱/캐시
// - 업종은 자주 바뀌지 않으므로 긴 TTL로 캐시합니다.
const NAVER_SECTOR_TTL_MS_DEFAULT = 30 * 24 * 60 * 60 * 1000; // 30d
const naverSectorCacheByCode = new Map();

// ✅ 네이버 item/main 기반 시세 fallback (유니버스 밖 종목용)
const NAVER_ITEM_MAIN_QUOTE_TTL_MS_DEFAULT = 45_000; // 45s
const naverItemMainQuoteCacheByCode = new Map();

const FOREIGN_FLOW_TTL_MS_DEFAULT = 60 * 1000; // 60s
const foreignFlowCacheByKey = new Map();

const KRX_SHORT_BALANCE_TTL_MS_DEFAULT = 30 * 60 * 1000; // 30m
const krxShortBalanceCacheByKey = new Map();

const MARKET_DIV_RESOLVE_TTL_MS_DEFAULT = 24 * 60 * 60 * 1000; // 24h
const marketDivCacheByCode = new Map();

const RANGE_STOCKS_TTL_MS_DEFAULT = 5 * 60 * 1000; // 5m (네이버 페이지 다수 크롤링)
const rangeStocksCacheByKey = new Map();
const TRADING_VALUE_STOCKS_TTL_MS_DEFAULT = 60 * 1000; // 60s
const tradingValueStocksCacheByKey = new Map();

const RESOLVE_STOCK_UNIVERSE_TTL_MS_DEFAULT = 12 * 60 * 60 * 1000; // 12h (전체 종목 리스트)
const resolveStockUniverseCache = {
  value: null,
  expiresAtMs: 0,
  inFlight: null,
};

const naverClient = axios.create({
  baseURL: 'https://finance.naver.com',
  timeout: 20_000,
  headers: {
    // 기본 UA가 없으면 403/차단이 날 수 있어 브라우저 UA를 설정
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
    'Accept-Language': 'ko-KR,ko;q=0.9,en;q=0.8',
  },
});

const kofiaClient = axios.create({
  baseURL: 'https://freesis.kofia.or.kr',
  timeout: 10_000,
  headers: {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
    'Accept-Language': 'ko-KR,ko;q=0.9,en;q=0.8',
  },
});

const yahooClient = axios.create({
  baseURL: 'https://query1.finance.yahoo.com',
  timeout: 10_000,
  headers: {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
    'Accept-Language': 'ko-KR,ko;q=0.9,en;q=0.8',
    Accept: 'application/json,text/plain,*/*',
  },
});

const alternativeMeClient = axios.create({
  baseURL: 'https://api.alternative.me',
  timeout: 10_000,
  headers: {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
    'Accept-Language': 'ko-KR,ko;q=0.9,en;q=0.8',
    Accept: 'application/json,text/plain,*/*',
  },
});

function formatKstYmdHm(dateLike) {
  const d = dateLike instanceof Date ? dateLike : new Date(dateLike);
  if (!Number.isFinite(d.getTime())) return null;
  try {
    const parts = new Intl.DateTimeFormat('sv-SE', {
      timeZone: 'Asia/Seoul',
      year: 'numeric',
      month: '2-digit',
      day: '2-digit',
      hour: '2-digit',
      minute: '2-digit',
      hourCycle: 'h23',
    }).format(d);
    // sv-SE: 2026-03-05 14:13
    return parts.replace(/-/g, '.');
  } catch {
    const y = d.getFullYear();
    const m = String(d.getMonth() + 1).padStart(2, '0');
    const day = String(d.getDate()).padStart(2, '0');
    const hh = String(d.getHours()).padStart(2, '0');
    const mm = String(d.getMinutes()).padStart(2, '0');
    return `${y}.${m}.${day} ${hh}:${mm}`;
  }
}

async function getYahooFuturesQuote(symbol) {
  const sym = String(symbol || '').trim();
  if (!sym) {
    const err = new Error('symbol 누락');
    err.code = 'INVALID_SYMBOL';
    throw err;
  }

  const res = await yahooClient.get(`/v8/finance/chart/${encodeURIComponent(sym)}`, {
    params: {
      range: '1d',
      interval: '1m',
      includePrePost: 'true',
    },
  });

  const result = res?.data?.chart?.result?.[0] ?? null;
  const meta = result?.meta ?? null;
  const timestamps = Array.isArray(result?.timestamp) ? result.timestamp : [];
  const closes = Array.isArray(result?.indicators?.quote?.[0]?.close) ? result.indicators.quote[0].close : [];

  let lastTradePrice = null;
  let lastTradeUnixSec = null;
  for (let i = Math.min(timestamps.length, closes.length) - 1; i >= 0; i--) {
    const close = Number(closes[i]);
    const ts = Number(timestamps[i]);
    if (!Number.isFinite(close) || !Number.isFinite(ts)) continue;
    lastTradePrice = close;
    lastTradeUnixSec = ts;
    break;
  }

  const fallbackPrice = Number(meta?.regularMarketPrice);
  const price = Number.isFinite(lastTradePrice) ? lastTradePrice : fallbackPrice;
  if (!Number.isFinite(price)) {
    const err = new Error('Yahoo 선물 가격 파싱 실패');
    err.code = 'YAHOO_PARSE_FAILED';
    err.details = { hasResult: !!result };
    throw err;
  }

  const prevClose = Number(meta?.previousClose);
  const change = Number.isFinite(prevClose) ? price - prevClose : null;
  const changeRatePct = Number.isFinite(prevClose) && prevClose !== 0 ? (change / prevClose) * 100 : null;
  const direction = typeof change === 'number' ? (change > 0 ? 'up' : change < 0 ? 'down' : 'flat') : 'flat';

  const fallbackUnixSec = Number(meta?.regularMarketTime);
  const unixSec = Number.isFinite(lastTradeUnixSec) ? lastTradeUnixSec : fallbackUnixSec;
  const time = Number.isFinite(unixSec) ? formatKstYmdHm(unixSec * 1000) : null;
  const isoDate = Number.isFinite(unixSec) ? toIsoDateFromUnixSeconds(unixSec) : null;
  const name = String(meta?.shortName || meta?.longName || sym);

  return {
    name,
    code: sym,
    unit: 'pt',
    time,
    isoDate,
    marketTimeUnixSec: Number.isFinite(unixSec) ? unixSec : null,
    value: price,
    previousClose: Number.isFinite(prevClose) ? prevClose : null,
    change,
    changeRatePct,
    direction,
    sourceUrl: `https://finance.yahoo.com/quote/${encodeURIComponent(sym)}`,
  };
}

async function fetchUs10yFromFred({ timeoutMs } = {}) {
  // FRED graph CSV는 API 키 없이도 접근 가능합니다.
  const url = 'https://fred.stlouisfed.org/graph/fredgraph.csv?id=DGS10';
  const response = await axios.get(url, { timeout: Number(timeoutMs ?? 4_000), responseType: 'text' });
  const parsed = parseFredGraphCsvLastTwo(response.data);
  if (!parsed?.last) {
    throw new Error('FRED DGS10 파싱 실패');
  }
  const change = parsed.prev ? parsed.last.value - parsed.prev.value : null;
  const direction = change === null ? 'flat' : change > 0 ? 'up' : change < 0 ? 'down' : 'flat';
  return {
    series: 'DGS10',
    name: '미국 10년물 국채 금리',
    unit: '%',
    date: parsed.last.date,
    value: parsed.last.value,
    previousDate: parsed.prev?.date ?? null,
    previousValue: parsed.prev?.value ?? null,
    change,
    direction,
    source: 'fred',
    sourceUrl: 'https://fred.stlouisfed.org/series/DGS10',
    updatedAt: new Date().toISOString(),
  };
}

async function fetchUs10yFromYahoo({ timeoutMs } = {}) {
  // Yahoo ^TNX는 보통 "수익률*10" 형태로 제공됩니다. (예: 45.10 => 4.51%)
  const sym = '^TNX';
  const res = await yahooClient.get(`/v8/finance/chart/${encodeURIComponent(sym)}`, {
    params: { range: '1d', interval: '1m', includePrePost: 'true' },
    timeout: Number(timeoutMs ?? 10_000),
  });
  const result = res?.data?.chart?.result?.[0] ?? null;
  const meta = result?.meta ?? null;
  const raw = Number(meta?.regularMarketPrice);
  if (!Number.isFinite(raw)) throw new Error('Yahoo ^TNX 파싱 실패');

  const rawPrev = Number(meta?.previousClose);
  // 데이터 소스/시점에 따라 raw가 이미 %일 수 있습니다(예: 4.13).
  // 일반적인 10년물 수익률은 0~20% 범위이므로, raw가 20 이상이면 /10 스케일로 간주합니다.
  const scale = raw >= 20 ? 10 : 1;
  const value = raw / scale;
  const prev = Number.isFinite(rawPrev) ? rawPrev / scale : null;
  const change = typeof prev === 'number' ? value - prev : null;
  const direction = change === null ? 'flat' : change > 0 ? 'up' : change < 0 ? 'down' : 'flat';

  const unixSec = Number(meta?.regularMarketTime);
  const date = Number.isFinite(unixSec) ? toIsoDateFromUnixSeconds(unixSec) : null;
  const time = Number.isFinite(unixSec) ? formatKstYmdHm(unixSec * 1000) : null;

  return {
    series: sym,
    name: '미국 10년물 국채 금리',
    unit: '%',
    date,
    time,
    value,
    previousDate: null,
    previousValue: prev,
    change,
    direction,
    source: 'yahoo',
    sourceUrl: `https://finance.yahoo.com/quote/${encodeURIComponent(sym)}`,
    updatedAt: new Date().toISOString(),
  };
}

async function getUsFuturesCached(symbol, ttlMs) {
  const sym = String(symbol || '').trim();
  const now = Date.now();
  const existing = usFuturesCacheBySymbol.get(sym);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const parsed = await getYahooFuturesQuote(sym);
    const payload = { ...parsed, updatedAt: new Date().toISOString() };
    usFuturesCacheBySymbol.set(sym, {
      value: payload,
      expiresAtMs: Date.now() + ttlMs,
      inFlight: null,
    });
    return payload;
  })();

  usFuturesCacheBySymbol.set(sym, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const latest = usFuturesCacheBySymbol.get(sym);
    if (latest?.inFlight === inFlight) usFuturesCacheBySymbol.set(sym, { ...latest, inFlight: null });
  }
}

async function getYahooFxQuote(symbol, { nameOverride, unitOverride } = {}) {
  const parsed = await getYahooFuturesQuote(symbol);
  return {
    ...parsed,
    name: nameOverride ?? parsed.name,
    unit: unitOverride ?? parsed.unit,
  };
}

async function getFxCached(symbol, ttlMs, { nameOverride, unitOverride } = {}) {
  const sym = String(symbol || '').trim();
  const now = Date.now();
  const existing = fxCacheBySymbol.get(sym);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const parsed = await getYahooFxQuote(sym, { nameOverride, unitOverride });
    const payload = { ...parsed, updatedAt: new Date().toISOString() };
    fxCacheBySymbol.set(sym, {
      value: payload,
      expiresAtMs: Date.now() + ttlMs,
      inFlight: null,
    });
    return payload;
  })();

  fxCacheBySymbol.set(sym, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const latest = fxCacheBySymbol.get(sym);
    if (latest?.inFlight === inFlight) fxCacheBySymbol.set(sym, { ...latest, inFlight: null });
  }
}

function parseStooqQuoteCsvFirstRow(csvText) {
  const lines = String(csvText || '').trim().split(/\r?\n/);
  if (lines.length < 2) return null;
  const header = lines[0].split(',').map(s => s.trim());
  const row = lines[1].split(',').map(s => String(s ?? '').trim());
  if (row.length !== header.length) return null;
  const out = {};
  for (let i = 0; i < header.length; i++) out[header[i]] = row[i];
  return out;
}

function parseStooqDailyCsvAll(csvText) {
  // Format: Date,Open,High,Low,Close,Volume
  const lines = String(csvText || '').trim().split(/\r?\n/);
  if (lines.length < 2) return [];

  const header = lines[0].split(',').map(s => s.trim().toLowerCase());
  const idxDate = header.indexOf('date');
  const idxClose = header.indexOf('close');
  if (idxDate < 0 || idxClose < 0) return [];

  const items = [];
  for (let i = 1; i < lines.length; i++) {
    const line = lines[i].trim();
    if (!line) continue;
    const cols = line.split(',').map(s => String(s ?? '').trim());
    const date = String(cols[idxDate] ?? '').trim();
    const closeRaw = String(cols[idxClose] ?? '').trim();
    if (!date || !closeRaw) continue;
    const value = Number(closeRaw.replace(/,/g, ''));
    if (!Number.isFinite(value)) continue;
    items.push({ date, value });
  }

  items.sort((a, b) => String(a.date).localeCompare(String(b.date)));
  return items;
}

async function fetchDxyFromStooq({ timeoutMs } = {}) {
  // Stooq realtime-ish quote (DX.F = US Dollar Index futures)
  const url = 'https://stooq.com/q/l/?s=dx.f&f=sd2t2ohlcv&h&e=csv';
  const response = await axios.get(url, { timeout: Number(timeoutMs ?? 8_000), responseType: 'text' });
  const row = parseStooqQuoteCsvFirstRow(response.data);
  if (!row) throw new Error('Stooq DXY 파싱 실패');

  const symbol = String(row.Symbol || row.symbol || 'DX.F').trim();
  const date = String(row.Date || row.date || '').trim();
  const timeRaw = String(row.Time || row.time || '').trim();
  const open = Number(String(row.Open || row.open || '').replace(/,/g, ''));
  const close = Number(String(row.Close || row.close || '').replace(/,/g, ''));
  if (!Number.isFinite(close)) throw new Error('Stooq DXY close 파싱 실패');

  const previousClose = Number.isFinite(open) ? open : null;
  const change = Number.isFinite(previousClose) ? close - previousClose : null;
  const changeRatePct = Number.isFinite(previousClose) && previousClose !== 0
    ? (change / previousClose) * 100
    : null;
  const direction = typeof change === 'number' ? (change > 0 ? 'up' : change < 0 ? 'down' : 'flat') : 'flat';

  const time = (date && timeRaw && timeRaw !== 'N/D') ? `${date} ${timeRaw}` : (date || null);
  const isoDate = date && date !== 'N/D' ? date : null;

  return {
    name: '달러인덱스(DXY)',
    code: symbol || 'DX.F',
    unit: 'pt',
    time,
    isoDate,
    marketTimeUnixSec: null,
    value: close,
    previousClose,
    change,
    changeRatePct,
    direction,
    source: 'stooq',
    sourceUrl: 'https://stooq.com/q/?s=dx.f',
    updatedAt: new Date().toISOString(),
  };
}

async function getDxyCached(ttlMs) {
  const now = Date.now();
  if (dxyCache.value && now < dxyCache.expiresAtMs) return dxyCache.value;
  if (dxyCache.inFlight) return dxyCache.inFlight;

  const inFlight = (async () => {
    let payload = null;
    try {
      // Prefer Yahoo when available (better change/prevClose), but it can 429.
      const parsed = await getYahooFxQuote('DX-Y.NYB', { nameOverride: '달러인덱스(DXY)', unitOverride: 'pt' });
      payload = { ...parsed, updatedAt: new Date().toISOString() };
    } catch {
      payload = await fetchDxyFromStooq({ timeoutMs: 8_000 });
    }
    dxyCache.value = payload;
    dxyCache.expiresAtMs = Date.now() + ttlMs;
    dxyCache.inFlight = null;
    return payload;
  })();

  dxyCache.inFlight = inFlight;
  try {
    return await inFlight;
  } finally {
    if (dxyCache.inFlight === inFlight) dxyCache.inFlight = null;
  }
}

function scoreKoreanReadability(text) {
  if (!text) return 0;
  const hangulMatches = String(text).match(/[가-힣]/g);
  const replacementMatches = String(text).match(/�/g);
  const mojibakeMatches = String(text).match(/����/g);
  const hangulCount = hangulMatches ? hangulMatches.length : 0;
  const replacementCount = replacementMatches ? replacementMatches.length : 0;
  const mojibakeCount = mojibakeMatches ? mojibakeMatches.length : 0;
  return hangulCount - replacementCount * 5 - mojibakeCount * 10;
}

function decodeNaverHtml(data) {
  const buf = Buffer.isBuffer(data) ? data : Buffer.from(data);
  const utf8 = buf.toString('utf8');
  const eucKr = iconv.decode(buf, 'euc-kr');
  return scoreKoreanReadability(eucKr) > scoreKoreanReadability(utf8) ? eucKr : utf8;
}

function parseSignedNumberFromText(text) {
  const m = String(text || '').replace(/,/g, '').match(/([+-]?\d+(?:\.\d+)?)/);
  if (!m) return null;
  const n = Number(m[1]);
  return Number.isFinite(n) ? n : null;
}

function parsePercentFromText(text) {
  const m = String(text || '').replace(/,/g, '').match(/([+-]?\d+(?:\.\d+)?)\s*%/);
  if (!m) return null;
  const n = Number(m[1]);
  return Number.isFinite(n) ? n : null;
}

function parseNaverCompanyAnalysisUnitFromHtml($, $table) {
  if (!$ || !$table) return null;
  const text = String($table.text() || '').replace(/\s+/g, ' ').trim();
  const m = text.match(/단위\s*[:：]?\s*([가-힣]+)/);
  return m ? String(m[1]).trim() : null;
}

function parseNaverAnnualColumnLabelsFromCompanyAnalysisTable($, $table) {
  if (!$ || !$table) return null;

  // 1) "최근 연간 실적" colspan을 우선 신뢰
  let annualCount = null;
  const topHeader = $table.find('thead tr.t_line').first();
  const annualTh = topHeader.find('th').filter((_, el) => {
    const t = String($(el).text() || '').replace(/\s+/g, ' ').trim();
    return t.includes('최근 연간 실적');
  }).first();
  if (annualTh && annualTh.length) {
    const cs = Number(annualTh.attr('colspan'));
    if (Number.isFinite(cs) && cs > 0) annualCount = cs;
  }

  // 2) 연/월 라벨이 있는 헤더 행에서 라벨 리스트 수집
  const yearRowEl = $table.find('thead tr').toArray().find(tr => /\b\d{4}\.\d{2}\b/.test(String($(tr).text() || '')));
  if (!yearRowEl) return null;

  const labels = $(yearRowEl).find('th').toArray().map(th => {
    const text = $(th).text();
    return String(text || '').replace(/\s+/g, ' ').trim();
  }).filter(Boolean);

  // 숫자 패턴이 있는 라벨만 남김 (연간+분기)
  const yearLabels = labels.filter(t => /\b\d{4}\.\d{2}\b/.test(t));
  if (yearLabels.length === 0) return null;

  const n = annualCount ?? Math.min(5, yearLabels.length);
  return {
    annualCount: Math.max(1, Math.min(n, yearLabels.length)),
    annualLabels: yearLabels,
  };
}

function parseNaverOperatingProfitFromItemMainHtml(html) {
  const $ = cheerio.load(String(html || ''));
  const $table = $('table.tb_type1_ifrs').first();
  if (!$table || $table.length === 0) return null;

  const meta = parseNaverAnnualColumnLabelsFromCompanyAnalysisTable($, $table);
  if (!meta?.annualCount) return null;

  const annualCount = meta.annualCount;
  const annualLabels = meta.annualLabels.slice(0, annualCount);

  const $opRow = $table.find('tr').filter((_, tr) => {
    const thText = $(tr).find('th[scope="row"]').first().text();
    const label = String(thText || '').replace(/\s+/g, ' ').trim();
    return label === '영업이익';
  }).first();

  if (!$opRow || $opRow.length === 0) return null;
  const tds = $opRow.find('td').toArray();
  if (!tds || tds.length < annualCount) return null;

  const annualValues = tds.slice(0, annualCount).map(td => {
    const text = $(td).text();
    const cleaned = String(text || '').replace(/\s+/g, ' ').trim();
    if (!cleaned || cleaned === '-' || cleaned === 'N/A') return null;
    return parseNumberWithCommas(cleaned);
  });

  const unit = parseNaverCompanyAnalysisUnitFromHtml($, $table) || '억원';
  return { annualLabels, annualValues, unit };
}

function normalizeFinanceRowLabel(text) {
  return String(text || '').replace(/\u00a0/g, ' ').replace(/\s+/g, ' ').trim();
}

function parseFnGuideAnnualRowFromFinanceHtml(html, rowLabel) {
  const $ = cheerio.load(String(html || ''));
  const wanted = normalizeFinanceRowLabel(rowLabel);
  if (!wanted) return null;

  const tableConfigs = [
    { selector: '#highlight_D_Y table', unit: '억원' },
    { selector: '#highlight_B_Y table', unit: '억원' },
  ];

  for (const config of tableConfigs) {
    const $table = $(config.selector).first();
    if (!$table || $table.length === 0) continue;

    const annualLabels = $table.find('thead tr').last().find('th').toArray()
      .map(th => normalizeFinanceRowLabel($(th).text()))
      .filter(text => /^\d{4}\/\d{2}$/.test(text));
    if (annualLabels.length === 0) continue;

    const $row = $table.find('tbody tr').filter((_, tr) => {
      const label = normalizeFinanceRowLabel($(tr).find('th[scope="row"]').first().text());
      return label === wanted;
    }).first();
    if (!$row || $row.length === 0) continue;

    const annualValues = $row.find('td').toArray().slice(0, annualLabels.length).map(td => {
      const text = normalizeFinanceRowLabel($(td).text());
      if (!text || text === '-' || text === 'N/A') return null;
      return parseNumberWithCommas(text);
    });

    return {
      annualLabels,
      annualValues,
      unit: config.unit,
    };
  }

  return null;
}

function parseNaverAnnualRowFromItemMainHtml(html, rowLabel) {
  const $ = cheerio.load(String(html || ''));
  const $table = $('table.tb_type1_ifrs').first();
  if (!$table || $table.length === 0) return null;

  const meta = parseNaverAnnualColumnLabelsFromCompanyAnalysisTable($, $table);
  if (!meta?.annualCount) return null;

  const annualCount = meta.annualCount;
  const annualLabels = meta.annualLabels.slice(0, annualCount);

  const wanted = String(rowLabel || '').replace(/\s+/g, ' ').trim();
  if (!wanted) return null;

  const $row = $table.find('tr').filter((_, tr) => {
    const thText = $(tr).find('th[scope="row"]').first().text();
    const label = String(thText || '').replace(/\s+/g, ' ').trim();
    return label === wanted;
  }).first();

  if (!$row || $row.length === 0) return null;
  const tds = $row.find('td').toArray();
  if (!tds || tds.length < annualCount) return null;

  const annualValues = tds.slice(0, annualCount).map(td => {
    const text = $(td).text();
    const cleaned = String(text || '').replace(/\s+/g, ' ').trim();
    if (!cleaned || cleaned === '-' || cleaned === 'N/A') return null;
    return parseNumberWithCommas(cleaned);
  });

  const unit = parseNaverCompanyAnalysisUnitFromHtml($, $table) || '억원';
  return { annualLabels, annualValues, unit };
}

function pickPreferredAnnualEstimate(parsed, preferYear) {
  if (!parsed?.annualLabels || !parsed?.annualValues) return null;
  const entries = parsed.annualLabels.map((label, i) => {
    const lbl = String(label || '').replace(/\s+/g, ' ').trim();
    const year = Number((lbl.match(/^(\d{4})\./) || [])[1]);
    const value = parsed.annualValues[i];
    const isEstimate = /\(\s*E\s*\)|\bE\b|추정|예상/i.test(lbl);
    return {
      label: lbl,
      year: Number.isFinite(year) ? year : null,
      value: (value === null || value === undefined) ? null : Number(value),
      isEstimate,
    };
  }).filter(e => e.year && Number.isFinite(e.year));

  const prefer = entries.find(e => e.year === preferYear && e.isEstimate && Number.isFinite(e.value));
  if (prefer) return prefer;

  const est = entries
    .filter(e => e.isEstimate && Number.isFinite(e.value))
    .sort((a, b) => (a.year - b.year) || String(a.label).localeCompare(String(b.label)))
    .pop();
  if (est) return est;

  const latest = entries
    .filter(e => Number.isFinite(e.value))
    .sort((a, b) => (a.year - b.year) || String(a.label).localeCompare(String(b.label)))
    .pop();
  return latest || null;
}

function parseNaverListedSharesFromItemMainHtml(html) {
  const $ = cheerio.load(String(html || ''));
  let text = '';

  const $th = $('th').filter((_, el) => {
    const t = String($(el).text() || '').replace(/\s+/g, ' ').trim();
    return t.includes('상장주식수');
  }).first();

  if ($th && $th.length) {
    text = String($th.next('td')?.text?.() || '').trim();
    if (!text) {
      text = String($th.parent()?.find('td')?.first()?.text?.() || '').trim();
    }
  }

  if (!text) {
    // Fallback: regex search on raw HTML
    const raw = String(html || '');
    const m = raw.match(/상장주식수[\s\S]{0,200}?([0-9]{1,3}(?:,[0-9]{3})+)/);
    if (m) text = m[1];
  }

  const cleaned = String(text || '').replace(/\s+/g, ' ').trim();
  if (!cleaned) return null;
  const m1 = cleaned.match(/([0-9]{1,3}(?:,[0-9]{3})+|[0-9]+)/);
  const base = parseNumberWithCommas(m1 ? m1[1] : cleaned);
  if (!Number.isFinite(base)) return null;

  // Some pages may show units like '천주', '만주'
  if (cleaned.includes('천주')) return Math.round(base * 1000);
  if (cleaned.includes('만주')) return Math.round(base * 10000);
  return Math.round(base);
}

function normalizeLooseText(s) {
  return String(s || '').replace(/\s+/g, ' ').trim();
}

function findNaverValueTextByLabel($, labelPredicate) {
  if (!$ || typeof labelPredicate !== 'function') return null;

  const pickValueFrom = ($labelEl) => {
    if (!$labelEl || !$labelEl.length) return null;

    // Common patterns: <th>라벨</th><td>값</td>, <dt>라벨</dt><dd>값</dd>
    const $nextTd = $labelEl.next('td');
    if ($nextTd && $nextTd.length) {
      const t = normalizeLooseText($nextTd.text());
      if (t) return t;
    }
    const $nextDd = $labelEl.next('dd');
    if ($nextDd && $nextDd.length) {
      const t = normalizeLooseText($nextDd.text());
      if (t) return t;
    }

    const $tr = $labelEl.closest('tr');
    if ($tr && $tr.length) {
      const $td = $tr.find('td').first();
      const t = normalizeLooseText($td.text());
      if (t) return t;
    }

    const $dl = $labelEl.closest('dl');
    if ($dl && $dl.length) {
      const $dd = $labelEl.closest('dt').next('dd');
      const t = normalizeLooseText($dd.text());
      if (t) return t;
    }

    // Fallback: try parent row/box text
    const parentText = normalizeLooseText($labelEl.parent().text());
    return parentText || null;
  };

  const els = $('th, dt, span, strong, em').toArray();
  for (const el of els) {
    const t = normalizeLooseText($(el).text());
    if (!t) continue;
    if (!labelPredicate(t)) continue;
    const v = pickValueFrom($(el));
    if (v) return v;
  }
  return null;
}

function parseNaverEpsAndCreditFromItemMainHtml(html) {
  const raw = String(html || '');
  const $ = cheerio.load(raw);

  // EPS
  let eps = null;
  try {
    const epsText = findNaverValueTextByLabel($, (t) => t === 'EPS' || t.startsWith('EPS'));
    const n = parseSignedNumberFromText(epsText);
    if (Number.isFinite(n)) eps = n;
  } catch {
    eps = null;
  }
  if (!Number.isFinite(eps)) {
    const m = raw
      .replace(/\s+/g, ' ')
      .match(/\bEPS\b[\s\S]{0,200}?([+-]?(?:\d{1,3}(?:,\d{3})+|\d+)(?:\.\d+)?)/i);
    const n = parseSignedNumberFromText(m ? m[1] : null);
    if (Number.isFinite(n)) eps = n;
  }

  // Credit ratio (%): 신용비율
  let creditRatioPct = null;
  try {
    const creditText = findNaverValueTextByLabel($, (t) => t.includes('신용비율'));
    const p = parseSignedNumberFromText(creditText);
    if (Number.isFinite(p)) creditRatioPct = p;
  } catch {
    creditRatioPct = null;
  }

  if (!Number.isFinite(creditRatioPct)) {
    const m = raw
      .replace(/\s+/g, ' ')
      .match(/신용비율[\s\S]{0,200}?([+-]?\d+(?:\.\d+)?)\s*%?/);
    const n = parseSignedNumberFromText(m ? m[1] : null);
    if (Number.isFinite(n)) creditRatioPct = n;
  }

  return {
    eps: Number.isFinite(eps) ? eps : null,
    creditRatioPct: Number.isFinite(creditRatioPct) ? creditRatioPct : null,
  };
}

function parseNaverConsensusEpsFromItemMainHtml(html) {
  const raw = String(html || '');
  const $ = cheerio.load(raw);

  const parseEpsFromText = (textLike) => {
    const n = parseSignedNumberFromText(textLike);
    return Number.isFinite(n) ? n : null;
  };

  // 1) label 기반(가장 안정): EPS + 추정/예상/E/컨센서스 표기 우선
  try {
    const preferredText = findNaverValueTextByLabel($, (t) => {
      const s = normalizeLooseText(t);
      if (!s) return false;
      if (!/^EPS\b/i.test(s)) return false;
      return /(추정|예상|컨센서스|\bE\b|\(\s*E\s*\)|\(.*E.*\))/i.test(s);
    });
    const preferred = parseEpsFromText(preferredText);
    if (Number.isFinite(preferred)) return preferred;
  } catch {
    // ignore
  }

  // 2) 정규식 fallback: EPS(2026E) 등
  try {
    const flat = raw.replace(/\s+/g, ' ');
    const m = flat.match(/EPS\s*\([^)]*E[^)]*\)[\s\S]{0,120}?([+-]?(?:\d{1,3}(?:,\d{3})+|\d+)(?:\.\d+)?)/i);
    const picked = parseEpsFromText(m ? m[1] : null);
    if (Number.isFinite(picked)) return picked;
  } catch {
    // ignore
  }

  // 3) 컨센서스 문구 주변 fallback
  try {
    const flat = raw.replace(/\s+/g, ' ');
    const m = flat.match(/컨센서스[\s\S]{0,200}?EPS[\s\S]{0,80}?([+-]?(?:\d{1,3}(?:,\d{3})+|\d+)(?:\.\d+)?)/i);
    const picked = parseEpsFromText(m ? m[1] : null);
    if (Number.isFinite(picked)) return picked;
  } catch {
    // ignore
  }

  // 4) 최후 fallback: item/main의 EPS(표기만 EPS인 경우)
  try {
    const keyStats = parseNaverEpsAndCreditFromItemMainHtml(raw);
    const eps = Number(keyStats?.eps);
    return Number.isFinite(eps) ? eps : null;
  } catch {
    return null;
  }
}

async function getNaverConsensusEpsEstimate(code) {
  const itemCode = String(code || '').trim().padStart(6, '0');
  if (!/^[0-9]{6}$/.test(itemCode)) {
    const err = new Error('유효하지 않은 code');
    err.code = 'INVALID_CODE';
    throw err;
  }

  const html = await fetchNaverHtml('/item/main.naver', { code: itemCode });
  const epsConsensus = parseNaverConsensusEpsFromItemMainHtml(html);

  return {
    code: itemCode,
    epsConsensus: Number.isFinite(Number(epsConsensus)) ? Number(epsConsensus) : null,
    sourceUrl: `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(itemCode)}`,
    updatedAt: new Date().toISOString(),
  };
}

async function getNaverConsensusEpsEstimateCached(code, ttlMs) {
  const itemCode = String(code || '').trim().padStart(6, '0');
  const ms = Math.max(60_000, Math.min(24 * 60 * 60 * 1000, Number(ttlMs ?? 6 * 60 * 60 * 1000)));
  const now = Date.now();
  const existing = naverConsensusEpsCacheByCode.get(itemCode);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const value = await getNaverConsensusEpsEstimate(itemCode);
    naverConsensusEpsCacheByCode.set(itemCode, { value, expiresAtMs: Date.now() + ms, inFlight: null });
    return value;
  })();

  naverConsensusEpsCacheByCode.set(itemCode, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const entry = naverConsensusEpsCacheByCode.get(itemCode);
    if (entry?.inFlight === inFlight) {
      naverConsensusEpsCacheByCode.set(itemCode, { ...entry, inFlight: null });
    }
  }
}

function parseNaverSectorFromItemMainHtml(html) {
  const raw = String(html || '');
  const $ = cheerio.load(raw);

  const extractIndustryName = (textLike) => {
    const t = String(textLike || '').replace(/\s+/g, ' ').trim();
    if (!t) return null;
    if (t === '업종별') return null;
    if (/^업종명\s*[:：]?\s*$/.test(t)) return null;
    if (/^업종\s*[:：]?\s*$/.test(t)) return null;
    // Prefer explicit "업종명 : XXX" patterns.
    const m = t.match(/업종명\s*[:：]\s*([^|)\]】\n\r]{1,60})/);
    if (m) {
      const picked = String(m[1] || '').trim();
      if (picked) return picked;
    }
    // If the whole string is short, accept as-is.
    if (t.length <= 30) return t;
    return null;
  };

  // 0) Fast path: raw text contains 업종명
  try {
    const flat = raw.replace(/\s+/g, ' ');
    const m = flat.match(/업종명\s*[:：]\s*([^|)\]】<]{1,60})/);
    const picked = extractIndustryName(m ? `업종명:${m[1]}` : null);
    if (picked) return picked;
  } catch {
    // ignore
  }

  // 0.5) 업종 상세 링크(type=upjong)에서 업종명 직접 추출(가장 정확)
  try {
    const anchors = $('a[href*="type=upjong"], a[href*="sise_group_detail.naver"][href*="upjong"]').toArray();
    for (const a of anchors) {
      const txt = normalizeLooseText($(a).text());
      if (!txt) continue;
      // 퀵링크/메뉴의 "업종별"은 업종명이 아니므로 제외
      if (txt === '업종별') continue;
      // 너무 긴 문자열은 제외(광고/템플릿 가능성)
      if (txt.length > 40) continue;
      return txt;
    }
  } catch {
    // ignore
  }

  // 0.6) 정규식으로 업종 상세 링크 앵커 텍스트 직접 추출(HTML 구조 변화 방어)
  try {
    const flat = raw.replace(/\s+/g, ' ');
    const m = flat.match(/sise_group_detail\.naver\?type=upjong[^"']{0,200}>([^<]{1,40})<\s*\/a>/i);
    const txt = normalizeLooseText(m ? m[1] : null);
    if (txt && txt !== '업종별' && !/^업종명\s*[:：]?\s*$/.test(txt)) return txt;
  } catch {
    // ignore
  }

  // 1) label 기반(기존 helper 재사용)
  try {
    const v = findNaverValueTextByLabel($, (t) => t === '업종' || t.includes('업종'));
    const picked = extractIndustryName(v);
    if (picked) return picked;
  } catch {
    // ignore
  }

  // 2) 테이블/정적 구조 기반(방어)
  try {
    const th = $('th, dt').toArray().find((el) => {
      const t = normalizeLooseText($(el).text());
      return t === '업종' || t === '업종명';
    });
    if (th) {
      const $th = $(th);
      const $val = $th.next('td, dd').first();
      const picked = extractIndustryName($val.text());
      if (picked) return picked;
    }
  } catch {
    // ignore
  }

  // 3) 정규식 fallback
  try {
    const s = raw.replace(/\s+/g, ' ');
    // 업종</th><td>XXX</td> 또는 업종</dt><dd>XXX</dd>
    const m = s.match(/업종(?:명)?\s*<\/(?:th|dt)>\s*<\s*(?:td|dd)[^>]*>\s*([^<]{1,80})\s*<\//i);
    const picked = extractIndustryName(m ? m[1] : null);
    if (picked) return picked;
  } catch {
    // ignore
  }

  return null;
}

function parseLooseNumberFromText(text) {
  const raw = String(text ?? '').trim();
  if (!raw || raw === '-') return null;
  const normalized = raw
    .replace(/,/g, '')
    .replace(/%/g, '')
    .replace(/[\u2212\u2013\u2014\uFF0D]/g, '-')
    .replace(/\s+/g, ' ');
  const m = normalized.match(/[-+]?\d*\.?\d+(?:e[-+]?\d+)?/i);
  if (!m) return null;
  const n = Number(m[0]);
  return Number.isFinite(n) ? n : null;
}

function parseNaverQuoteFromItemMainHtml(html) {
  try {
    const raw = String(html || '');
    const $ = cheerio.load(raw);

    const name = (
      $('div.wrap_company h2 a').first().text().trim() ||
      $('div.wrap_company h2').first().text().trim() ||
      $('h2 a').first().text().trim() ||
      $('h2').first().text().trim() ||
      null
    );

    const blindTexts = $('p.no_today span.blind')
      .map((_, el) => $(el).text().trim())
      .get()
      .filter(Boolean);

    let stck_prpr = null;
    let prdy_vrss = null;
    let prdy_ctrt = null;

    // Most reliable numeric signals live in blind spans.
    const nums = blindTexts.map(parseLooseNumberFromText).filter((n) => Number.isFinite(n));
    if (nums.length >= 1) stck_prpr = nums[0];
    if (nums.length >= 2) prdy_vrss = nums[1];

    // Prefer explicit percent parsing.
    const pctText = blindTexts.find(t => String(t).includes('%'));
    const pct = parseLooseNumberFromText(pctText);
    if (Number.isFinite(pct)) prdy_ctrt = pct;

    const hasDown = blindTexts.some(t => /하락/i.test(String(t)));
    const hasUp = blindTexts.some(t => /상승/i.test(String(t)));
    if (Number.isFinite(prdy_ctrt)) {
      if (hasDown && prdy_ctrt > 0) prdy_ctrt = -prdy_ctrt;
      if (hasUp && prdy_ctrt < 0) prdy_ctrt = Math.abs(prdy_ctrt);
    }
    if (Number.isFinite(prdy_vrss)) {
      if (hasDown && prdy_vrss > 0) prdy_vrss = -prdy_vrss;
      if (hasUp && prdy_vrss < 0) prdy_vrss = Math.abs(prdy_vrss);
    }

    return {
      name: name || null,
      stck_prpr: Number.isFinite(stck_prpr) ? stck_prpr : null,
      prdy_vrss: Number.isFinite(prdy_vrss) ? prdy_vrss : null,
      prdy_ctrt: Number.isFinite(prdy_ctrt) ? prdy_ctrt : null,
    };
  } catch {
    return { name: null, stck_prpr: null, prdy_vrss: null, prdy_ctrt: null };
  }
}

async function getNaverItemMainQuoteCached(code, ttlMs) {
  const itemCode = String(code || '').trim().padStart(6, '0');
  if (!/^[0-9]{6}$/.test(itemCode)) {
    const err = new Error('유효하지 않은 code');
    err.code = 'INVALID_CODE';
    throw err;
  }

  const ms = Math.max(5_000, Math.min(10 * 60_000, Number(ttlMs ?? NAVER_ITEM_MAIN_QUOTE_TTL_MS_DEFAULT)));
  const now = Date.now();
  const existing = naverItemMainQuoteCacheByCode.get(itemCode);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const html = await fetchNaverHtml('/item/main.naver', { code: itemCode });
    const parsed = parseNaverQuoteFromItemMainHtml(html);
    const value = {
      code: itemCode,
      name: parsed?.name ?? null,
      stck_prpr: parsed?.stck_prpr ?? null,
      prdy_vrss: parsed?.prdy_vrss ?? null,
      prdy_ctrt: parsed?.prdy_ctrt ?? null,
      sourceUrl: `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(itemCode)}`,
      updatedAt: new Date().toISOString(),
    };
    naverItemMainQuoteCacheByCode.set(itemCode, { value, expiresAtMs: Date.now() + ms, inFlight: null });
    return value;
  })();

  naverItemMainQuoteCacheByCode.set(itemCode, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const entry = naverItemMainQuoteCacheByCode.get(itemCode);
    if (entry?.inFlight === inFlight) {
      naverItemMainQuoteCacheByCode.set(itemCode, { ...entry, inFlight: null });
    }
  }
}

function unitToWonMultiplier(unitText) {
  const u = String(unitText || '').replace(/\s+/g, '');
  if (!u) return 100_000_000;
  if (u.includes('십억원')) return 1_000_000_000;
  if (u.includes('억원')) return 100_000_000;
  if (u.includes('천만원')) return 10_000_000;
  if (u.includes('백만원')) return 1_000_000;
  if (u.includes('원')) return 1;
  return 100_000_000;
}

async function getNaverExpectedSalesAndShares(code) {
  const itemCode = String(code || '').trim().padStart(6, '0');
  if (!/^[0-9]{6}$/.test(itemCode)) {
    const err = new Error('유효하지 않은 code');
    err.code = 'INVALID_CODE';
    throw err;
  }

  const html = await fetchNaverHtml('/item/main.naver', { code: itemCode });
  const sales = parseNaverAnnualRowFromItemMainHtml(html, '매출액');
  const shares = parseNaverListedSharesFromItemMainHtml(html);

  if (!sales) {
    const err = new Error('네이버 매출액 파싱 실패');
    err.code = 'NAVER_PARSE_FAILED';
    throw err;
  }

  const nowYear = new Date().getFullYear();
  const picked = pickPreferredAnnualEstimate(sales, nowYear);

  return {
    code: itemCode,
    unit: sales.unit || '억원',
    expectedYear: picked?.year ?? null,
    expectedLabel: picked?.label ?? null,
    expectedSales: Number.isFinite(Number(picked?.value)) ? Number(picked.value) : null,
    listedShares: Number.isFinite(Number(shares)) ? Number(shares) : null,
    sourceUrl: `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(itemCode)}`,
  };
}

async function getNaverExpectedSalesAndSharesCached(code, ttlMs) {
  const itemCode = String(code || '').trim().padStart(6, '0');
  const now = Date.now();
  const existing = expectedSalesCacheByCode.get(itemCode);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const value = await getNaverExpectedSalesAndShares(itemCode);
    expectedSalesCacheByCode.set(itemCode, { value, expiresAtMs: Date.now() + ttlMs, inFlight: null });
    return value;
  })();

  expectedSalesCacheByCode.set(itemCode, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const entry = expectedSalesCacheByCode.get(itemCode);
    if (entry?.inFlight === inFlight) {
      expectedSalesCacheByCode.set(itemCode, { ...entry, inFlight: null });
    }
  }
}

async function getNaverOperatingProfit(code) {
  const itemCode = String(code || '').trim().padStart(6, '0');
  if (!/^[0-9]{6}$/.test(itemCode)) {
    const err = new Error('유효하지 않은 code');
    err.code = 'INVALID_CODE';
    throw err;
  }

  const html = await fetchNaverHtml('/item/main.naver', { code: itemCode });
  const parsed = parseNaverOperatingProfitFromItemMainHtml(html);
  if (!parsed) {
    const err = new Error('네이버 영업이익 파싱 실패');
    err.code = 'NAVER_PARSE_FAILED';
    throw err;
  }

  const keyStats = parseNaverEpsAndCreditFromItemMainHtml(html);

  const nowYear = new Date().getFullYear();
  const recentYears = Array.from({ length: 5 }, (_, idx) => nowYear - (idx + 1));

  const findByYear = (year) => {
    const idx = parsed.annualLabels.findIndex(lbl => String(lbl).startsWith(String(year)));
    if (idx < 0) return null;
    return {
      label: parsed.annualLabels[idx] ?? null,
      value: parsed.annualValues[idx] ?? null,
    };
  };

  let fnGuideParsed = null;
  const needsOlderHistory = recentYears.some((year) => {
    const found = findByYear(year);
    return !(found?.label || Number.isFinite(found?.value));
  });

  if (needsOlderHistory) {
    try {
      const fnGuideHtml = await fetchFnGuideHtml('/SVO2/ASP/SVD_Main.asp', {
        pGB: 1,
        gicode: `A${itemCode}`,
        cID: '',
        MenuYn: 'Y',
        ReportGB: '',
        NewMenuID: 101,
        stkGb: 701,
      });
      fnGuideParsed = parseFnGuideAnnualRowFromFinanceHtml(fnGuideHtml, '영업이익');
    } catch {
      fnGuideParsed = null;
    }
  }

  const findFnGuideByYear = (year) => {
    if (!fnGuideParsed?.annualLabels?.length) return null;
    const idx = fnGuideParsed.annualLabels.findIndex(lbl => String(lbl).startsWith(String(year)));
    if (idx < 0) return null;
    return {
      label: fnGuideParsed.annualLabels[idx] ?? null,
      value: fnGuideParsed.annualValues[idx] ?? null,
    };
  };

  const annualOpProfits = recentYears.map((year) => {
    const found = findByYear(year);
    const fallback = (!(found?.label || Number.isFinite(found?.value))) ? findFnGuideByYear(year) : null;
    return {
      year,
      label: found?.label ?? fallback?.label ?? null,
      value: found?.value ?? fallback?.value ?? null,
    };
  });

  const [last, prev, third, fourth, fifth] = annualOpProfits;

  return {
    code: itemCode,
    unit: parsed.unit || '억원',
    annualOpProfits,
    lastYear: last?.year ?? null,
    prevYear: prev?.year ?? null,
    thirdYear: third?.year ?? null,
    fourthYear: fourth?.year ?? null,
    fifthYear: fifth?.year ?? null,
    lastYearLabel: last?.label ?? null,
    prevYearLabel: prev?.label ?? null,
    thirdYearLabel: third?.label ?? null,
    fourthYearLabel: fourth?.label ?? null,
    fifthYearLabel: fifth?.label ?? null,
    opProfitLastYear: last?.value ?? null,
    opProfitPrevYear: prev?.value ?? null,
    opProfitThirdYear: third?.value ?? null,
    opProfitFourthYear: fourth?.value ?? null,
    opProfitFifthYear: fifth?.value ?? null,
    eps: keyStats?.eps ?? null,
    creditRatioPct: keyStats?.creditRatioPct ?? null,
    sourceUrl: `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(itemCode)}`,
  };
}

async function getNaverOperatingProfitCached(code, ttlMs) {
  const itemCode = String(code || '').trim().padStart(6, '0');
  const now = Date.now();
  const existing = operatingProfitCacheByCode.get(itemCode);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const value = await getNaverOperatingProfit(itemCode);
    operatingProfitCacheByCode.set(itemCode, { value, expiresAtMs: Date.now() + ttlMs, inFlight: null });
    return value;
  })();

  operatingProfitCacheByCode.set(itemCode, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const entry = operatingProfitCacheByCode.get(itemCode);
    if (entry?.inFlight === inFlight) {
      operatingProfitCacheByCode.set(itemCode, { ...entry, inFlight: null });
    }
  }
}

async function getNaverSectorCached(code, ttlMs) {
  const itemCode = String(code || '').trim().padStart(6, '0');
  if (!/^[0-9]{6}$/.test(itemCode)) {
    const err = new Error('유효하지 않은 code');
    err.code = 'INVALID_CODE';
    throw err;
  }

  const ms = Math.max(60_000, Math.min(180 * 24 * 60 * 60 * 1000, Number(ttlMs ?? NAVER_SECTOR_TTL_MS_DEFAULT)));
  const now = Date.now();
  const existing = naverSectorCacheByCode.get(itemCode);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const html = await fetchNaverHtml('/item/main.naver', { code: itemCode });
    const sector = parseNaverSectorFromItemMainHtml(html);
    const value = {
      code: itemCode,
      sector: sector || null,
      sourceUrl: `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(itemCode)}`,
      updatedAt: new Date().toISOString(),
    };
    naverSectorCacheByCode.set(itemCode, { value, expiresAtMs: Date.now() + ms, inFlight: null });
    return value;
  })();

  naverSectorCacheByCode.set(itemCode, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const entry = naverSectorCacheByCode.get(itemCode);
    if (entry?.inFlight === inFlight) {
      naverSectorCacheByCode.set(itemCode, { ...entry, inFlight: null });
    }
  }
}

async function fetchNaverHtml(pathname, params) {
  const response = await naverClient.get(pathname, {
    params,
    responseType: 'arraybuffer',
  });
  return decodeNaverHtml(response.data);
}

async function fetchFnGuideHtml(pathname, params) {
  const response = await fnGuideClient.get(pathname, {
    params,
    responseType: 'arraybuffer',
  });
  return decodeNaverHtml(response.data);
}

async function fetchNaverFchartOhlcXml({ symbol, timeframe, count }) {
  const url = 'https://fchart.stock.naver.com/sise.nhn';
  const response = await axios.get(url, {
    timeout: 10_000,
    responseType: 'arraybuffer',
    headers: {
      'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
      'Accept-Language': 'ko-KR,ko;q=0.9,en;q=0.8',
    },
    params: {
      symbol,
      timeframe,
      count,
      requestType: 0,
    },
  });

  // fchart는 EUC-KR XML을 내려줍니다.
  const buf = Buffer.isBuffer(response.data) ? response.data : Buffer.from(response.data);
  return iconv.decode(buf, 'euc-kr');
}

function parseNaverFchartOhlcFromXml(xml) {
  const out = [];
  const re = /<item\s+data="(\d{8})\|(\d+)\|(\d+)\|(\d+)\|(\d+)\|(\d+)"\s*\/>/g;
  let m;
  while ((m = re.exec(String(xml))) !== null) {
    const date = m[1];
    const open = Number(m[2]);
    const high = Number(m[3]);
    const low = Number(m[4]);
    const close = Number(m[5]);
    const volume = Number(m[6]);
    if (![open, high, low, close, volume].every(Number.isFinite)) continue;
    out.push({ date, open, high, low, close, volume });
  }
  return out;
}

function computeSmaFromCloses(closes, windowSize) {
  const w = Number(windowSize);
  if (!Number.isFinite(w) || w <= 0) return null;
  if (!Array.isArray(closes) || closes.length < w) return null;
  let sum = 0;
  for (let i = closes.length - w; i < closes.length; i++) {
    const v = Number(closes[i]);
    if (!Number.isFinite(v)) return null;
    sum += v;
  }
  return sum / w;
}

function computeRsiBasicFromCloses(closes, period = 14) {
  const p = Number(period);
  if (!Number.isFinite(p) || p <= 0) return null;
  if (!Array.isArray(closes) || closes.length < p + 1) return null;

  // Use the most recent (p) changes: need (p + 1) closes.
  const slice = closes.slice(closes.length - (p + 1));
  let sumUp = 0;
  let sumDown = 0;
  for (let i = 1; i < slice.length; i++) {
    const prev = Number(slice[i - 1]);
    const cur = Number(slice[i]);
    if (!Number.isFinite(prev) || !Number.isFinite(cur)) return null;
    const diff = cur - prev;
    if (diff > 0) sumUp += diff;
    else if (diff < 0) sumDown += Math.abs(diff);
  }

  const avgU = sumUp / p;
  const avgD = sumDown / p;
  if (avgD === 0 && avgU === 0) return 50;
  if (avgD === 0) return 100;
  if (avgU === 0) return 0;

  const rs = avgU / avgD;
  const rsi = 100 - (100 / (1 + rs));
  return Number.isFinite(rsi) ? rsi : null;
}

function computeMaSignalsFromOhlcItems(items) {
  const list = Array.isArray(items) ? items.slice() : [];
  // 날짜 기준으로 정렬(YYYYMMDD 문자열)
  list.sort((a, b) => String(a?.date ?? '').localeCompare(String(b?.date ?? '')));
  const closes = list.map(it => Number(it?.close)).filter(Number.isFinite);
  if (closes.length === 0) {
    return {
      asOfDate: null,
      close: null,
      ma5: null,
      ma20: null,
      rsi14: null,
      tradeSignal: null,
      crossSignal: null,
      disparity5Pct: null,
      disparitySignal: null,
    };
  }

  const last = list[list.length - 1] || null;
  const close = Number(last?.close);
  const asOfDate = last?.date ? String(last.date) : null;

  const ma5 = computeSmaFromCloses(closes, 5);
  const ma20 = computeSmaFromCloses(closes, 20);
  const rsi14 = computeRsiBasicFromCloses(closes, 14);
  const tradeSignal = (Number.isFinite(ma5) && Number.isFinite(ma20))
    ? (ma5 > ma20 ? '매수' : '매도')
    : null;

  // 골든/데드크로스(이벤트) 판단
  // - 전일: MA5_prev <= MA20_prev && 오늘: MA5 > MA20 => 골든크로스
  // - 전일: MA5_prev >= MA20_prev && 오늘: MA5 < MA20 => 데드크로스
  // (동일값(=)은 경계로 포함)
  let crossSignal = null;
  if (closes.length >= 21) {
    const prevCloses = closes.slice(0, closes.length - 1);
    const ma5Prev = computeSmaFromCloses(prevCloses, 5);
    const ma20Prev = computeSmaFromCloses(prevCloses, 20);
    if ([ma5Prev, ma20Prev, ma5, ma20].every(Number.isFinite)) {
      if (ma5Prev <= ma20Prev && ma5 > ma20) crossSignal = '골든크로스';
      else if (ma5Prev >= ma20Prev && ma5 < ma20) crossSignal = '데드크로스';
    }
  }

  const disparity5Pct = (Number.isFinite(close) && Number.isFinite(ma5) && ma5 !== 0)
    ? (close / ma5) * 100
    : null;
  let disparitySignal = null;
  if (Number.isFinite(disparity5Pct)) {
    if (disparity5Pct >= 103) disparitySignal = '과매수';
    else if (disparity5Pct <= 97) disparitySignal = '과매도';
  }

  return {
    asOfDate,
    close: Number.isFinite(close) ? close : null,
    ma5: Number.isFinite(ma5) ? ma5 : null,
    ma20: Number.isFinite(ma20) ? ma20 : null,
    rsi14: Number.isFinite(rsi14) ? rsi14 : null,
    tradeSignal,
    crossSignal,
    disparity5Pct: Number.isFinite(disparity5Pct) ? disparity5Pct : null,
    disparitySignal,
  };
}

function clampNumber(n, min, max) {
  const v = Number(n);
  if (!Number.isFinite(v)) return null;
  const lo = Number(min);
  const hi = Number(max);
  if (!Number.isFinite(lo) || !Number.isFinite(hi)) return v;
  return Math.min(hi, Math.max(lo, v));
}

function scoreByThresholds(value, thresholds) {
  // thresholds: [{ le: number, score: number }, ...] in ascending le
  const v = Number(value);
  if (!Number.isFinite(v)) return null;
  const list = Array.isArray(thresholds) ? thresholds : [];
  for (const t of list) {
    const le = Number(t?.le);
    const s = Number(t?.score);
    if (!Number.isFinite(le) || !Number.isFinite(s)) continue;
    if (v <= le) return s;
  }
  const last = list[list.length - 1];
  const fallback = Number(last?.fallbackScore);
  return Number.isFinite(fallback) ? fallback : 0;
}

function computeStdDev(values) {
  const arr = Array.isArray(values) ? values.map(Number).filter(Number.isFinite) : [];
  if (arr.length === 0) return null;
  const mean = arr.reduce((a, b) => a + b, 0) / arr.length;
  const varSum = arr.reduce((a, b) => a + Math.pow(b - mean, 2), 0) / arr.length;
  const sd = Math.sqrt(varSum);
  return Number.isFinite(sd) ? sd : null;
}

function computeAtrBasicFromOhlcItems(items, period = 14) {
  const p = Number(period);
  const list = Array.isArray(items) ? items.slice() : [];
  if (!Number.isFinite(p) || p <= 0) return null;
  if (list.length < p + 1) return null;
  list.sort((a, b) => String(a?.date ?? '').localeCompare(String(b?.date ?? '')));
  const slice = list.slice(list.length - (p + 1));

  const trs = [];
  for (let i = 1; i < slice.length; i++) {
    const prevClose = Number(slice[i - 1]?.close);
    const high = Number(slice[i]?.high);
    const low = Number(slice[i]?.low);
    if (![prevClose, high, low].every(Number.isFinite)) return null;
    const tr = Math.max(
      high - low,
      Math.abs(high - prevClose),
      Math.abs(low - prevClose)
    );
    if (!Number.isFinite(tr)) return null;
    trs.push(tr);
  }
  if (trs.length !== p) return null;
  const atr = trs.reduce((a, b) => a + b, 0) / p;
  return Number.isFinite(atr) ? atr : null;
}

function computeBollingerBandwidthPctFromCloses(closes, windowSize = 20, stdevMul = 2) {
  const w = Number(windowSize);
  const k = Number(stdevMul);
  if (!Number.isFinite(w) || w <= 1) return null;
  if (!Number.isFinite(k) || k <= 0) return null;
  const arr = Array.isArray(closes) ? closes.map(Number).filter(Number.isFinite) : [];
  if (arr.length < w) return null;
  const last = arr.slice(arr.length - w);
  const sma = last.reduce((a, b) => a + b, 0) / w;
  const sd = computeStdDev(last);
  if (![sma, sd].every(Number.isFinite) || sma === 0) return null;
  const upper = sma + (k * sd);
  const lower = sma - (k * sd);
  const widthPct = ((upper - lower) / sma) * 100;
  return Number.isFinite(widthPct) ? widthPct : null;
}

function classifySidewaysByScore(score) {
  const s = Number(score);
  if (!Number.isFinite(s)) return { label: null, meaning: null };
  if (s >= 80) return { label: '강한 횡보', meaning: '박스권 확실, 돌파 임박 가능성' };
  if (s >= 60) return { label: '횡보', meaning: '방향성 부재, 관망 구간' };
  if (s >= 40) return { label: '약한 횡보', meaning: '방향성 모호' };
  return { label: '추세', meaning: '상승 또는 하락 추세 중' };
}

function computeSidewaysScoreFromOhlcItems(items, options = {}) {
  const list = Array.isArray(items) ? items.slice() : [];
  list.sort((a, b) => String(a?.date ?? '').localeCompare(String(b?.date ?? '')));
  if (list.length === 0) {
    return {
      asOfDate: null,
      close: null,
      score: null,
      label: null,
      meaning: null,
    };
  }

  const lastBar = list[list.length - 1] || null;
  const close = Number(lastBar?.close);
  const asOfDate = lastBar?.date ? String(lastBar.date) : null;
  if (!Number.isFinite(close) || close <= 0) {
    return { asOfDate, close: null, score: null, label: null, meaning: null };
  }

  const lookback = Math.max(40, Math.min(240, Number(options.lookback ?? 90)));
  const rangeWindow = Math.max(20, Math.min(120, Number(options.rangeWindow ?? 40)));
  const slopeGap = Math.max(5, Math.min(30, Number(options.slopeGap ?? 10)));
  const volumeShort = Math.max(5, Math.min(30, Number(options.volumeShort ?? 10)));
  const volumeLong = Math.max(10, Math.min(90, Number(options.volumeLong ?? 30)));

  const slice = list.slice(Math.max(0, list.length - lookback));
  const closes = slice.map(x => Number(x?.close)).filter(Number.isFinite);
  const highs = slice.map(x => Number(x?.high)).filter(Number.isFinite);
  const lows = slice.map(x => Number(x?.low)).filter(Number.isFinite);
  const volumes = slice.map(x => Number(x?.volume)).filter(Number.isFinite);

  // [1] 가격 범위 분석 (고점/저점 밴드)
  let rangeScore = null;
  if (slice.length >= rangeWindow) {
    const rSlice = slice.slice(slice.length - rangeWindow);
    const maxHigh = Math.max(...rSlice.map(x => Number(x?.high)).filter(Number.isFinite));
    const minLow = Math.min(...rSlice.map(x => Number(x?.low)).filter(Number.isFinite));
    if ([maxHigh, minLow].every(Number.isFinite) && maxHigh > 0 && minLow > 0 && maxHigh >= minLow) {
      const rangePct = ((maxHigh - minLow) / close) * 100;
      rangeScore = scoreByThresholds(rangePct, [
        { le: 6, score: 25 },
        { le: 10, score: 20 },
        { le: 15, score: 13 },
        { le: 22, score: 7 },
        { le: 32, score: 3 },
      ]);
      rangeScore = clampNumber(rangeScore, 0, 25);
    }
  }

  // [2] 이동평균선 기울기 계산 (MA20)
  let slopeScore = null;
  if (closes.length >= 20 + slopeGap) {
    const ma20Now = computeSmaFromCloses(closes, 20);
    const prevCloses = closes.slice(0, closes.length - slopeGap);
    const ma20Prev = computeSmaFromCloses(prevCloses, 20);
    if ([ma20Now, ma20Prev].every(Number.isFinite) && ma20Prev !== 0) {
      const slopePctPerDay = ((ma20Now - ma20Prev) / ma20Prev) * 100 / slopeGap;
      const absSlope = Math.abs(slopePctPerDay);
      slopeScore = scoreByThresholds(absSlope, [
        { le: 0.05, score: 25 },
        { le: 0.10, score: 20 },
        { le: 0.20, score: 13 },
        { le: 0.35, score: 7 },
        { le: 0.60, score: 3 },
      ]);
      slopeScore = clampNumber(slopeScore, 0, 25);
    }
  }

  // [3] 변동성 지표 (ATR, 볼린저밴드폭)
  let volaScore = null;
  const atr = computeAtrBasicFromOhlcItems(slice, 14);
  const atrPct = (Number.isFinite(atr) && close !== 0) ? (atr / close) * 100 : null;
  const atrScore = scoreByThresholds(atrPct, [
    { le: 1.0, score: 25 },
    { le: 1.6, score: 20 },
    { le: 2.4, score: 13 },
    { le: 3.2, score: 7 },
    { le: 4.2, score: 3 },
  ]);
  const bbWidthPct = computeBollingerBandwidthPctFromCloses(closes, 20, 2);
  const bbScore = scoreByThresholds(bbWidthPct, [
    { le: 6, score: 25 },
    { le: 9, score: 20 },
    { le: 13, score: 13 },
    { le: 19, score: 7 },
    { le: 28, score: 3 },
  ]);
  if ([atrScore, bbScore].some(x => Number.isFinite(Number(x)))) {
    const a = Number.isFinite(Number(atrScore)) ? Number(atrScore) : null;
    const b = Number.isFinite(Number(bbScore)) ? Number(bbScore) : null;
    const denom = (a !== null ? 1 : 0) + (b !== null ? 1 : 0);
    const avg = denom > 0 ? ((a ?? 0) + (b ?? 0)) / denom : null;
    volaScore = clampNumber(Math.round(avg), 0, 25);
  }

  // [4] 거래량 패턴 분석
  let volScore = null;
  if (volumes.length >= volumeLong) {
    const vLong = volumes.slice(volumes.length - volumeLong);
    const vShort = volumes.slice(volumes.length - volumeShort);
    const avgLong = vLong.reduce((a, b) => a + b, 0) / vLong.length;
    const avgShort = vShort.reduce((a, b) => a + b, 0) / vShort.length;
    const ratio = (Number.isFinite(avgLong) && avgLong > 0 && Number.isFinite(avgShort)) ? (avgShort / avgLong) : null;
    volScore = scoreByThresholds(ratio, [
      { le: 0.70, score: 25 },
      { le: 0.85, score: 20 },
      { le: 1.00, score: 13 },
      { le: 1.20, score: 7 },
      { le: 1.40, score: 3 },
    ]);
    volScore = clampNumber(volScore, 0, 25);
  }

  // [5] 복합 점수화 → 횡보 판정
  const parts = [rangeScore, slopeScore, volaScore, volScore].map(x => (Number.isFinite(Number(x)) ? Number(x) : null));
  const present = parts.filter(x => x !== null);
  if (present.length === 0) {
    return { asOfDate, close, score: null, label: null, meaning: null };
  }
  // If some components are missing (e.g. too few bars), scale to 100.
  const rawSum = present.reduce((a, b) => a + b, 0);
  const maxSum = present.length * 25;
  const score = clampNumber(Math.round((rawSum / maxSum) * 100), 0, 100);
  const cls = classifySidewaysByScore(score);
  return {
    asOfDate,
    close,
    score,
    label: cls.label,
    meaning: cls.meaning,
  };
}

async function getNaverFchartOhlcCached(ttlMs, { symbol, timeframe, count }) {
  const now = Date.now();
  const cacheKey = stableStringify({ symbol, timeframe, count });
  const existing = naverFchartOhlcCache.get(cacheKey);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const xml = await fetchNaverFchartOhlcXml({ symbol, timeframe, count });
    const items = parseNaverFchartOhlcFromXml(xml);
    return {
      symbol,
      timeframe,
      count: items.length,
      items,
      updatedAt: new Date().toISOString(),
      sourceUrl: `https://fchart.stock.naver.com/sise.nhn?symbol=${encodeURIComponent(symbol)}&timeframe=${encodeURIComponent(timeframe)}&count=${encodeURIComponent(count)}&requestType=0`,
    };
  })();

  naverFchartOhlcCache.set(cacheKey, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    const payload = await inFlight;
    naverFchartOhlcCache.set(cacheKey, { value: payload, expiresAtMs: Date.now() + ttlMs, inFlight: null });
    return payload;
  } finally {
    const latest = naverFchartOhlcCache.get(cacheKey);
    if (latest?.inFlight === inFlight) {
      naverFchartOhlcCache.set(cacheKey, { ...latest, inFlight: null });
    }
  }
}

function parseNaverIndexSnapshotHtml(html, { name, code, sourceUrl }) {
  const $ = cheerio.load(html);
  const valueText = ($('#now_value').first().text() || '').trim();
  const timeText = ($('#time').first().text() || '').trim();
  const flucText = ($('#change_value_and_rate').first().text() || '').replace(/\s+/g, ' ').trim();

  const value = parseSignedNumberFromText(valueText);
  if (!Number.isFinite(value)) return null;

  const quotientClass = ($('#quotient').first().attr('class') || '').toLowerCase();
  const direction = quotientClass.includes('up') ? 'up' : quotientClass.includes('dn') ? 'down' : 'flat';

  // 전일대비 수치는 보통 절대값만 표시되는 경우가 있어, 방향은 quotient class로 결정
  let changeAbs = parseSignedNumberFromText(flucText);
  if (!Number.isFinite(changeAbs)) changeAbs = null;
  const changeRatePct = parsePercentFromText(flucText);

  let change = changeAbs;
  if (typeof changeAbs === 'number') {
    if (direction === 'down') change = -Math.abs(changeAbs);
    else if (direction === 'up') change = Math.abs(changeAbs);
  }

  return {
    name,
    code,
    unit: 'pt',
    time: timeText || null,
    value,
    change,
    changeRatePct,
    direction,
    sourceUrl,
  };
}

function parseKospiFromNaverIndexHtml(html) {
  return parseNaverIndexSnapshotHtml(html, {
    name: '코스피',
    code: 'KOSPI',
    sourceUrl: 'https://finance.naver.com/sise/sise_index.naver?code=KOSPI',
  });
}

function parseKospi200SpotFromNaverIndexHtml(html) {
  return parseNaverIndexSnapshotHtml(html, {
    name: '코스피200',
    code: 'KPI200',
    sourceUrl: 'https://finance.naver.com/sise/sise_index.naver?code=KPI200',
  });
}

// ✅ VKOSPI 파서 추가 (네이버 지수 페이지 구조 동일)
function parseVkospiFromNaverIndexHtml(html) {
  return parseNaverIndexSnapshotHtml(html, {
    name: '한국증시 공포지수(VKOSPI)',
    code: 'KVI200',
    sourceUrl: 'https://finance.naver.com/sise/sise_index.naver?code=KVI200',
  });
}

function parseKospi200NightFuturesFromNaverFutHtml(html) {
  const $ = cheerio.load(html);
  const valueText = ($('#now_value').first().text() || '').trim();
  const timeText = ($('#time').first().text() || '').trim();
  const changeText = ($('#change_value').first().text() || '').replace(/\s+/g, ' ').trim();
  const rateText = ($('#change_rate').first().text() || '').replace(/\s+/g, ' ').trim();

  const value = parseSignedNumberFromText(valueText);
  if (!Number.isFinite(value)) return null;

  let changeAbs = parseSignedNumberFromText(changeText);
  if (!Number.isFinite(changeAbs)) changeAbs = null;

  const isDown = changeText.includes('▼') || changeText.includes('하락');
  const isUp = changeText.includes('▲') || changeText.includes('상승');

  let change = changeAbs;
  if (typeof changeAbs === 'number') {
    if (isDown) change = -Math.abs(changeAbs);
    else if (isUp) change = Math.abs(changeAbs);
  }

  const changeRatePct = parsePercentFromText(rateText);
  const direction = typeof change === 'number' ? (change > 0 ? 'up' : change < 0 ? 'down' : 'flat') : 'flat';

  return {
    name: '코스피200 야간선물',
    code: 'FUT',
    unit: 'pt',
    time: timeText || null,
    value,
    change,
    changeRatePct,
    direction,
    sourceUrl: 'https://finance.naver.com/sise/sise_index.naver?code=FUT',
  };
}

function parseLastPageFromNaverMarketSumHtml(html) {
  const $ = cheerio.load(html);
  const href = ($('td.pgRR a').first().attr('href') || $('a.pgRR').first().attr('href') || '').trim();
  const m = href.match(/(?:\?|&)page=(\d+)/);
  const n = m ? Number(m[1]) : null;
  return Number.isFinite(n) && n > 0 ? n : 1;
}

function parseNaverMarketSumItemsFromHtml(html) {
  const $ = cheerio.load(html);
  const rows = $('table.type_2 tbody tr');
  const items = [];

  rows.each((_, tr) => {
    const $tr = $(tr);
    const tds = $tr.find('td');
    if (!tds || tds.length < 5) return;

    const a = $tr.find('a[href*="code="]').first();
    const name = (a.text() || '').trim();
    const href = (a.attr('href') || '').trim();
    const codeMatch = href.match(/(?:\?|&)code=(\d{4,8})/);
    const code = codeMatch ? String(codeMatch[1]).padStart(6, '0') : null;
    if (!code || !name) return;
    // 네이버 일부 페이지/환경에서 code=000000 같은 placeholder가 섞이는 경우가 있어 차단
    if (code === '000000') return;

    // 컬럼 구조(대략): no, name, price, change, change%, ... volume, ...
    const current = parseNumberWithCommas($(tds.get(2)).text());
    if (!Number.isFinite(current)) return;
    // ✅ 5,000원 이하 종목은 아예 수집하지 않음
    if (current <= LOW_PRICE_CUTOFF_KRW) return;

    const changeCell = $(tds.get(3));
    const changeAbs = parseSignedNumberFromText(changeCell.text());
    let change = Number.isFinite(changeAbs) ? changeAbs : null;

    const dirText = (changeCell.find('span.blind').first().text() || '').trim();
    const isDown = dirText.includes('하락');
    const isUp = dirText.includes('상승');
    if (typeof change === 'number') {
      if (isDown) change = -Math.abs(change);
      else if (isUp) change = Math.abs(change);
    }

    const pct = parsePercentFromText($(tds.get(4)).text());
    if (!Number.isFinite(pct)) return;

    const volume = parseNumberWithCommas($(tds.get(9)).text());

    items.push({
      name,
      code,
      stck_prpr: String(Math.round(current)),
      prdy_vrss: typeof change === 'number' ? String(change) : '',
      prdy_ctrt: String(pct),
      acml_vol: Number.isFinite(volume) ? String(Math.round(volume)) : '',
      _pct: pct,
    });
  });

  return items;
}

async function fetchNaverMarketSumAll(sosok) {
  const firstHtml = await fetchNaverHtml('/sise/sise_market_sum.naver', { sosok, page: 1 });
  const lastPage = parseLastPageFromNaverMarketSumHtml(firstHtml);

  const targetItems = Math.max(
    NAVER_MARKET_SUM_ITEMS_PER_PAGE,
    Math.min(10_000, Number(process.env.NAVER_MARKET_SUM_TARGET_ITEMS ?? NAVER_MARKET_SUM_TARGET_ITEMS_DEFAULT))
  );
  const minPagesForTarget = Math.ceil(targetItems / NAVER_MARKET_SUM_ITEMS_PER_PAGE);

  // lastPage가 과소추정되는 경우를 대비해 “목표 개수”에 필요한 최소 페이지 수만큼은 시도합니다.
  const pages = Math.max(1, Math.min(NAVER_MARKET_SUM_MAX_PAGES, Math.max(lastPage, minPagesForTarget)));

  const all = [];
  const seen = new Set();

  const firstItems = parseNaverMarketSumItemsFromHtml(firstHtml) || [];
  for (const it of firstItems) {
    const code = it?.code ? String(it.code).trim().padStart(6, '0') : null;
    if (!code || !/^[0-9]{6}$/.test(code)) continue;
    if (seen.has(code)) continue;
    seen.add(code);
    all.push(it);
    if (all.length >= targetItems) return all;
  }

  // 일부 페이지가 반복/빈 결과로 들어올 수 있어, “새 종목이 0개”인 페이지가 연속으로 나오면 종료합니다.
  let consecutiveNoNewPages = 0;

  for (let page = 2; page <= pages && all.length < targetItems; page += 1) {
    const html = await fetchNaverHtml('/sise/sise_market_sum.naver', { sosok, page });
    const items = parseNaverMarketSumItemsFromHtml(html) || [];
    if (items.length === 0) {
      consecutiveNoNewPages += 1;
      if (consecutiveNoNewPages >= 2) break;
      continue;
    }

    let newCount = 0;
    for (const it of items) {
      const code = it?.code ? String(it.code).trim().padStart(6, '0') : null;
      if (!code || !/^[0-9]{6}$/.test(code)) continue;
      if (seen.has(code)) continue;
      seen.add(code);
      all.push(it);
      newCount += 1;
      if (all.length >= targetItems) break;
    }

    if (newCount === 0) {
      consecutiveNoNewPages += 1;
      if (consecutiveNoNewPages >= 2) break;
    } else {
      consecutiveNoNewPages = 0;
    }
  }

  return all;
}

async function getRangeStocksCached(ttlMs, { minPct, maxPct, limit, market }) {
  const now = Date.now();
  const cacheKey = stableStringify({ v: 2, minPct, maxPct, limit, market });
  const existing = rangeStocksCacheByKey.get(cacheKey);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    // sosok=0: 코스피, sosok=1: 코스닥
    const safeMarket = market === 'kospi' || market === 'kosdaq' ? market : 'all';
    const wantsKospi = safeMarket === 'all' || safeMarket === 'kospi';
    const wantsKosdaq = safeMarket === 'all' || safeMarket === 'kosdaq';

    const [kospiAll, kosdaqAll] = await Promise.all([
      wantsKospi ? fetchNaverMarketSumAll(0) : Promise.resolve([]),
      wantsKosdaq ? fetchNaverMarketSumAll(1) : Promise.resolve([]),
    ]);

    const merged = [...(kospiAll || []), ...(kosdaqAll || [])];

    const inRange = merged
      .filter(item => {
        if (!Number.isFinite(item?._pct) || item._pct < minPct || item._pct > maxPct) return false;
        // parseNaverMarketSumItemsFromHtml에서 1차 차단하지만, 방어적으로 2차 차단
        const p = parseKrwPrice(item?.stck_prpr);
        return !(Number.isFinite(p) && p <= LOW_PRICE_CUTOFF_KRW);
      });

    const sorted = inRange.sort((a, b) => {
      const av = Number(a?._pct);
      const bv = Number(b?._pct);
      if (!Number.isFinite(av) && !Number.isFinite(bv)) return 0;
      if (!Number.isFinite(av)) return 1;
      if (!Number.isFinite(bv)) return -1;

      // Range-aware ordering to avoid biasing results toward 0% when slicing.
      // - All positive range: show biggest gainers first
      // - All negative range: show biggest decliners first
      // - Cross-zero range: show biggest movers by magnitude
      if (minPct >= 0) return bv - av;
      if (maxPct <= 0) return av - bv;
      return Math.abs(bv) - Math.abs(av);
    });

    const filtered = sorted
      .slice(0, limit)
      .map(({ _pct, ...rest }) => rest);

    const payload = {
      markets: wantsKospi && wantsKosdaq ? ['KOSPI', 'KOSDAQ'] : wantsKospi ? ['KOSPI'] : ['KOSDAQ'],
      market: safeMarket,
      minPct,
      maxPct,
      count: filtered.length,
      items: filtered,
      sourceUrl: 'https://finance.naver.com/sise/sise_market_sum.naver',
      updatedAt: new Date().toISOString(),
    };

    rangeStocksCacheByKey.set(cacheKey, {
      value: payload,
      expiresAtMs: Date.now() + ttlMs,
      inFlight: null,
    });
    return payload;
  })();

  rangeStocksCacheByKey.set(cacheKey, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const latest = rangeStocksCacheByKey.get(cacheKey);
    if (latest?.inFlight === inFlight) {
      rangeStocksCacheByKey.set(cacheKey, { ...latest, inFlight: null });
    }
  }
}

async function getResolveStockUniverseCached(ttlMs) {
  const now = Date.now();
  if (resolveStockUniverseCache.value && now < resolveStockUniverseCache.expiresAtMs) return resolveStockUniverseCache.value;
  if (resolveStockUniverseCache.inFlight) return resolveStockUniverseCache.inFlight;

  const inFlight = (async () => {
    const [kospiAll, kosdaqAll] = await Promise.all([
      fetchNaverMarketSumAll(0),
      fetchNaverMarketSumAll(1),
    ]);

    const merged = [...(kospiAll || []), ...(kosdaqAll || [])]
      .map(it => ({
        code: it?.code ? String(it.code).trim().padStart(6, '0') : null,
        name: it?.name ? String(it.name).trim() : null,
        // range-stocks와 동일한 필드명으로 스냅샷 제공
        stck_prpr: it?.stck_prpr ?? null,
        prdy_vrss: it?.prdy_vrss ?? null,
        prdy_ctrt: it?.prdy_ctrt ?? null,
        acml_vol: it?.acml_vol ?? null,
      }))
      .filter(it => {
        if (!(it.code && /^[0-9]{6}$/.test(it.code) && it.name)) return false;
        if (it.code === '000000') return false;
        const p = parseKrwPrice(it?.stck_prpr);
        // 방어적으로 한 번 더: 5,000원 이하 제외
        if (Number.isFinite(p) && p <= LOW_PRICE_CUTOFF_KRW) return false;
        return true;
      });

    // code 중복 제거(드물지만 방어)
    const byCode = new Map();
    for (const it of merged) {
      if (!byCode.has(it.code)) byCode.set(it.code, it);
    }

    const payload = {
      count: byCode.size,
      items: Array.from(byCode.values()),
      sourceUrl: 'https://finance.naver.com/sise/sise_market_sum.naver',
      updatedAt: new Date().toISOString(),
    };

    resolveStockUniverseCache.value = payload;
    resolveStockUniverseCache.expiresAtMs = Date.now() + ttlMs;
    resolveStockUniverseCache.inFlight = null;
    return payload;
  })();

  resolveStockUniverseCache.inFlight = inFlight;
  try {
    return await inFlight;
  } finally {
    if (resolveStockUniverseCache.inFlight === inFlight) resolveStockUniverseCache.inFlight = null;
  }
}

async function getKospiCached(ttlMs) {
  const now = Date.now();
  if (kospiCache.value && now < kospiCache.expiresAtMs) return kospiCache.value;
  if (kospiCache.inFlight) return kospiCache.inFlight;

  const inFlight = (async () => {
    const html = await fetchNaverHtml('/sise/sise_index.naver', { code: 'KOSPI' });
    const parsed = parseKospiFromNaverIndexHtml(html);
    if (!parsed) throw new Error('네이버 코스피 파싱 실패');

    const payload = {
      ...parsed,
      updatedAt: new Date().toISOString(),
    };
    kospiCache.value = payload;
    kospiCache.expiresAtMs = Date.now() + ttlMs;
    kospiCache.inFlight = null;
    return payload;
  })();

  kospiCache.inFlight = inFlight;
  try {
    return await inFlight;
  } finally {
    if (kospiCache.inFlight === inFlight) kospiCache.inFlight = null;
  }
}

async function getKospi200SpotCached(ttlMs) {
  const now = Date.now();
  if (kospi200SpotCache.value && now < kospi200SpotCache.expiresAtMs) return kospi200SpotCache.value;
  if (kospi200SpotCache.inFlight) return kospi200SpotCache.inFlight;

  const inFlight = (async () => {
    const html = await fetchNaverHtml('/sise/sise_index.naver', { code: 'KPI200' });
    const parsed = parseKospi200SpotFromNaverIndexHtml(html);
    if (!parsed) throw new Error('네이버 코스피200 파싱 실패');

    const payload = {
      ...parsed,
      updatedAt: new Date().toISOString(),
    };
    kospi200SpotCache.value = payload;
    kospi200SpotCache.expiresAtMs = Date.now() + ttlMs;
    kospi200SpotCache.inFlight = null;
    return payload;
  })();

  kospi200SpotCache.inFlight = inFlight;
  try {
    return await inFlight;
  } finally {
    if (kospi200SpotCache.inFlight === inFlight) kospi200SpotCache.inFlight = null;
  }
}

// ✅ VKOSPI 캐시 함수 추가
async function getVkospiCached(ttlMs) {
  const now = Date.now();
  if (vkospiCache.value && now < vkospiCache.expiresAtMs) return vkospiCache.value;
  if (vkospiCache.inFlight) return vkospiCache.inFlight;

  const inFlight = (async () => {
    const html = await fetchNaverHtml('/sise/sise_index.naver', { code: 'KVI200' });
    const parsed = parseVkospiFromNaverIndexHtml(html);
    if (!parsed) throw new Error('네이버 VKOSPI 파싱 실패');

    const payload = { ...parsed, updatedAt: new Date().toISOString() };
    vkospiCache.value = payload;
    vkospiCache.expiresAtMs = Date.now() + ttlMs;
    vkospiCache.inFlight = null;
    return payload;
  })();

  vkospiCache.inFlight = inFlight;
  try {
    return await inFlight;
  } finally {
    if (vkospiCache.inFlight === inFlight) vkospiCache.inFlight = null;
  }
}

async function getFearGreedCached(ttlMs) {
  const now = Date.now();
  if (fearGreedCache.value && now < fearGreedCache.expiresAtMs) return fearGreedCache.value;
  if (fearGreedCache.inFlight) return fearGreedCache.inFlight;

  const inFlight = (async () => {
    const res = await alternativeMeClient.get('/fng/', {
      params: {
        limit: 1,
        format: 'json',
      },
    });

    const item = res?.data?.data?.[0] ?? null;
    const value = Number(item?.value);
    if (!Number.isFinite(value)) {
      const err = new Error('Fear&Greed value 파싱 실패');
      err.code = 'FEAR_GREED_PARSE_FAILED';
      throw err;
    }

    const classification = (item?.value_classification ? String(item.value_classification) : '').trim() || null;
    const timestampSec = Number(item?.timestamp);
    const time = Number.isFinite(timestampSec) ? formatKstYmdHm(timestampSec * 1000) : null;

    const prevValue = Number(fearGreedCache.value?.value);
    const change = Number.isFinite(prevValue) ? (value - prevValue) : null;
    const direction = (typeof change === 'number') ? (change > 0 ? 'up' : change < 0 ? 'down' : 'flat') : 'flat';

    const payload = {
      name: '공포탐욕지수',
      code: 'FNG',
      unit: 'index',
      time,
      value,
      change,
      changeRatePct: null,
      direction,
      classification,
      updatedAt: new Date().toISOString(),
      sourceUrl: 'https://alternative.me/crypto/fear-and-greed-index/',
    };

    fearGreedCache.value = payload;
    fearGreedCache.expiresAtMs = Date.now() + ttlMs;
    fearGreedCache.inFlight = null;
    return payload;
  })();

  fearGreedCache.inFlight = inFlight;
  try {
    return await inFlight;
  } finally {
    if (fearGreedCache.inFlight === inFlight) fearGreedCache.inFlight = null;
  }
}

async function getKospi200NightFuturesCached(ttlMs) {
  const now = Date.now();
  if (kospi200NightFuturesCache.value && now < kospi200NightFuturesCache.expiresAtMs) return kospi200NightFuturesCache.value;
  if (kospi200NightFuturesCache.inFlight) return kospi200NightFuturesCache.inFlight;

  const inFlight = (async () => {
    const html = await fetchNaverHtml('/sise/sise_index.naver', { code: 'FUT' });
    const parsed = parseKospi200NightFuturesFromNaverFutHtml(html);
    if (!parsed) throw new Error('네이버 선물(FUT) 파싱 실패');
    const payload = { ...parsed, updatedAt: new Date().toISOString() };
    kospi200NightFuturesCache.value = payload;
    kospi200NightFuturesCache.expiresAtMs = Date.now() + ttlMs;
    kospi200NightFuturesCache.inFlight = null;
    return payload;
  })();

  kospi200NightFuturesCache.inFlight = inFlight;
  try {
    return await inFlight;
  } finally {
    if (kospi200NightFuturesCache.inFlight === inFlight) kospi200NightFuturesCache.inFlight = null;
  }
}

function parseNumberWithCommas(text) {
  const s = String(text ?? '').replace(/,/g, '').trim();
  if (!s) return null;
  const n = Number(s);
  return Number.isFinite(n) ? n : null;
}

function parseKrwPrice(value) {
  if (value === null || value === undefined) return null;
  if (typeof value === 'number') return Number.isFinite(value) ? value : null;
  const s = String(value).replace(/,/g, '').trim();
  if (!s) return null;
  const n = Number(s);
  return Number.isFinite(n) ? n : null;
}

function clampUniverseTtlMs(ttlMsLike) {
  // Universe는 네이버 전체 종목 리스트를 긁으므로 과도하게 짧은 TTL을 피합니다.
  const def = RESOLVE_STOCK_UNIVERSE_TTL_MS_DEFAULT;
  const ms = Number(ttlMsLike ?? def);
  return Math.max(60_000, Math.min(48 * 60 * 60 * 1000, Number.isFinite(ms) ? ms : def));
}

async function getUniverseAllowedCodeSet(ttlMsLike) {
  const ttlMs = clampUniverseTtlMs(ttlMsLike);
  const universe = await getResolveStockUniverseCached(ttlMs);
  const set = new Set();
  for (const it of (universe?.items || [])) {
    const code = String(it?.code ?? '').trim();
    // 유효하지 않은 코드(빈 문자열 등)를 padStart로 000000으로 만들지 않도록 그대로 검증합니다.
    if (/^[0-9]{6}$/.test(code)) set.add(code);
  }
  return set;
}

async function filterCodesByUniverse(codes, ttlMsLike) {
  const list = Array.isArray(codes) ? codes : [];
  if (list.length === 0) return [];
  const allowed = await getUniverseAllowedCodeSet(ttlMsLike);
  return list.filter(c => allowed.has(String(c).padStart(6, '0')));
}

async function assertUniverseAllowsCodeOrReject(res, code, ttlMsLike) {
  const safeCode = String(code ?? '').trim().padStart(6, '0');
  const allowed = await getUniverseAllowedCodeSet(ttlMsLike);
  if (!allowed.has(safeCode)) {
    // 5,000원 이하(또는 유니버스에 없는) 종목은 수집/표시 대상이 아닙니다.
    res.status(404).json({ error: 'EXCLUDED_BY_PRICE_CUTOFF', code: safeCode });
    return false;
  }
  return true;
}

function getKstYmd() {
  // YYYYMMDD in Asia/Seoul
  try {
    const parts = new Intl.DateTimeFormat('en-CA', {
      timeZone: 'Asia/Seoul',
      year: 'numeric',
      month: '2-digit',
      day: '2-digit',
    }).format(new Date());
    return parts.replace(/-/g, '');
  } catch {
    const d = new Date();
    const y = d.getFullYear();
    const m = String(d.getMonth() + 1).padStart(2, '0');
    const day = String(d.getDate()).padStart(2, '0');
    return `${y}${m}${day}`;
  }
}

function shiftKstYmd(ymd, deltaDays) {
  const s = String(ymd || '').trim();
  const m = s.match(/^(\d{4})(\d{2})(\d{2})$/);
  if (!m) return null;
  const y = Number(m[1]);
  const mo = Number(m[2]);
  const d = Number(m[3]);
  if (!Number.isFinite(y) || !Number.isFinite(mo) || !Number.isFinite(d)) return null;
  try {
    // Interpret as KST midnight then shift days.
    const base = new Date(`${m[1]}-${m[2]}-${m[3]}T00:00:00+09:00`);
    if (!Number.isFinite(base.getTime())) return null;
    base.setDate(base.getDate() + Number(deltaDays || 0));
    const parts = new Intl.DateTimeFormat('en-CA', {
      timeZone: 'Asia/Seoul',
      year: 'numeric',
      month: '2-digit',
      day: '2-digit',
    }).format(base);
    return parts.replace(/-/g, '');
  } catch {
    return null;
  }
}

function pickKisOutputArray(data) {
  if (!data || typeof data !== 'object') return null;
  const candidates = ['output', 'output1', 'output2', 'output3'];
  for (const key of candidates) {
    const v = data[key];
    if (Array.isArray(v)) return v;
  }
  // Fallback: any array-valued property named like output*
  for (const [k, v] of Object.entries(data)) {
    if (k.toLowerCase().startsWith('output') && Array.isArray(v)) return v;
  }
  return null;
}

function pickBestDailyRow(rows) {
  if (!Array.isArray(rows) || rows.length === 0) return null;
  const withDate = rows
    .map(r => {
      const d = String(r?.stck_bsop_date ?? r?.bsop_date ?? r?.bsop_dt ?? r?.trade_date ?? '').trim();
      return { r, d };
    })
    .filter(x => /^[0-9]{8}$/.test(x.d));
  if (withDate.length) {
    withDate.sort((a, b) => (a.d < b.d ? 1 : a.d > b.d ? -1 : 0));
    return withDate[0].r;
  }
  return rows[0];
}

function pickDailyRowExact(rows, targetYmd) {
  if (!Array.isArray(rows) || rows.length === 0) return null;
  const norm = String(targetYmd || '').trim();
  if (!/^[0-9]{8}$/.test(norm)) return null;
  return rows.find(r => {
    const d = String(r?.stck_bsop_date ?? r?.bsop_date ?? r?.bsop_dt ?? r?.trade_date ?? '').trim();
    return d === norm;
  }) || null;
}

async function getForeignFlowDailyByStock(token, code, ymd, marketDiv) {
  const url = 'https://openapi.koreainvestment.com:9443/uapi/domestic-stock/v1/quotations/investor-trade-by-stock-daily';
  const trId = process.env.KIS_TR_ID_FOREIGN_FLOW_DAILY || 'FHPTJ04160001';
  const params = {
    'fid_cond_mrkt_div_code': marketDiv,
    'fid_input_iscd': code,
    // 오늘 데이터가 없을 수 있어 최근 N일 범위로 요청 후 최신 행을 선택합니다.
    // (환경별로 date_1/date_2 의미가 달라질 수 있어, 동작 확인된 형태로 유지)
    'fid_input_date_1': shiftKstYmd(ymd, -14) || ymd,
    'fid_input_date_2': ymd,
    'fid_org_adj_prc': '0',
    'fid_etc_cls_code': '0',
  };

  let response;
  for (let attempt = 0; attempt < 2; attempt += 1) {
    try {
      response = await axios.get(url, {
        headers: {
          'authorization': `Bearer ${token}`,
          'appkey': process.env.KIS_APP_KEY,
          'appsecret': process.env.KIS_APP_SECRET,
          'tr_id': trId,
          'custtype': process.env.KIS_CUSTTYPE || 'P',
        },
        timeout: 10_000,
        params,
      });
      break;
    } catch (e) {
      const msg = String(e?.message || '').toLowerCase();
      const isTransient =
        msg.includes('socket hang up') ||
        msg.includes('econnreset') ||
        msg.includes('stream has been aborted') ||
        msg.includes('aborted') ||
        msg.includes('timeout') ||
        e?.code === 'ECONNRESET' ||
        e?.code === 'ECONNABORTED';
      if (!isTransient || attempt >= 1) throw e;
      await new Promise(r => setTimeout(r, 150));
    }
  }

  // KIS 에러 포맷(예: { rt_cd, msg_cd, msg1, ... }) 처리
  if (response?.data && typeof response.data === 'object') {
    const rt = String(response.data.rt_cd ?? '').trim();
    if (rt && rt !== '0') {
      const err = new Error(String(response.data.msg1 || 'foreign-flow(daily) KIS 오류'));
      err.code = String(response.data.msg_cd || 'KIS_ERROR');
      err.details = response.data;
      throw err;
    }
  }

  const rows = pickKisOutputArray(response.data);
  if (!Array.isArray(rows) || rows.length === 0) {
    const err = new Error('foreign-flow(daily) 응답 형식 오류');
    err.details = response.data;
    throw err;
  }

  // KIS가 요청 날짜(오늘) 행을 제공하지 않는 경우가 있어,
  // 화면 갱신/표시를 위해 가장 최신 행으로 폴백합니다.
  const exact = pickDailyRowExact(rows, ymd);
  const row = exact || pickBestDailyRow(rows) || {};
  if (!row || typeof row !== 'object') {
    const err = new Error('foreign-flow(daily) 행 선택 실패');
    err.details = { ymd, hasExact: !!exact, rowType: typeof row };
    throw err;
  }
  const buyVol = parseNumberWithCommas(row?.frgn_shnu_vol);
  const sellVol = parseNumberWithCommas(row?.frgn_seln_vol);
  const buyAmt = parseNumberWithCommas(row?.frgn_shnu_tr_pbmn);
  const sellAmt = parseNumberWithCommas(row?.frgn_seln_tr_pbmn);
  const netQty = parseNumberWithCommas(row?.frgn_ntby_qty);
  const date = String(row?.stck_bsop_date ?? row?.bsop_date ?? row?.bsop_dt ?? ymd ?? '').trim() || null;

  return {
    code,
    date,
    marketDiv,
    mode: 'daily',
    frgn_buy_vol: Number.isFinite(buyVol) ? String(Math.round(buyVol)) : null,
    frgn_sell_vol: Number.isFinite(sellVol) ? String(Math.round(sellVol)) : null,
    frgn_buy_amt: Number.isFinite(buyAmt) ? String(Math.round(buyAmt)) : null,
    frgn_sell_amt: Number.isFinite(sellAmt) ? String(Math.round(sellAmt)) : null,
    frgn_net_qty: Number.isFinite(netQty) ? String(Math.round(netQty)) : null,
  };
}

async function getForeignNetOnly(token, code, marketDiv, dateYmd) {
  const url = 'https://openapi.koreainvestment.com:9443/uapi/domestic-stock/v1/quotations/inquire-investor';
  const trId = process.env.KIS_TR_ID_INVESTOR_NET || 'FHKST01010900';
  let response;
  for (let attempt = 0; attempt < 2; attempt += 1) {
    try {
      response = await axios.get(url, {
        headers: {
          'authorization': `Bearer ${token}`,
          'appkey': process.env.KIS_APP_KEY,
          'appsecret': process.env.KIS_APP_SECRET,
          'tr_id': trId,
          'custtype': process.env.KIS_CUSTTYPE || 'P',
        },
        timeout: 10_000,
        params: {
          'fid_cond_mrkt_div_code': marketDiv,
          'fid_input_iscd': code,
        },
      });
      break;
    } catch (e) {
      const msg = String(e?.message || '').toLowerCase();
      const isTransient =
        msg.includes('socket hang up') ||
        msg.includes('econnreset') ||
        msg.includes('stream has been aborted') ||
        msg.includes('aborted') ||
        msg.includes('timeout') ||
        e?.code === 'ECONNRESET' ||
        e?.code === 'ECONNABORTED';
      if (!isTransient || attempt >= 1) throw e;
      await new Promise(r => setTimeout(r, 150));
    }
  }

  // KIS 에러 포맷(예: { rt_cd, msg_cd, msg1, ... }) 처리
  if (response?.data && typeof response.data === 'object') {
    const rt = String(response.data.rt_cd ?? '').trim();
    if (rt && rt !== '0') {
      const err = new Error(String(response.data.msg1 || 'foreign-flow(net) KIS 오류'));
      err.code = String(response.data.msg_cd || 'KIS_ERROR');
      err.details = response.data;
      throw err;
    }
  }

  // inquire-investor 응답은 계정/환경에 따라 output*, 배열/객체 형태가 달라질 수 있습니다.
  const data = response?.data;
  const candidates = [];
  const pushCandidate = (v) => {
    if (!v || typeof v !== 'object') return;
    if (Array.isArray(v)) {
      for (const it of v) {
        if (it && typeof it === 'object' && !Array.isArray(it)) candidates.push(it);
      }
      return;
    }
    candidates.push(v);
  };

  if (data && typeof data === 'object') {
    // top-level output candidates
    pushCandidate(data.output);
    pushCandidate(data.output1);
    pushCandidate(data.output2);
    pushCandidate(data.output3);
    // any output* properties
    for (const [k, v] of Object.entries(data)) {
      if (k.toLowerCase().startsWith('output')) pushCandidate(v);
    }
    // one-level nested search
    for (const v of Object.values(data)) {
      if (v && typeof v === 'object') {
        for (const vv of Object.values(v)) pushCandidate(vv);
      }
    }
  }

  const looksLikeInvestorObj = (obj) => {
    if (!obj || typeof obj !== 'object' || Array.isArray(obj)) return false;
    return Object.keys(obj).some(k => {
      const kk = k.toLowerCase();
      return kk.includes('frgn') && kk.includes('ntby');
    });
  };

  const output = candidates.find(looksLikeInvestorObj) || candidates[0] || null;
  if (!output || typeof output !== 'object' || Array.isArray(output)) {
    const err = new Error('foreign-flow(net) 응답 형식 오류');
    err.details = { hasData: !!data, topKeys: data && typeof data === 'object' ? Object.keys(data) : null };
    throw err;
  }

  const netQty = parseNumberWithCommas(output?.frgn_ntby_qty ?? output?.frgn_ntby_vol ?? output?.frgn_net_qty);

  // 일부 응답에는 매수/매도 수량/금액이 함께 들어옵니다.
  const buyVolRaw = parseNumberWithCommas(output?.frgn_shnu_vol ?? output?.frgn_shnu_qty ?? output?.frgn_buy_vol);
  const sellVolRaw = parseNumberWithCommas(output?.frgn_seln_vol ?? output?.frgn_seln_qty ?? output?.frgn_sell_vol);
  const buyAmtRaw = parseNumberWithCommas(output?.frgn_shnu_tr_pbmn ?? output?.frgn_buy_tr_pbmn ?? output?.frgn_buy_amt);
  const sellAmtRaw = parseNumberWithCommas(output?.frgn_seln_tr_pbmn ?? output?.frgn_sell_tr_pbmn ?? output?.frgn_sell_amt);

  const buy = Number.isFinite(buyVolRaw)
    ? buyVolRaw
    : Number.isFinite(netQty)
      ? Math.max(netQty, 0)
      : null;
  const sell = Number.isFinite(sellVolRaw)
    ? sellVolRaw
    : Number.isFinite(netQty)
      ? Math.abs(Math.min(netQty, 0))
      : null;

  return {
    code,
    // net-only 엔드포인트는 날짜 필드가 없지만, 화면 갱신/매칭을 위해 요청 날짜를 태깅합니다.
    date: String(dateYmd || '').trim() || null,
    marketDiv,
    mode: 'net',
    frgn_buy_vol: Number.isFinite(buy) ? String(Math.round(buy)) : null,
    frgn_sell_vol: Number.isFinite(sell) ? String(Math.round(sell)) : null,
    frgn_buy_amt: Number.isFinite(buyAmtRaw) ? String(Math.round(buyAmtRaw)) : null,
    frgn_sell_amt: Number.isFinite(sellAmtRaw) ? String(Math.round(sellAmtRaw)) : null,
    frgn_net_qty: Number.isFinite(netQty) ? String(Math.round(netQty)) : null,
  };
}

async function getForeignFlowCached(token, code, { ymd, marketDiv, ttlMs, debug }) {
  const safeCode = String(code || '').trim().padStart(6, '0');
  if (!/^[0-9]{6}$/.test(safeCode)) {
    const err = new Error('유효하지 않은 code');
    err.code = 'INVALID_CODE';
    throw err;
  }

  const safeMarketDiv = ['J', 'Q'].includes(String(marketDiv || '').trim().toUpperCase())
    ? String(marketDiv).trim().toUpperCase()
    : 'J';

  const dateYmd = String(ymd || '').trim() || getKstYmd();
  const cacheKey = stableStringify({ code: safeCode, dateYmd, marketDiv: safeMarketDiv });
  const now = Date.now();
  const existing = foreignFlowCacheByKey.get(cacheKey);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const cacheTtlMs = Number.isFinite(ttlMs) ? ttlMs : FOREIGN_FLOW_TTL_MS_DEFAULT;
    let netErrorForDebug = null;
    const hasMeaningfulNetSignal = (net) => {
      const buyVol = parseNumberWithCommas(net?.frgn_buy_vol);
      const sellVol = parseNumberWithCommas(net?.frgn_sell_vol);
      const netQty = parseNumberWithCommas(net?.frgn_net_qty);
      const buyAmt = parseNumberWithCommas(net?.frgn_buy_amt);
      const sellAmt = parseNumberWithCommas(net?.frgn_sell_amt);
      return [buyVol, sellVol, netQty, buyAmt, sellAmt].some(n => Number.isFinite(n) && n !== 0);
    };

    // 1) 당일추정: net-only 우선
    try {
      const net = await getForeignNetOnly(token, safeCode, safeMarketDiv, dateYmd);
      if (hasMeaningfulNetSignal(net)) {
        foreignFlowCacheByKey.set(cacheKey, { value: net, expiresAtMs: Date.now() + cacheTtlMs, inFlight: null });
        return net;
      }
    } catch (e) {
      netErrorForDebug = e;

      // net은 시장구분에 따라 실패하는 케이스가 있어, 반대 marketDiv로도 1회 시도합니다.
      const otherDiv = safeMarketDiv === 'J' ? 'Q' : 'J';
      try {
        const net2 = await getForeignNetOnly(token, safeCode, otherDiv, dateYmd);
        if (hasMeaningfulNetSignal(net2)) {
          // 반대 marketDiv가 성공하면 캐시도 교정합니다.
          marketDivCacheByCode.set(safeCode, { value: otherDiv, expiresAtMs: Date.now() + MARKET_DIV_RESOLVE_TTL_MS_DEFAULT, inFlight: null });
          const correctedKey = stableStringify({ code: safeCode, dateYmd, marketDiv: otherDiv });
          foreignFlowCacheByKey.set(correctedKey, { value: net2, expiresAtMs: Date.now() + cacheTtlMs, inFlight: null });
          foreignFlowCacheByKey.set(cacheKey, { value: net2, expiresAtMs: Date.now() + cacheTtlMs, inFlight: null });
          return net2;
        }
      } catch (e2) {
        // invalid marketDiv는 보다 명확한 에러라면 덮어씁니다.
        if (isKisInvalidMarketDivError(e2) || !isKisInvalidMarketDivError(netErrorForDebug)) {
          netErrorForDebug = e2;
        }
      }
    }

    // 2) net 실패 시 daily로 보조
    let dailyErrorForDebug = null;
    try {
      const daily = await getForeignFlowDailyByStock(token, safeCode, dateYmd, safeMarketDiv);
      const payload = debug && netErrorForDebug
        ? {
          ...daily,
          _netError: netErrorForDebug?.message || String(netErrorForDebug),
          _netErrorCode: netErrorForDebug?.code || null,
          _netErrorStatus: netErrorForDebug?.response?.status || null,
          _netErrorMsg1: netErrorForDebug?.response?.data?.msg1 || null,
          _netErrorMsgCd: netErrorForDebug?.response?.data?.msg_cd || null,
        }
        : daily;
      foreignFlowCacheByKey.set(cacheKey, { value: payload, expiresAtMs: Date.now() + cacheTtlMs, inFlight: null });
      return payload;
    } catch (e) {
      dailyErrorForDebug = e;
      if (isKisInvalidMarketDivError(e)) {
        const otherDiv = safeMarketDiv === 'J' ? 'Q' : 'J';
        try {
          const daily2 = await getForeignFlowDailyByStock(token, safeCode, dateYmd, otherDiv);
          marketDivCacheByCode.set(safeCode, { value: otherDiv, expiresAtMs: Date.now() + MARKET_DIV_RESOLVE_TTL_MS_DEFAULT, inFlight: null });
          const correctedKey = stableStringify({ code: safeCode, dateYmd, marketDiv: otherDiv });
          const payload2 = debug && netErrorForDebug
            ? {
              ...daily2,
              _netError: netErrorForDebug?.message || String(netErrorForDebug),
              _netErrorCode: netErrorForDebug?.code || null,
              _netErrorStatus: netErrorForDebug?.response?.status || null,
              _netErrorMsg1: netErrorForDebug?.response?.data?.msg1 || null,
              _netErrorMsgCd: netErrorForDebug?.response?.data?.msg_cd || null,
            }
            : daily2;
          foreignFlowCacheByKey.set(correctedKey, { value: payload2, expiresAtMs: Date.now() + cacheTtlMs, inFlight: null });
          foreignFlowCacheByKey.set(cacheKey, { value: payload2, expiresAtMs: Date.now() + cacheTtlMs, inFlight: null });
          return payload2;
        } catch (e2) {
          dailyErrorForDebug = e2;
        }
      }
    }

    // 3) 최후: net-only를 J로 재시도
    try {
      let net = await getForeignNetOnly(token, safeCode, 'J', dateYmd);
      if (debug) {
        net = {
          ...net,
          _netError: netErrorForDebug?.message || String(netErrorForDebug),
          _netErrorCode: netErrorForDebug?.code || null,
          _netErrorStatus: netErrorForDebug?.response?.status || null,
          _netErrorMsg1: netErrorForDebug?.response?.data?.msg1 || null,
          _netErrorMsgCd: netErrorForDebug?.response?.data?.msg_cd || null,
          _dailyError: dailyErrorForDebug?.message || String(dailyErrorForDebug),
          _dailyErrorCode: dailyErrorForDebug?.code || null,
          _dailyErrorStatus: dailyErrorForDebug?.response?.status || null,
          _dailyErrorMsg1: dailyErrorForDebug?.response?.data?.msg1 || null,
          _dailyErrorMsgCd: dailyErrorForDebug?.response?.data?.msg_cd || null,
        };
      }
      foreignFlowCacheByKey.set(cacheKey, { value: net, expiresAtMs: Date.now() + cacheTtlMs, inFlight: null });
      return net;
    } catch {
      // debug가 꺼져있더라도 원인 파악이 가능하도록 마지막 daily 에러를 던집니다.
      throw dailyErrorForDebug || netErrorForDebug || new Error('foreign-flow 조회 실패');
    }
  })();

  foreignFlowCacheByKey.set(cacheKey, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const latest = foreignFlowCacheByKey.get(cacheKey);
    if (latest?.inFlight === inFlight) {
      foreignFlowCacheByKey.set(cacheKey, { ...latest, inFlight: null });
    }
  }
}

async function getForeignFlowMaybeAuto(token, code, { ymd, marketDiv, ttlMs, debug }) {
  const div = String(marketDiv || '').trim().toUpperCase();
  if (div === 'J' || div === 'Q') {
    return getForeignFlowCached(token, code, { ymd, marketDiv: div, ttlMs, debug });
  }

  const resolved = await getMarketDivCached(token, code, MARKET_DIV_RESOLVE_TTL_MS_DEFAULT);
  return getForeignFlowCached(token, code, { ymd, marketDiv: resolved, ttlMs, debug });
}

function computeIsinCheckDigit(isinBody) {
  const body = String(isinBody || '').trim().toUpperCase();
  if (!/^[A-Z0-9]+$/.test(body)) return null;
  const expanded = body
    .split('')
    .map((ch) => (/\d/.test(ch) ? ch : String(ch.charCodeAt(0) - 55)))
    .join('');
  if (!/^\d+$/.test(expanded)) return null;

  let sum = 0;
  let shouldDouble = true;
  for (let idx = expanded.length - 1; idx >= 0; idx--) {
    let digit = Number(expanded[idx]);
    if (shouldDouble) {
      digit *= 2;
      if (digit > 9) digit = Math.floor(digit / 10) + (digit % 10);
    }
    sum += digit;
    shouldDouble = !shouldDouble;
  }
  return (10 - (sum % 10)) % 10;
}

function buildBestEffortKrxIsuCd(value) {
  const raw = String(value || '').trim().toUpperCase();
  if (/^KR[A-Z0-9]{10}$/.test(raw)) return raw;
  const code = raw.replace(/[^0-9]/g, '').padStart(6, '0').slice(-6);
  if (!/^\d{6}$/.test(code)) return null;
  const body = `KR7${code}00`;
  const checkDigit = computeIsinCheckDigit(body);
  return Number.isInteger(checkDigit) ? `${body}${checkDigit}` : null;
}

async function getKrxShortBalanceCached(code, { ttlMs, startYmd, endYmd } = {}) {
  const safeCode = String(code || '').trim().padStart(6, '0');
  if (!/^\d{6}$/.test(safeCode)) {
    const err = new Error('유효하지 않은 code');
    err.code = 'INVALID_CODE';
    throw err;
  }

  const isuCd = buildBestEffortKrxIsuCd(safeCode);
  if (!isuCd) {
    const err = new Error('KRX isuCd 계산 실패');
    err.code = 'INVALID_ISU_CD';
    throw err;
  }

  const cacheTtlMs = Math.max(60_000, Math.min(24 * 60 * 60 * 1000, Number(ttlMs ?? KRX_SHORT_BALANCE_TTL_MS_DEFAULT)));
  const endDateYmd = String(endYmd || '').trim() || getKstYmd();
  const startDateYmd = String(startYmd || '').trim() || shiftKstYmd(endDateYmd, -31) || endDateYmd;
  const cacheKey = `${isuCd}|${startDateYmd}|${endDateYmd}`;
  const now = Date.now();
  const existing = krxShortBalanceCacheByKey.get(cacheKey);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const form = new URLSearchParams({
      bld: 'dbms/MDC_OUT/STAT/srt/MDCSTAT30001_OUT',
      locale: 'ko_KR',
      isuCd,
      strtDd: startDateYmd,
      endDd: endDateYmd,
      share: '1',
      money: '1',
    }).toString();

    const response = await axios.post('https://data.krx.co.kr/comm/bldAttendant/getJsonData.cmd', form, {
      timeout: 20_000,
      headers: {
        'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8',
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.0.0 Safari/537.36',
        Origin: 'https://data.krx.co.kr',
        Referer: `https://data.krx.co.kr/comm/srt/srtLoader/index.cmd?screenId=MDCSTAT300&isuCd=${encodeURIComponent(safeCode)}`,
        'X-Requested-With': 'XMLHttpRequest',
        Accept: 'application/json, text/javascript, */*; q=0.01',
      },
    });

    const rows = Array.isArray(response?.data?.OutBlock_1) ? response.data.OutBlock_1 : [];
    const pickedRow = rows.find((row) => Number.isFinite(parseNumberWithCommas(row?.STR_CONST_VAL2))) || rows[0] || null;
    const loanBalanceAmount = parseNumberWithCommas(pickedRow?.STR_CONST_VAL2);
    const payload = {
      code: safeCode,
      isuCd,
      date: String(pickedRow?.TRD_DD ?? '').trim() || null,
      loan_balance_amount: Number.isFinite(loanBalanceAmount) ? String(Math.round(loanBalanceAmount)) : null,
      sourceUrl: `https://data.krx.co.kr/comm/srt/srtLoader/index.cmd?screenId=MDCSTAT300&isuCd=${encodeURIComponent(safeCode)}`,
      updatedAt: new Date().toISOString(),
    };

    krxShortBalanceCacheByKey.set(cacheKey, { value: payload, expiresAtMs: Date.now() + cacheTtlMs, inFlight: null });
    return payload;
  })();

  krxShortBalanceCacheByKey.set(cacheKey, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const latest = krxShortBalanceCacheByKey.get(cacheKey);
    if (latest?.inFlight === inFlight) {
      krxShortBalanceCacheByKey.set(cacheKey, { ...latest, inFlight: null });
    }
  }
}

function parseFredGraphCsvLastTwo(csvText) {
  const lines = String(csvText || '').trim().split(/\r?\n/);
  if (lines.length < 2) return null;

  const values = [];
  for (let i = 1; i < lines.length; i++) {
    const line = lines[i].trim();
    if (!line) continue;

    const [date, rawValue] = line.split(',');
    const v = String(rawValue ?? '').trim();
    if (!date || !v || v === '.') continue;

    const value = Number(v);
    if (!Number.isFinite(value)) continue;
    values.push({ date: date.trim(), value });
  }

  if (values.length === 0) return null;
  const last = values[values.length - 1];
  const prev = values.length >= 2 ? values[values.length - 2] : null;
  return { last, prev };
}

function parseFredGraphCsvAll(csvText) {
  const lines = String(csvText || '').trim().split(/\r?\n/);
  if (lines.length < 2) return [];

  const values = [];
  for (let i = 1; i < lines.length; i++) {
    const line = lines[i].trim();
    if (!line) continue;

    const [date, rawValue] = line.split(',');
    const v = String(rawValue ?? '').trim();
    if (!date || !v || v === '.') continue;

    const value = Number(v);
    if (!Number.isFinite(value)) continue;
    values.push({ date: date.trim(), value });
  }

  return values;
}

function formatUtcYmd(dateLike) {
  const d = dateLike instanceof Date ? dateLike : new Date(dateLike);
  if (!Number.isFinite(d.getTime())) return null;
  const y = d.getUTCFullYear();
  const m = String(d.getUTCMonth() + 1).padStart(2, '0');
  const day = String(d.getUTCDate()).padStart(2, '0');
  return `${y}-${m}-${day}`;
}

function parseNyFedEffrAll(json) {
  const rows = json?.refRates;
  if (!Array.isArray(rows) || rows.length === 0) return [];

  const items = [];
  for (const r of rows) {
    const date = String(r?.effectiveDate ?? '').trim();
    if (!date) continue;

    const effr = Number(r?.percentRate);
    const targetFrom = Number(r?.targetRateFrom);
    const targetTo = Number(r?.targetRateTo);

    // "기준금리"에 가장 가까운 값으로 타겟 밴드의 중간값을 사용.
    // (밴드가 없으면 EFFR 자체를 사용)
    let value = NaN;
    if (Number.isFinite(targetFrom) && Number.isFinite(targetTo)) {
      value = (targetFrom + targetTo) / 2;
    } else if (Number.isFinite(effr)) {
      value = effr;
    }

    if (!Number.isFinite(value)) continue;
    items.push({
      date,
      value,
      effr: Number.isFinite(effr) ? effr : null,
      targetFrom: Number.isFinite(targetFrom) ? targetFrom : null,
      targetTo: Number.isFinite(targetTo) ? targetTo : null,
    });
  }

  items.sort((a, b) => String(a.date).localeCompare(String(b.date)));
  return items;
}

async function getUs10ySeriesCached(ttlMs, { days } = {}) {
  const d = Math.max(30, Math.min(3650, Number(days ?? 365)));
  const cacheKey = stableStringify({ days: d });
  const now = Date.now();
  const existing = us10ySeriesCacheByKey.get(cacheKey);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const url = 'https://fred.stlouisfed.org/graph/fredgraph.csv?id=DGS10';
    const response = await axios.get(url, { timeout: 10_000, responseType: 'text' });
    const all = parseFredGraphCsvAll(response.data);
    if (!Array.isArray(all) || all.length === 0) throw new Error('FRED DGS10 파싱 실패');

    const lastDateStr = all[all.length - 1]?.date;
    const lastTs = Date.parse(String(lastDateStr || ''));
    const endTs = Number.isFinite(lastTs) ? lastTs : Date.now();
    const cutoffTs = endTs - d * 24 * 60 * 60 * 1000;
    const items = all.filter((p) => {
      const ts = Date.parse(String(p?.date || ''));
      if (!Number.isFinite(ts)) return false;
      return ts >= cutoffTs && ts <= endTs;
    });

    return {
      series: 'DGS10',
      name: '미국 10년물 국채 금리',
      unit: '%',
      days: d,
      count: items.length,
      items,
      updatedAt: new Date().toISOString(),
      source: 'fred',
      sourceUrl: 'https://fred.stlouisfed.org/series/DGS10',
      csvUrl: url,
    };
  })();

  us10ySeriesCacheByKey.set(cacheKey, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    const payload = await inFlight;
    us10ySeriesCacheByKey.set(cacheKey, { value: payload, expiresAtMs: Date.now() + ttlMs, inFlight: null });
    return payload;
  } finally {
    const latest = us10ySeriesCacheByKey.get(cacheKey);
    if (latest?.inFlight === inFlight) us10ySeriesCacheByKey.set(cacheKey, { ...latest, inFlight: null });
  }
}

async function getFedFundsSeriesCached(ttlMs, { days } = {}) {
  const d = Math.max(30, Math.min(3650, Number(days ?? 365)));
  const cacheKey = stableStringify({ days: d });
  const now = Date.now();
  const existing = fedFundsSeriesCacheByKey.get(cacheKey);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    // FRED CSV가 현재 환경에서 타임아웃이 잦아, NY Fed Markets API(EFFR)를 사용합니다.
    // https://markets.newyorkfed.org/api/rates/unsecured/effr/search.json?startDate=YYYY-MM-DD&endDate=YYYY-MM-DD
    const reqDays = d + 30; // 주말/휴일 결측을 감안한 여유
    const endDate = formatUtcYmd(new Date());
    const startDate = formatUtcYmd(new Date(Date.now() - reqDays * 24 * 60 * 60 * 1000));
    if (!startDate || !endDate) throw new Error('날짜 범위 계산 실패');

    const url = `https://markets.newyorkfed.org/api/rates/unsecured/effr/search.json?startDate=${startDate}&endDate=${endDate}`;
    const response = await axios.get(url, { timeout: 10_000 });
    const all = parseNyFedEffrAll(response.data);
    if (!Array.isArray(all) || all.length === 0) throw new Error('NY Fed EFFR 파싱 실패');

    const lastDateStr = all[all.length - 1]?.date;
    const lastTs = Date.parse(String(lastDateStr || ''));
    const endTs = Number.isFinite(lastTs) ? lastTs : Date.now();
    const cutoffTs = endTs - d * 24 * 60 * 60 * 1000;
    const items = all.filter((p) => {
      const ts = Date.parse(String(p?.date || ''));
      if (!Number.isFinite(ts)) return false;
      return ts >= cutoffTs && ts <= endTs;
    });

    return {
      series: 'EFFR',
      name: '미국 기준금리',
      unit: '%',
      days: d,
      count: items.length,
      items,
      updatedAt: new Date().toISOString(),
      source: 'nyfed',
      sourceUrl: 'https://markets.newyorkfed.org',
      jsonUrl: url,
    };
  })();

  fedFundsSeriesCacheByKey.set(cacheKey, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    const payload = await inFlight;
    fedFundsSeriesCacheByKey.set(cacheKey, { value: payload, expiresAtMs: Date.now() + ttlMs, inFlight: null });
    return payload;
  } finally {
    const latest = fedFundsSeriesCacheByKey.get(cacheKey);
    if (latest?.inFlight === inFlight) fedFundsSeriesCacheByKey.set(cacheKey, { ...latest, inFlight: null });
  }
}

async function getVixSeriesCached(ttlMs, { days } = {}) {
  const d = Math.max(30, Math.min(3650, Number(days ?? 1095)));
  const cacheKey = stableStringify({ days: d });
  const now = Date.now();
  const existing = vixSeriesCacheByKey.get(cacheKey);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const url = 'https://fred.stlouisfed.org/graph/fredgraph.csv?id=VIXCLS';
    const response = await axios.get(url, { timeout: 12_000, responseType: 'text' });
    const all = parseFredGraphCsvAll(response.data);
    if (!Array.isArray(all) || all.length === 0) throw new Error('FRED VIXCLS 파싱 실패');

    const lastDateStr = all[all.length - 1]?.date;
    const lastTs = Date.parse(String(lastDateStr || ''));
    const endTs = Number.isFinite(lastTs) ? lastTs : Date.now();
    const cutoffTs = endTs - d * 24 * 60 * 60 * 1000;
    const items = all.filter((p) => {
      const ts = Date.parse(String(p?.date || ''));
      if (!Number.isFinite(ts)) return false;
      return ts >= cutoffTs && ts <= endTs;
    });

    return {
      series: 'VIXCLS',
      name: '빅스지수(VIX)',
      unit: 'pt',
      days: d,
      count: items.length,
      items,
      updatedAt: new Date().toISOString(),
      source: 'fred',
      sourceUrl: 'https://fred.stlouisfed.org/series/VIXCLS',
      csvUrl: url,
    };
  })();

  vixSeriesCacheByKey.set(cacheKey, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    const payload = await inFlight;
    vixSeriesCacheByKey.set(cacheKey, { value: payload, expiresAtMs: Date.now() + ttlMs, inFlight: null });
    return payload;
  } finally {
    const latest = vixSeriesCacheByKey.get(cacheKey);
    if (latest?.inFlight === inFlight) vixSeriesCacheByKey.set(cacheKey, { ...latest, inFlight: null });
  }
}

function parseEiaSeriesLastTwo(seriesJson) {
  // Legacy EIA series endpoint format:
  // { series: [{ data: [["YYYYMMDD", value], ...] }] }
  const data = seriesJson?.series?.[0]?.data;
  if (!Array.isArray(data) || data.length < 2) return null;

  const toIso = (yyyymmdd) => {
    const m = String(yyyymmdd ?? '').trim().match(/^(\d{4})(\d{2})(\d{2})$/);
    if (!m) return null;
    return `${m[1]}-${m[2]}-${m[3]}`;
  };

  const pick = (row) => {
    if (!Array.isArray(row) || row.length < 2) return null;
    const date = toIso(row[0]);
    const value = Number(row[1]);
    if (!date || !Number.isFinite(value)) return null;
    return { date, value };
  };

  // EIA typically provides most-recent first.
  const last = pick(data[0]);
  const prev = pick(data[1]);
  if (!last) return null;
  return { last, prev };
}

function toIsoDateFromUnixSeconds(sec) {
  const n = Number(sec);
  if (!Number.isFinite(n)) return null;
  try {
    return new Date(n * 1000).toISOString().slice(0, 10);
  } catch {
    return null;
  }
}

function parseYahooChartDailyPrevClosePayload(json, { name, unit, sourceUrl }) {
  const result = json?.chart?.result?.[0];
  const timestamps = result?.timestamp;
  const closes = result?.indicators?.quote?.[0]?.close;
  if (!Array.isArray(timestamps) || !Array.isArray(closes)) return null;

  const points = [];
  const n = Math.min(timestamps.length, closes.length);
  for (let i = 0; i < n; i++) {
    const close = closes[i];
    if (typeof close !== 'number' || !Number.isFinite(close)) continue;
    const date = toIsoDateFromUnixSeconds(timestamps[i]);
    if (!date) continue;
    points.push({ date, value: close });
  }
  if (points.length < 3) return null;

  // We want "전일(어제)" 기준: use previous trading day close.
  const last = points[points.length - 1];
  const prev = points[points.length - 2];
  const prev2 = points[points.length - 3];

  const change = prev.value - prev2.value;
  const changeRatePct = prev2.value !== 0 ? (change / prev2.value) * 100 : null;
  const direction = change > 0 ? 'up' : change < 0 ? 'down' : 'flat';

  return {
    series: 'CL=F',
    name: name || 'WTI 오일(선물)',
    unit: unit || '$/bbl',
    date: prev.date,
    value: prev.value,
    previousDate: prev2.date,
    previousValue: prev2.value,
    change,
    changeRatePct,
    direction,
    source: 'yahoo',
    sourceUrl: sourceUrl || 'https://finance.yahoo.com/quote/CL%3DF',
    upstreamLastDate: last?.date ?? null,
    updatedAt: new Date().toISOString(),
  };
}

async function getUs10yCached(ttlMs) {
  const now = Date.now();
  if (us10yCache.value && now < us10yCache.expiresAtMs) return us10yCache.value;
  if (us10yCache.inFlight) return us10yCache.inFlight;

  const inFlight = (async () => {
    // 1) Prefer Yahoo (near real-time, intraday)
    // 2) Fallback to FRED (daily) if Yahoo fails (429/parse/etc)
    let payload;
    try {
      payload = await fetchUs10yFromYahoo({ timeoutMs: 10_000 });
    } catch {
      payload = await fetchUs10yFromFred({ timeoutMs: 6_000 });
    }

    us10yCache.value = payload;
    us10yCache.expiresAtMs = Date.now() + ttlMs;
    us10yCache.inFlight = null;
    return payload;
  })();

  us10yCache.inFlight = inFlight;
  try {
    return await inFlight;
  } finally {
    if (us10yCache.inFlight === inFlight) us10yCache.inFlight = null;
  }
}

async function getOilWtiCached(ttlMs) {
  const now = Date.now();
  if (oilWtiCache.value && now < oilWtiCache.expiresAtMs) return oilWtiCache.value;
  if (oilWtiCache.inFlight) return oilWtiCache.inFlight;

  const inFlight = (async () => {
    // 1) Prefer intraday WTI futures quote (CL=F) so the number updates during market hours.
    try {
      const q = await getYahooFuturesQuote('CL=F');
      const payload = {
        series: 'CL=F',
        name: '오일(WTI)',
        unit: '$/bbl',
        date: q.isoDate ?? null,
        time: q.time ?? null,
        value: q.value,
        previousValue: q.previousClose ?? null,
        change: q.change,
        changeRatePct: q.changeRatePct,
        direction: q.direction,
        source: 'yahoo',
        sourceUrl: q.sourceUrl,
        updatedAt: new Date().toISOString(),
      };

      oilWtiCache.value = payload;
      oilWtiCache.expiresAtMs = Date.now() + ttlMs;
      oilWtiCache.inFlight = null;
      return payload;
    } catch {
      // fall through
    }

    // 1) Prefer spot WTI when an API key is available (EIA PET.RWTC.D).
    //    This is the cleanest way to satisfy "현물 + 전일".
    const eiaKey = String(process.env.EIA_API_KEY ?? '').trim();
    if (eiaKey) {
      try {
        const url = `https://api.eia.gov/series/?api_key=${encodeURIComponent(eiaKey)}&series_id=PET.RWTC.D`;
        const response = await axios.get(url, { timeout: 10_000, responseType: 'json' });
        const parsed = parseEiaSeriesLastTwo(response.data);
        if (parsed?.last) {
          const change = parsed.prev ? parsed.last.value - parsed.prev.value : null;
          const changeRatePct = (parsed.prev && typeof change === 'number' && parsed.prev.value !== 0)
            ? (change / parsed.prev.value) * 100
            : null;
          const direction = change === null ? 'flat' : change > 0 ? 'up' : change < 0 ? 'down' : 'flat';

          const payload = {
            series: 'PET.RWTC.D',
            name: '오일(WTI)',
            unit: '$/bbl',
            date: parsed.last.date,
            value: parsed.last.value,
            previousDate: parsed.prev?.date ?? null,
            previousValue: parsed.prev?.value ?? null,
            change,
            changeRatePct,
            direction,
            source: 'eia',
            sourceUrl: 'https://www.eia.gov/dnav/pet/hist/RWTCd.htm',
            updatedAt: new Date().toISOString(),
          };

          oilWtiCache.value = payload;
          oilWtiCache.expiresAtMs = Date.now() + ttlMs;
          oilWtiCache.inFlight = null;
          return payload;
        }
      } catch {
        // fall through
      }
    }

    // 2) Fallback that best matches "전일 기준": Yahoo Finance (CL=F) 일봉 종가.
    //    (EIA 키가 없거나 실패하는 경우에도 전일 기준을 맞추기 위한 대체 소스)
    try {
      const url = 'https://query1.finance.yahoo.com/v8/finance/chart/CL=F?range=15d&interval=1d';
      const response = await axios.get(url, {
        timeout: 10_000,
        responseType: 'json',
        headers: {
          'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
          'Accept-Language': 'ko-KR,ko;q=0.9,en;q=0.8',
        },
      });
      const payload = parseYahooChartDailyPrevClosePayload(response.data, {
        name: '오일(WTI)',
        unit: '$/bbl',
        sourceUrl: 'https://finance.yahoo.com/quote/CL%3DF',
      });
      if (payload) {
        oilWtiCache.value = payload;
        oilWtiCache.expiresAtMs = Date.now() + ttlMs;
        oilWtiCache.inFlight = null;
        return payload;
      }
    } catch {
      // fall through to FRED
    }

    // 3) Last resort: FRED graph CSV (spot WTI). API 키 없이 접근 가능합니다.
    // DCOILWTICO: WTI Crude Oil Prices (Cushing, Oklahoma)
    const url = 'https://fred.stlouisfed.org/graph/fredgraph.csv?id=DCOILWTICO';
    const response = await axios.get(url, { timeout: 10_000, responseType: 'text' });
    const parsed = parseFredGraphCsvLastTwo(response.data);
    if (!parsed?.last) {
      throw new Error('FRED DCOILWTICO 파싱 실패');
    }

    const change = parsed.prev ? parsed.last.value - parsed.prev.value : null;
    const changeRatePct = (parsed.prev && typeof change === 'number' && parsed.prev.value !== 0)
      ? (change / parsed.prev.value) * 100
      : null;
    const direction = change === null ? 'flat' : change > 0 ? 'up' : change < 0 ? 'down' : 'flat';

    const payload = {
      series: 'DCOILWTICO',
      name: '오일(WTI)',
      unit: '$/bbl',
      date: parsed.last.date,
      value: parsed.last.value,
      previousDate: parsed.prev?.date ?? null,
      previousValue: parsed.prev?.value ?? null,
      change,
      changeRatePct,
      direction,
      source: 'fred',
      sourceUrl: 'https://fred.stlouisfed.org/series/DCOILWTICO',
      updatedAt: new Date().toISOString(),
    };

    oilWtiCache.value = payload;
    oilWtiCache.expiresAtMs = Date.now() + ttlMs;
    oilWtiCache.inFlight = null;
    return payload;
  })();

  oilWtiCache.inFlight = inFlight;
  try {
    return await inFlight;
  } finally {
    if (oilWtiCache.inFlight === inFlight) oilWtiCache.inFlight = null;
  }
}

async function fetchUsCpiFromFred({ timeoutMs, year, lastN } = {}) {
  const yearStr = year === undefined || year === null ? '' : String(year).trim();
  const y = yearStr ? Number(yearStr) : NaN;
  const targetYear = Number.isFinite(y) ? Math.max(1940, Math.min(2100, Math.floor(y))) : null;
  const nRaw = Number(lastN);
  const takeN = Number.isFinite(nRaw) ? Math.max(3, Math.min(36, Math.floor(nRaw))) : 12;

  // FRED graph CSV는 API 키 없이도 접근 가능합니다.
  const url = 'https://fred.stlouisfed.org/graph/fredgraph.csv?id=CPIAUCSL';
  const response = await axios.get(url, { timeout: Number(timeoutMs ?? 8_000), responseType: 'text' });
  const all = parseFredGraphCsvAll(response.data);
  if (!Array.isArray(all) || all.length === 0) {
    throw new Error('FRED CPIAUCSL 파싱 실패');
  }

  const todayIso = new Date().toISOString().slice(0, 10);
  const uptoToday = all
    .filter((p) => typeof p?.date === 'string' && p.date <= todayIso)
    .sort((a, b) => String(a.date).localeCompare(String(b.date)));

  // Build YoY(%): (thisMonth / sameMonthLastYear - 1) * 100
  const yoyAll = [];
  for (let i = 12; i < uptoToday.length; i++) {
    const cur = uptoToday[i];
    const prev = uptoToday[i - 12];
    const curV = Number(cur?.value);
    const prevV = Number(prev?.value);
    if (!cur?.date) continue;
    if (!Number.isFinite(curV) || !Number.isFinite(prevV) || prevV === 0) continue;
    yoyAll.push({ date: cur.date, value: ((curV / prevV) - 1) * 100 });
  }

  let items;
  let mode;
  if (targetYear) {
    const startRequested = `${targetYear}-01-01`;
    items = yoyAll.filter((p) => p.date >= startRequested);
    mode = { type: 'year', year: targetYear, startRequested, endRequested: todayIso };
    if (items.length === 0) {
      throw new Error('CPI YoY 데이터(연초~현재) 없음');
    }
  } else {
    items = yoyAll.slice(-takeN);
    mode = { type: 'lastN', lastN: takeN, endRequested: todayIso };
    if (items.length === 0) {
      throw new Error('CPI YoY 데이터(최근 1년) 없음');
    }
  }

  const start = items[0]?.date ?? null;
  const end = items[items.length - 1]?.date ?? null;

  return {
    series: 'CPIAUCSL',
    name: '미국 CPI (YoY)',
    unit: '%',
    metric: 'yoy',
    start,
    end,
    mode,
    items,
    source: 'fred',
    sourceUrl: 'https://fred.stlouisfed.org/series/CPIAUCSL',
    updatedAt: new Date().toISOString(),
  };
}

async function getUsCpiCached(ttlMs, { year, lastN } = {}) {
  const now = Date.now();
  const yearStr = year === undefined || year === null ? '' : String(year).trim();
  const y = yearStr ? Number(yearStr) : NaN;
  const targetYear = Number.isFinite(y) ? Math.max(1940, Math.min(2100, Math.floor(y))) : null;
  const nRaw = Number(lastN);
  const takeN = Number.isFinite(nRaw) ? Math.max(3, Math.min(36, Math.floor(nRaw))) : 12;

  const cacheKey = targetYear ? `year:${targetYear}` : `lastN:${takeN}`;
  const existing = usCpiCacheByKey.get(cacheKey);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const payload = await fetchUsCpiFromFred({ timeoutMs: 8_000, year: targetYear, lastN: takeN });
    usCpiCacheByKey.set(cacheKey, { value: payload, expiresAtMs: Date.now() + ttlMs, inFlight: null });
    return payload;
  })();

  usCpiCacheByKey.set(cacheKey, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const latest = usCpiCacheByKey.get(cacheKey);
    if (latest?.inFlight === inFlight) usCpiCacheByKey.set(cacheKey, { ...latest, inFlight: null });
  }
}

function inferIsoDateFromMmDd(mmdd, now = new Date()) {
  const m = String(mmdd || '').trim().match(/^(\d{1,2})\/(\d{1,2})$/);
  if (!m) return null;

  let year = now.getFullYear();
  const month = Number(m[1]);
  const day = Number(m[2]);
  if (!Number.isFinite(month) || !Number.isFinite(day)) return null;

  const todayUtc = new Date(Date.UTC(now.getFullYear(), now.getMonth(), now.getDate()));
  const candidateUtc = new Date(Date.UTC(year, month - 1, day));
  if (candidateUtc > todayUtc) year -= 1;

  return `${year}-${String(month).padStart(2, '0')}-${String(day).padStart(2, '0')}`;
}

async function fetchKofiaIndexHtml() {
  const response = await kofiaClient.get('/index.jsp', { responseType: 'arraybuffer' });
  return decodeNaverHtml(response.data);
}

function parseInvestorDepositFromKofiaIndexHtml(html) {
  const $ = cheerio.load(html);
  const anchor = $("a[onclick*='OS0021']").first();
  if (!anchor.length) return null;

  const li = anchor.closest('li');
  const scope = li.length ? li : anchor.parent();

  const name = (scope.find('dt.chart-name a').first().text() || scope.find('dt.chart-name').first().text() || '투자자예탁금').trim();
  const unit = (scope.find('span.dan').first().text() || '').trim();
  const mmdd = (scope.find('span.date').first().text() || '').trim();
  const valueText = (scope.find('span.num1').first().text() || '').trim();
  const value = parseNumberWithCommas(valueText);
  if (!Number.isFinite(value)) return null;

  let multiplier = 1;
  if (unit === '백만원') multiplier = 1_000_000;
  else if (unit === '억원') multiplier = 100_000_000;
  else if (unit === '천만원') multiplier = 10_000_000;
  else if (unit === '조원') multiplier = 1_000_000_000_000;

  const valueKrw = value * multiplier;
  const isoDate = inferIsoDateFromMmDd(mmdd);

  return {
    name: name || '투자자예탁금',
    unit: unit || '백만원',
    mmdd: mmdd || null,
    date: isoDate,
    value,
    valueKrw,
    sourceUrl: 'https://freesis.kofia.or.kr/index.jsp',
  };
}

async function getMarketDepositCached(ttlMs) {
  const now = Date.now();
  if (marketDepositCache.value && now < marketDepositCache.expiresAtMs) return marketDepositCache.value;
  if (marketDepositCache.inFlight) return marketDepositCache.inFlight;

  const inFlight = (async () => {
    const html = await fetchKofiaIndexHtml();
    const parsed = parseInvestorDepositFromKofiaIndexHtml(html);
    if (!parsed) {
      throw new Error('KOFIA 투자자예탁금 파싱 실패');
    }

    const valueTrillionWon = parsed.valueKrw / 1_000_000_000_000;
    const valueTrillionWonRounded = Math.round(valueTrillionWon * 10) / 10;

    const payload = {
      ...parsed,
      valueTrillionWon,
      valueTrillionWonRounded,
      display: `${valueTrillionWonRounded.toLocaleString('ko-KR')}조원`,
      updatedAt: new Date().toISOString(),
    };

    marketDepositCache.value = payload;
    marketDepositCache.expiresAtMs = Date.now() + ttlMs;
    marketDepositCache.inFlight = null;
    return payload;
  })();

  marketDepositCache.inFlight = inFlight;
  try {
    return await inFlight;
  } finally {
    if (marketDepositCache.inFlight === inFlight) marketDepositCache.inFlight = null;
  }
}

async function mapWithConcurrency(items, concurrency, mapper) {
  const results = new Array(items.length);
  let nextIndex = 0;

  async function worker() {
    while (true) {
      const i = nextIndex++;
      if (i >= items.length) return;
      results[i] = await mapper(items[i], i);
    }
  }

  const workers = Array.from({ length: Math.max(1, concurrency) }, () => worker());
  await Promise.all(workers);
  return results;
}

async function inquirePriceOutput(token, code, marketDiv) {
  const url = 'https://openapi.koreainvestment.com:9443/uapi/domestic-stock/v1/quotations/inquire-price';
  const response = await axios.get(url, {
    headers: {
      'authorization': `Bearer ${token}`,
      'appkey': process.env.KIS_APP_KEY,
      'appsecret': process.env.KIS_APP_SECRET,
      'tr_id': 'FHKST01010100',
    },
    timeout: 10_000,
    params: {
      'fid_cond_mrkt_div_code': marketDiv,
      'fid_input_iscd': code
    }
  });
  if (!response.data || !response.data.output) {
    const err = new Error('inquire-price 응답 형식 오류');
    err.details = response.data;
    throw err;
  }
  return response.data.output;
}

async function inquirePriceOutputWithFallback(token, code) {
  try {
    return await inquirePriceOutput(token, code, 'J');
  } catch (e) {
    // 일부 종목/환경에서 market div code가 다를 수 있어 보조 시도
    try {
      return await inquirePriceOutput(token, code, 'Q');
    } catch {
      throw e;
    }
  }
}

async function resolveMarketDivByInquirePrice(token, code) {
  const safeCode = String(code || '').trim().padStart(6, '0');
  if (!/^[0-9]{6}$/.test(safeCode)) {
    const err = new Error('유효하지 않은 code');
    err.code = 'INVALID_CODE';
    throw err;
  }

  // inquire-price는 marketDiv가 틀려도 응답을 내주는 경우가 있어,
  // 성공/실패로 판별하지 않고 응답의 대표 시장명으로 판별합니다.
  const output = await inquirePriceOutputWithFallback(token, safeCode);
  const reprRaw = String(output?.rprs_mrkt_kor_name ?? '').trim();
  const reprUpper = reprRaw.toUpperCase();

  // 예) KOSPI200, KOSPI, KSQ150, 코스피, 코스닥 등
  if (reprUpper.includes('KSQ') || reprUpper.includes('KOSDAQ') || reprRaw.includes('코스닥')) return 'Q';
  if (reprUpper.includes('KOSPI') || reprRaw.includes('코스피')) return 'J';

  // fallback: 여전히 판별 불가하면 기존 방식으로 보조 시도
  try {
    await inquirePriceOutput(token, safeCode, 'J');
    return 'J';
  } catch (e) {
    try {
      await inquirePriceOutput(token, safeCode, 'Q');
      return 'Q';
    } catch {
      throw e;
    }
  }
}

function isKisInvalidMarketDivError(e) {
  const code = String(e?.code ?? '').trim();
  if (code !== 'OPSQ2001') return false;
  const msg = String(e?.message ?? '').toUpperCase();
  const msg1 = String(e?.response?.data?.msg1 ?? e?.details?.msg1 ?? '').toUpperCase();
  const combined = `${msg} ${msg1}`;
  return combined.includes('FID_COND_MRKT_DIV_CODE') || combined.includes('MRKT_DIV');
}

async function getMarketDivCached(token, code, ttlMs) {
  const safeCode = String(code || '').trim().padStart(6, '0');
  if (!/^[0-9]{6}$/.test(safeCode)) {
    const err = new Error('유효하지 않은 code');
    err.code = 'INVALID_CODE';
    throw err;
  }

  const now = Date.now();
  const existing = marketDivCacheByCode.get(safeCode);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const div = await resolveMarketDivByInquirePrice(token, safeCode);
    marketDivCacheByCode.set(safeCode, { value: div, expiresAtMs: Date.now() + ttlMs, inFlight: null });
    return div;
  })();

  marketDivCacheByCode.set(safeCode, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const latest = marketDivCacheByCode.get(safeCode);
    if (latest?.inFlight === inFlight) {
      marketDivCacheByCode.set(safeCode, { ...latest, inFlight: null });
    }
  }
}

async function getInquirePriceCached(token, code, ttlMs) {
  const now = Date.now();
  const existing = priceCache.get(code);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const output = await inquirePriceOutputWithFallback(token, code);
    priceCache.set(code, {
      value: output,
      expiresAtMs: Date.now() + ttlMs,
      inFlight: null,
    });
    return output;
  })();

  priceCache.set(code, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const entry = priceCache.get(code);
    if (entry?.inFlight === inFlight) {
      priceCache.set(code, { ...entry, inFlight: null });
    }
  }
}

function normalizeBrokerName(name) {
  return String(name || '').replace(/[\s\u00A0]+/g, '').trim();
}

function parseBooleanParam(value, defaultValue) {
  if (value === undefined || value === null || value === '') return defaultValue;
  if (typeof value === 'boolean') return value;
  const s = String(value).trim().toLowerCase();
  if (s === '1' || s === 'true' || s === 'yes' || s === 'y') return true;
  if (s === '0' || s === 'false' || s === 'no' || s === 'n') return false;
  return defaultValue;
}

function parseNaverNidFromHref(href) {
  if (!href) return null;
  const m = String(href).match(/\bnid=(\d+)/i);
  return m ? m[1] : null;
}

function parseTargetPriceFromCompanyReadHtml(html) {
  try {
    const $ = cheerio.load(html);
    const raw = $('div.view_info_1').first().find('em.money strong').first().text().trim();
    if (raw) {
      const n = Number(raw.replace(/,/g, ''));
      return Number.isFinite(n) ? n : null;
    }

    // 일부 페이지는 <strong> 없이 <em class="money">123,000</em> 형태
    const emText = $('div.view_info_1').first().find('em.money').first().text().trim();
    if (emText) {
      const m = emText.match(/([0-9][0-9,]*)/);
      if (m) {
        const n = Number(String(m[1]).replace(/,/g, ''));
        return Number.isFinite(n) ? n : null;
      }
    }
  } catch {
    // fallthrough
  }

  const m = String(html || '').match(/목표(?:주)?가[\s\S]{0,50}?<em[^>]*class=["']money["'][^>]*>[\s\S]{0,50}?([0-9][0-9,]*)/);
  if (!m) return null;
  const n = Number(String(m[1]).replace(/,/g, ''));
  return Number.isFinite(n) ? n : null;
}

function parseCompanyListRows(html) {
  const $ = cheerio.load(html);
  const rows = [];
  const seenNids = new Set();

  $('table.type_1 tr').each((_, tr) => {
    const tds = $(tr).find('td');
    if (tds.length < 3) return;

    const href = tds.eq(1).find('a[href*="company_read.naver?"]').attr('href');
    const nid = parseNaverNidFromHref(href);
    if (!nid) return;
    if (seenNids.has(nid)) return;
    seenNids.add(nid);

    const brokerRaw = String(tds.eq(2).text() || '').trim();
    const brokerKey = normalizeBrokerName(brokerRaw);
    rows.push({ nid, brokerRaw, brokerKey });
  });

  return rows;
}

async function fetchNaverCompanyListHtml(params) {
  const response = await naverClient.get('/research/company_list.naver', {
    responseType: 'arraybuffer',
    params,
  });
  return decodeNaverHtml(response.data);
}

function getCompanyListPageDebugInfo(html, sampleLimit) {
  try {
    const $ = cheerio.load(html);
    const title = ($('title').first().text() || '').trim();
    const rows = $('table.type_1 tr');
    const brokerSamples = [];

    rows.each((_, tr) => {
      if (brokerSamples.length >= sampleLimit) return;
      const tds = $(tr).find('td');
      if (tds.length < 3) return;
      const brokerRaw = tds.eq(2).text();
      const brokerKey = normalizeBrokerName(brokerRaw);
      if (brokerKey) brokerSamples.push(brokerKey);
    });

    return {
      title,
      rowCount: rows.length,
      brokerSamples,
    };
  } catch {
    return null;
  }
}

function extractBrokerKeysFromCompanyList(html, limit) {
  const $ = cheerio.load(html);
  const brokers = [];
  const seen = new Set();
  $('table.type_1 tr').each((_, tr) => {
    if (brokers.length >= limit) return;
    const tds = $(tr).find('td');
    if (tds.length < 3) return;
    const brokerKey = normalizeBrokerName(tds.eq(2).text());
    if (!brokerKey) return;
    if (seen.has(brokerKey)) return;
    seen.add(brokerKey);
    brokers.push(brokerKey);
  });
  return brokers;
}

async function fetchNaverCompanyListPage(itemCode, page) {
  return fetchNaverCompanyListHtml({
    searchType: 'itemCode',
    itemCode,
    page,
  });
}

function parseCompanyListForBrokerNids(html, wantedBrokerNeedles) {
  const found = new Map(); // needle -> nid[]

  const rows = parseCompanyListRows(html);
  for (const row of rows) {
    if (!row?.nid || !row?.brokerKey) continue;
    for (const needle of wantedBrokerNeedles) {
      if (!needle) continue;
      if (row.brokerKey.includes(needle)) {
        const list = found.get(needle) ?? [];
        if (!list.includes(row.nid)) list.push(row.nid);
        found.set(needle, list);
      }
    }
  }

  return found;
}

async function fetchNaverCompanyReadHtml(nid) {
  const response = await naverClient.get('/research/company_read.naver', {
    responseType: 'arraybuffer',
    params: { nid }
  });
  return decodeNaverHtml(response.data);
}

async function getBrokerTargetPricesFromNaver(itemCode, options) {
  const maxPages = Math.max(1, Math.min(30, Number(options?.maxPages ?? 10)));
  const debug = options?.debug === true;
  const maxNidsPerBroker = Math.max(1, Math.min(10, Number(options?.maxNidsPerBroker ?? 5)));
  const allowFallbackAnyBroker = parseBooleanParam(options?.allowFallbackAnyBroker, true);

  // 목록의 증권사 표기가 괄호/부가문구를 포함하는 경우가 있어 substring 매칭을 사용
  const wantedNeedleToKey = new Map([
    [normalizeBrokerName('KB증권'), 'kb'],
    [normalizeBrokerName('NH투자증권'), 'nh'],
    [normalizeBrokerName('한국투자증권'), 'kis'],
  ]);
  const wantedNeedles = Array.from(wantedNeedleToKey.keys());

  const nidsByNeedle = new Map(); // needle -> nid[]
  let debugFirstPageInfo = null;
  const debugBrokersSeen = debug ? [] : null;
  const debugBrokersSeenSet = debug ? new Set() : null;

  const orderedRecentRows = [];
  const orderedRecentNids = new Set();

  for (let page = 1; page <= maxPages; page += 1) {
    const html = await fetchNaverCompanyListPage(itemCode, page);
    if (debug && page === 1) {
      debugFirstPageInfo = getCompanyListPageDebugInfo(html, 20);
    }

    // fallback용: 최신 리포트(표 상단)부터 nid/broker를 순서대로 저장
    const rowsForFallback = parseCompanyListRows(html);
    for (const row of rowsForFallback) {
      if (orderedRecentRows.length >= 200) break;
      if (!row?.nid || orderedRecentNids.has(row.nid)) continue;
      orderedRecentNids.add(row.nid);
      orderedRecentRows.push(row);
    }

    if (debug && debugBrokersSeen && debugBrokersSeenSet && debugBrokersSeen.length < 200) {
      const brokers = extractBrokerKeysFromCompanyList(html, 200);
      for (const b of brokers) {
        if (debugBrokersSeen.length >= 200) break;
        if (!debugBrokersSeenSet.has(b)) {
          debugBrokersSeenSet.add(b);
          debugBrokersSeen.push(b);
        }
      }
    }

    const found = parseCompanyListForBrokerNids(html, wantedNeedles);
    for (const [needle, nids] of found.entries()) {
      const existing = nidsByNeedle.get(needle) ?? [];
      for (const nid of nids) {
        if (existing.length >= maxNidsPerBroker) break;
        if (!existing.includes(nid)) existing.push(nid);
      }
      nidsByNeedle.set(needle, existing);
    }

    const complete = Array.from(wantedNeedleToKey.keys()).every((needle) => {
      const list = nidsByNeedle.get(needle) ?? [];
      return list.length >= maxNidsPerBroker;
    });
    if (complete) break;
  }

  const result = {
    kb_tp: null,
    nh_tp: null,
    kis_tp: null,
  };

  const resultSrc = {
    kb_tp_src: null,
    nh_tp_src: null,
    kis_tp_src: null,
  };

  for (const [needle, nids] of nidsByNeedle.entries()) {
    const outKey = wantedNeedleToKey.get(needle);
    if (!outKey) continue;

    for (const nid of nids) {
      try {
        const html = await fetchNaverCompanyReadHtml(nid);
        const tp = parseTargetPriceFromCompanyReadHtml(html);
        if (Number.isFinite(tp)) {
          result[`${outKey}_tp`] = tp;
          resultSrc[`${outKey}_tp_src`] = needle;
          break;
        }
      } catch {
        // ignore
      }
    }
  }

  // 특정 증권사 목표가가 없으면, 해당 종목의 최신 리포트 중 목표가(숫자)가 있는
  // '다른 증권사' 목표가로 대체
  if (allowFallbackAnyBroker) {
    const missingKeys = [];
    for (const key of ['kb', 'nh', 'kis']) {
      if (!Number.isFinite(result[`${key}_tp`])) missingKeys.push(key);
    }

    if (missingKeys.length > 0) {
      let fallback = null;
      for (const row of orderedRecentRows) {
        try {
          const html = await fetchNaverCompanyReadHtml(row.nid);
          const tp = parseTargetPriceFromCompanyReadHtml(html);
          if (Number.isFinite(tp)) {
            fallback = { tp, brokerKey: row.brokerKey, brokerRaw: row.brokerRaw, nid: row.nid };
            break;
          }
        } catch {
          // ignore
        }
      }

      if (fallback) {
        for (const key of missingKeys) {
          result[`${key}_tp`] = fallback.tp;
          resultSrc[`${key}_tp_src`] = `fallback:${fallback.brokerRaw || fallback.brokerKey || 'unknown'}`;
        }
      }
    }
  }

  if (!debug) return { ...result, ...resultSrc };
  return {
    ...result,
    ...resultSrc,
    _debug: {
      maxPages,
      maxNidsPerBroker,
      allowFallbackAnyBroker,
      firstPage: debugFirstPageInfo,
      brokersSeen: debugBrokersSeen,
      nids: Object.fromEntries(
        Array.from(nidsByNeedle.entries()).map(([needle, nids]) => [wantedNeedleToKey.get(needle) || needle, nids])
      ),
      fallbackPool: orderedRecentRows.slice(0, 20),
    }
  };
}

async function getBrokerTargetPricesFromNaverCached(code, ttlMs, options) {
  const itemCode = String(code || '').trim().padStart(6, '0');
  const optMaxPages = Math.max(1, Math.min(30, Number(options?.maxPages ?? 10)));
  const optMaxNidsPerBroker = Math.max(1, Math.min(10, Number(options?.maxNidsPerBroker ?? 5)));
  const optAllowFallbackAnyBroker = parseBooleanParam(options?.allowFallbackAnyBroker, true);
  if (String(options?.debug ?? '0') === '1') {
    return await getBrokerTargetPricesFromNaver(itemCode, {
      ...options,
      maxPages: optMaxPages,
      maxNidsPerBroker: optMaxNidsPerBroker,
      allowFallbackAnyBroker: optAllowFallbackAnyBroker,
      debug: true,
    });
  }

  const cacheKey = `${itemCode}|p${optMaxPages}|n${optMaxNidsPerBroker}|f${optAllowFallbackAnyBroker ? 1 : 0}`;
  const now = Date.now();

  const existing = naverResearchCache.get(cacheKey);
  if (existing?.value && now < existing.expiresAtMs) return existing.value;
  if (existing?.inFlight) return existing.inFlight;

  const inFlight = (async () => {
    const value = await getBrokerTargetPricesFromNaver(itemCode, {
      ...options,
      maxPages: optMaxPages,
      maxNidsPerBroker: optMaxNidsPerBroker,
      allowFallbackAnyBroker: optAllowFallbackAnyBroker,
    });
    naverResearchCache.set(cacheKey, {
      value,
      expiresAtMs: Date.now() + ttlMs,
      inFlight: null,
    });
    return value;
  })();

  naverResearchCache.set(cacheKey, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    return await inFlight;
  } finally {
    const entry = naverResearchCache.get(cacheKey);
    if (entry?.inFlight === inFlight) {
      naverResearchCache.set(cacheKey, { ...entry, inFlight: null });
    }
  }
}

function stableStringify(obj) {
  if (!obj || typeof obj !== 'object') return JSON.stringify(obj);
  const keys = Object.keys(obj).sort();
  const normalized = {};
  for (const key of keys) normalized[key] = obj[key];
  return JSON.stringify(normalized);
}

function extractKisContinuationCtx(data) {
  const tryGet = (obj) => {
    if (!obj || typeof obj !== 'object') return null;
    const fk = obj.ctx_area_fk200 ?? obj.ctx_area_fk ?? obj.ctx_area_f ?? obj.ctx_area_fk_200;
    const nk = obj.ctx_area_nk200 ?? obj.ctx_area_nk ?? obj.ctx_area_n ?? obj.ctx_area_nk_200;
    const fkStr = fk === undefined || fk === null ? '' : String(fk).trim();
    const nkStr = nk === undefined || nk === null ? '' : String(nk).trim();
    if (!fkStr && !nkStr) return null;
    return { ctx_area_fk200: fkStr, ctx_area_nk200: nkStr };
  };

  // KIS 응답은 ctx_area_*가 top-level 또는 output2 등에 들어오는 경우가 있어 후보를 넓게 탐색
  const candidates = [data, data?.output, data?.output1, data?.output2, data?.output3, data?.output4];
  for (const c of candidates) {
    const got = tryGet(c);
    if (got) return got;
  }

  // 1-depth nested 탐색
  for (const c of candidates) {
    if (!c || typeof c !== 'object') continue;
    for (const v of Object.values(c)) {
      const got = tryGet(v);
      if (got) return got;
    }
  }
  return null;
}

function pickFirstArrayFromResponse(data) {
  if (!data || typeof data !== 'object') return null;
  const candidates = [data.output, data.output1, data.output2, data.output3, data.output4];
  for (const c of candidates) {
    if (Array.isArray(c)) return c;
  }
  // 일부 응답은 output 안에 리스트가 들어가는 형태일 수 있어 추가 탐색
  for (const c of candidates) {
    if (c && typeof c === 'object') {
      const nested = [c.output, c.output1, c.output2];
      for (const n of nested) {
        if (Array.isArray(n)) return n;
      }
    }
  }
  return null;
}

async function getAccessToken() {
  const now = Date.now();
  if (cachedAccessToken && now < cachedAccessTokenExpiresAtMs - 30_000) {
    return cachedAccessToken;
  }

  if (accessTokenInFlight) {
    return accessTokenInFlight;
  }

  const url = 'https://openapi.koreainvestment.com:9443/oauth2/tokenP';
  const body = {
    grant_type: 'client_credentials',
    appkey: process.env.KIS_APP_KEY,
    appsecret: process.env.KIS_APP_SECRET
  };

  accessTokenInFlight = (async () => {
    try {
      const response = await axios.post(url, body);
      const token = response.data.access_token;
      const expiresInSec = Number(response.data.expires_in || 0);
      cachedAccessToken = token;
      cachedAccessTokenExpiresAtMs = Date.now() + (Number.isFinite(expiresInSec) ? expiresInSec * 1000 : 0);
      return token;
    } catch (e) {
      console.error('토큰 발급 실패:', e.response?.data || e.message);
      throw e;
    } finally {
      accessTokenInFlight = null;
    }
  })();

  return accessTokenInFlight;
}

app.get('/api/price', async (req, res) => {
  const { code } = req.query;
  const safeCode = String(code ?? '').trim().padStart(6, '0');
  if (!safeCode) {
    return res.status(400).json({ error: 'code(종목코드)가 필요합니다.' });
  }
  if (!/^[0-9]{6}$/.test(safeCode)) {
    return res.status(400).json({ error: '유효하지 않은 code 입니다.', details: { code } });
  }
  try {
    const universeTtlMs = clampUniverseTtlMs(req.query.universeTtlMs ?? req.query.ttlMs);
    const ok = await assertUniverseAllowsCodeOrReject(res, safeCode, universeTtlMs);
    if (!ok) return;

    const token = await getAccessToken();
    const out = await inquirePriceOutputWithFallback(token, safeCode);
    // 프론트에서 합치기 쉽게 code/name을 추가해 둡니다.
    out.code = safeCode;
    out.name = out?.hts_kor_isnm ?? out?.stck_name ?? out?.isnm ?? null;
    return res.json(out);
  } catch (e) {
    console.error('시세 조회 실패:', safeCode, e.response?.data || e.message);
    return res.status(500).json({ error: '시세 조회 실패', details: e.response?.data || e.message });
  }
});

// ── 종목명 → 종목코드(네이버 검색) ───────────────────
// GET /api/resolve-stock?query=대한전선&limit=5
app.get('/api/resolve-stock', async (req, res) => {
  const query = String(req.query.query ?? req.query.q ?? '').trim();
  if (!query) return res.status(400).json({ error: 'query 파라미터가 필요합니다.' });
  const limit = Math.max(1, Math.min(20, Number(req.query.limit ?? 5)));

  try {
    const ttlMs = Math.max(60_000, Math.min(48 * 60 * 60 * 1000, Number(req.query.ttlMs ?? RESOLVE_STOCK_UNIVERSE_TTL_MS_DEFAULT)));
    const universe = await getResolveStockUniverseCached(ttlMs);
    const q = query.toLowerCase();

    const matches = (universe?.items || [])
      .filter(it => {
        const name = String(it?.name ?? '').toLowerCase();
        const code = String(it?.code ?? '');
        return (name && name.includes(q)) || (code && code.includes(q));
      })
      .slice(0, limit)
      .map(it => ({
        code: it.code,
        name: it.name,
        sourceUrl: `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(it.code)}`,
      }));

    return res.json({ query, count: matches.length, items: matches, updatedAt: new Date().toISOString() });
  } catch (e) {
    const diagnostic = {
      message: e.message,
      code: e.code,
      status: e.response?.status,
      data: e.response?.data,
    };
    console.error('resolve-stock 실패:', diagnostic);
    return res.status(500).json({ error: '종목코드 조회 실패', details: diagnostic });
  }
});

// ── 종목 스냅샷(네이버 market-sum 기반, 배치) ─────────
// GET /api/stock-snapshots?codes=001440,005930
// - range-stocks 결과에 없더라도, 전체 종목 캐시에서 현재가/등락/거래량을 찾아 반환합니다.
app.get('/api/stock-snapshots', async (req, res) => {
  const raw = String(req.query.codes ?? '').trim();
  if (!raw) return res.status(400).json({ error: 'codes 파라미터가 필요합니다.' });

  const codes = Array.from(
    new Set(
      raw
        .split(/[,\s]+/)
        .map(s => String(s || '').trim())
        .filter(Boolean)
        .map(s => s.padStart(6, '0'))
        .filter(s => /^[0-9]{6}$/.test(s))
    )
  );

  if (codes.length === 0) return res.status(400).json({ error: '유효한 codes가 없습니다.' });
  if (codes.length > 300) return res.status(400).json({ error: 'codes는 한 번에 최대 300개까지 가능합니다.' });

  const ttlMs = clampUniverseTtlMs(req.query.ttlMs);
  const includeOutOfUniverse = String(req.query.includeOutOfUniverse ?? req.query.includeAll ?? '0') === '1';
  const fallbackItemMain = parseBooleanParam(req.query.fallbackItemMain, true);
  const fallbackTtlMs = Math.max(5_000, Math.min(10 * 60_000, Number(req.query.fallbackTtlMs ?? NAVER_ITEM_MAIN_QUOTE_TTL_MS_DEFAULT)));
  const fallbackConcurrency = Math.max(1, Math.min(6, Number(req.query.fallbackConcurrency ?? 4)));
  const preferItemMain = String(req.query.preferItemMain ?? req.query.quoteSource ?? '').toLowerCase() === '1'
    || String(req.query.preferItemMain ?? '').toLowerCase() === 'true'
    || String(req.query.quoteSource ?? '').toLowerCase() === 'itemmain';

  try {
    // ✅ 빠른 갱신 모드: 유니버스를 크롤링하지 않고 item/main 기준으로 스냅샷을 만듭니다.
    // (관심종목 팝업 등, 화면이 열려있는 동안 주기적으로 갱신할 때 사용)
    if (preferItemMain) {
      const resolved = await mapWithConcurrency(codes, fallbackConcurrency, async (code) => {
        try {
          return await getNaverItemMainQuoteCached(code, fallbackTtlMs);
        } catch {
          return null;
        }
      });
      const items = resolved.filter(Boolean).map((it) => ({
        code: it.code,
        name: it.name,
        stck_prpr: it.stck_prpr ?? null,
        prdy_vrss: it.prdy_vrss ?? null,
        prdy_ctrt: it.prdy_ctrt ?? null,
        acml_vol: null,
        sourceUrl: it.sourceUrl ?? `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(it.code)}`,
      }));
      return res.json({
        count: items.length,
        skippedCount: Math.max(0, codes.length - items.length),
        preferItemMain: true,
        items,
        updatedAt: new Date().toISOString(),
      });
    }

    const universe = await getResolveStockUniverseCached(ttlMs);
    const byCode = new Map();
    for (const it of (universe?.items || [])) {
      const code = String(it?.code ?? '').trim();
      if (code) byCode.set(code, it);
    }

    const inUniverseCodes = codes.filter(c => byCode.has(c));
    const outUniverseCodes = codes.filter(c => !byCode.has(c));

    const items = inUniverseCodes.map(code => {
      const it = byCode.get(code);
      return {
        code: it.code,
        name: it.name,
        stck_prpr: it.stck_prpr ?? null,
        prdy_vrss: it.prdy_vrss ?? null,
        prdy_ctrt: it.prdy_ctrt ?? null,
        acml_vol: it.acml_vol ?? null,
        sourceUrl: `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(it.code)}`,
      };
    });

    let fallbackCount = 0;
    if (includeOutOfUniverse && fallbackItemMain && outUniverseCodes.length > 0) {
      const resolved = await mapWithConcurrency(outUniverseCodes, fallbackConcurrency, async (code) => {
        try {
          return await getNaverItemMainQuoteCached(code, fallbackTtlMs);
        } catch {
          return null;
        }
      });
      for (const it of resolved) {
        if (!it) continue;
        fallbackCount++;
        items.push({
          code: it.code,
          name: it.name,
          stck_prpr: it.stck_prpr ?? null,
          prdy_vrss: it.prdy_vrss ?? null,
          prdy_ctrt: it.prdy_ctrt ?? null,
          acml_vol: null,
          sourceUrl: it.sourceUrl ?? `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(it.code)}`,
        });
      }
    }

    const skippedCount = includeOutOfUniverse ? 0 : Math.max(0, outUniverseCodes.length);
    return res.json({
      count: items.length,
      skippedCount,
      inUniverseCount: inUniverseCodes.length,
      outUniverseCount: outUniverseCodes.length,
      fallbackCount,
      items,
      updatedAt: new Date().toISOString(),
    });
  } catch (e) {
    const diagnostic = {
      message: e.message,
      code: e.code,
      status: e.response?.status,
      data: e.response?.data,
    };
    console.error('stock-snapshots 실패:', diagnostic);
    return res.status(500).json({ error: '종목 스냅샷 조회 실패', details: diagnostic });
  }
});

// ── 네이버 리서치 목표가(증권사별) 디버그 ────────────
// 브라우저/CLI → /api/broker-target?code=005930&maxPages=10
app.get('/api/broker-target', async (req, res) => {
  const code = String(req.query.code ?? '').trim();
  if (!code) return res.status(400).json({ error: 'code(종목코드)가 필요합니다.' });

  try {
    const universeTtlMs = clampUniverseTtlMs(req.query.universeTtlMs ?? req.query.ttlMs);
    const ok = await assertUniverseAllowsCodeOrReject(res, code, universeTtlMs);
    if (!ok) return;
  } catch (e) {
    return res.status(500).json({ error: '유니버스 확인 실패', details: e?.message || String(e) });
  }

  const ttlMs = Math.max(60_000, Math.min(24 * 60 * 60 * 1000, Number(req.query.ttlMs ?? NAVER_BROKER_TARGET_PRICE_TTL_MS_DEFAULT)));
  const maxPages = Math.max(1, Math.min(30, Number(req.query.maxPages ?? 10)));
  const maxNidsPerBroker = Math.max(1, Math.min(10, Number(req.query.maxNidsPerBroker ?? 5)));
  const allowFallbackAnyBroker = parseBooleanParam(req.query.allowFallbackAnyBroker, true);
  const debug = String(req.query.debug ?? '0') === '1';

  try {
    const tps = await getBrokerTargetPricesFromNaverCached(code, ttlMs, { maxPages, maxNidsPerBroker, allowFallbackAnyBroker, debug });
    return res.json({ code: String(code).padStart(6, '0'), ...tps });
  } catch (e) {
    return res.status(500).json({ error: '네이버 목표가 조회 실패', details: e.message });
  }
});

// ── 증시투자 예치금(투자자예탁금) ─────────────────────
// 브라우저 → /api/market-deposit
app.get('/api/market-deposit', async (req, res) => {
  const ttlMs = Math.max(30_000, Math.min(60 * 60 * 1000, Number(req.query.ttlMs ?? MARKET_DEPOSIT_TTL_MS_DEFAULT)));
  try {
    const payload = await getMarketDepositCached(ttlMs);
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '증시투자 예치금 조회 실패', details: e.message });
  }
});

// ── 미국 10년물 국채 금리(DGS10) ─────────────────────
// 브라우저 → /api/us10y
app.get('/api/us10y', async (req, res) => {
  const ttlMs = Math.max(30_000, Math.min(6 * 60 * 60 * 1000, Number(req.query.ttlMs ?? US10Y_TTL_MS_DEFAULT)));
  try {
    const payload = await getUs10yCached(ttlMs);
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '미국 10년물 금리 조회 실패', details: e.message });
  }
});

// ✅ 코스피200 현물
// 브라우저 → /api/kospi200-spot
app.get('/api/kospi200-spot', async (req, res) => {
  const ttlMs = Math.max(5_000, Math.min(10 * 60 * 1000, Number(req.query.ttlMs ?? KOSPI200_SPOT_TTL_MS_DEFAULT)));
  try {
    const payload = await getKospi200SpotCached(ttlMs);
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '코스피200 조회 실패', details: e.message });
  }
});

// ── 미국 10년물 국채 금리 시계열(DGS10, 최근 1년) ─────
// 브라우저 → /api/us10y-series?days=365
app.get('/api/us10y-series', async (req, res) => {
  const ttlMs = Math.max(30_000, Math.min(24 * 60 * 60 * 1000, Number(req.query.ttlMs ?? US10Y_SERIES_TTL_MS_DEFAULT)));
  const days = Number(req.query.days ?? 365);
  try {
    const payload = await getUs10ySeriesCached(ttlMs, { days });
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '미국 10년물 금리 시계열 조회 실패', details: e.message });
  }
});

// ── 미국 기준금리 시계열(EFFR 기반, 최근 1년) ─────────
// 브라우저 → /api/fedfunds-series?days=365
app.get('/api/fedfunds-series', async (req, res) => {
  const ttlMs = Math.max(30_000, Math.min(24 * 60 * 60 * 1000, Number(req.query.ttlMs ?? FEDFUNDS_SERIES_TTL_MS_DEFAULT)));
  const days = Number(req.query.days ?? 365);
  try {
    const payload = await getFedFundsSeriesCached(ttlMs, { days });
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '미국 기준금리 시계열 조회 실패', details: e.message });
  }
});

// ── VIX(공포지수) 시계열(Stooq ^VIX, 최근 3년) ─────────
// 브라우저 → /api/vix-series?days=1095
app.get('/api/vix-series', async (req, res) => {
  const ttlMs = Math.max(30_000, Math.min(24 * 60 * 60 * 1000, Number(req.query.ttlMs ?? VIX_SERIES_TTL_MS_DEFAULT)));
  const days = Number(req.query.days ?? 1095);
  try {
    const payload = await getVixSeriesCached(ttlMs, { days });
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: 'VIX 시계열 조회 실패', details: e.message });
  }
});

// ── 미국 CPI (FRED CPIAUCSL, 월별) ───────────────────
// 브라우저 → /api/us-cpi (기본: 최근 12개월)
// - ?year=2026  => 2026-01 ~ 최신 데이터
// - ?lastN=12   => 최신 월별 데이터 N개(기본 12)
app.get('/api/us-cpi', async (req, res) => {
  const ttlMs = Math.max(30_000, Math.min(24 * 60 * 60 * 1000, Number(req.query.ttlMs ?? US_CPI_TTL_MS_DEFAULT)));
  const yearRaw = req.query.year;
  const lastNRaw = req.query.lastN;
  try {
    const payload = await getUsCpiCached(ttlMs, { year: yearRaw, lastN: lastNRaw });
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '미국 CPI 조회 실패', details: e.message });
  }
});

// ── 오일 가격(WTI, FRED) ─────────────────────────────
// 브라우저 → /api/oil
app.get('/api/oil', async (req, res) => {
  const force = String(req.query.force ?? '0') === '1' || Number(req.query.ttlMs ?? NaN) === 0;
  const ttlMs = Math.max(10_000, Math.min(24 * 60 * 60 * 1000, Number(req.query.ttlMs ?? OIL_WTI_TTL_MS_DEFAULT)));
  try {
    if (force) {
      oilWtiCache.value = null;
      oilWtiCache.expiresAtMs = 0;
      oilWtiCache.inFlight = null;
    }
    const payload = await getOilWtiCached(ttlMs);
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '오일 가격 조회 실패', details: e.message });
  }
});

// ── 전 종목 범위 필터(코스피+코스닥, 네이버 페이지 크롤링) ───
// 브라우저 → /api/range-stocks?minPct=-10&maxPct=2&limit=200
app.get('/api/range-stocks', async (req, res) => {
  const ttlMs = Math.max(30_000, Math.min(30 * 60 * 1000, Number(req.query.ttlMs ?? RANGE_STOCKS_TTL_MS_DEFAULT)));
  const minPct = Number(req.query.minPct ?? -10);
  const maxPct = Number(req.query.maxPct ?? 2);
  const limit = Math.max(1, Math.min(2000, Number(req.query.limit ?? 300)));
  const marketRaw = String(req.query.market ?? 'all').toLowerCase();
  const market = ['kospi', 'kosdaq', 'all'].includes(marketRaw) ? marketRaw : 'all';
  const includeSector = String(req.query.includeSector ?? '0') === '1';
  const sectorTtlMs = Math.max(60_000, Math.min(180 * 24 * 60 * 60 * 1000, Number(req.query.sectorTtlMs ?? NAVER_SECTOR_TTL_MS_DEFAULT)));
  const sectorConcurrency = Math.max(1, Math.min(6, Number(req.query.sectorConcurrency ?? 3)));

  if (!Number.isFinite(minPct) || !Number.isFinite(maxPct)) {
    return res.status(400).json({ error: 'minPct/maxPct는 숫자여야 합니다.' });
  }

  const a = Math.min(minPct, maxPct);
  const b = Math.max(minPct, maxPct);

  try {
    const payload = await getRangeStocksCached(ttlMs, { minPct: a, maxPct: b, limit, market });
    if (!includeSector) return res.json(payload);

    const baseItems = Array.isArray(payload?.items) ? payload.items : [];
    const codes = baseItems
      .map(it => String(it?.code ?? '').trim().padStart(6, '0'))
      .filter(c => /^[0-9]{6}$/.test(c));

    const resolved = await mapWithConcurrency(codes, sectorConcurrency, async (code) => {
      try {
        return await getNaverSectorCached(code, sectorTtlMs);
      } catch {
        return { code, sector: null };
      }
    });

    const byCode = new Map();
    for (const it of (resolved || [])) {
      const c = String(it?.code ?? '').trim().padStart(6, '0');
      if (!/^[0-9]{6}$/.test(c)) continue;
      byCode.set(c, it?.sector ?? null);
    }

    const items = baseItems.map(it => {
      const c = String(it?.code ?? '').trim().padStart(6, '0');
      return {
        ...it,
        sector: byCode.has(c) ? byCode.get(c) : null,
      };
    });

    return res.json({
      ...payload,
      items,
      sectorIncluded: true,
    });
  } catch (e) {
    return res.status(500).json({ error: '전 종목 범위 조회 실패', details: e.message });
  }
});

app.get('/api/trading-value-stocks', async (req, res) => {
  const limit = Math.max(1, Math.min(100, Number(req.query.limit ?? 50)));
  const rawRows = Math.max(limit, Math.min(1000, Number(req.query.rawRows ?? 300)));
  const maxPages = Math.max(1, Math.min(30, Number(req.query.rawPages ?? 10)));
  const ttlMs = Math.max(10_000, Math.min(5 * 60_000, Number(req.query.ttlMs ?? TRADING_VALUE_STOCKS_TTL_MS_DEFAULT)));
  const marketRaw = String(req.query.market ?? 'all').toLowerCase();
  const market = ['kospi', 'kosdaq', 'all'].includes(marketRaw) ? marketRaw : 'all';
  const includeSector = String(req.query.includeSector ?? '0') === '1';
  const sectorTtlMs = Math.max(60_000, Math.min(180 * 24 * 60 * 60 * 1000, Number(req.query.sectorTtlMs ?? NAVER_SECTOR_TTL_MS_DEFAULT)));
  const sectorConcurrency = Math.max(1, Math.min(6, Number(req.query.sectorConcurrency ?? 3)));
  const fidQueryParams = Object.fromEntries(
    Object.entries(req.query)
      .filter(([key]) => key.toLowerCase().startsWith('fid_'))
      .map(([key, value]) => [key.toUpperCase(), String(value)])
  );
  const cacheKey = stableStringify({ market, limit, rawRows, maxPages, includeSector, fidQueryParams });
  const now = Date.now();
  const existing = tradingValueStocksCacheByKey.get(cacheKey);
  if (existing?.value && now < existing.expiresAtMs) return res.json(existing.value);
  if (existing?.inFlight) {
    const awaited = await existing.inFlight;
    return res.json(awaited);
  }

  const inFlight = (async () => {
    const token = await getAccessToken();
    const url = 'https://openapi.koreainvestment.com:9443/uapi/domestic-stock/v1/quotations/volume-rank';
    const trId = process.env.KIS_TR_ID_VOLUME_RANK || 'FHPST01710000';
    const allRaw = [];
    const scopeInputs = fidQueryParams.FID_INPUT_ISCD
      ? [fidQueryParams.FID_INPUT_ISCD]
      : market === 'kospi'
        ? ['0001']
        : market === 'kosdaq'
          ? ['1001']
          : ['0001', '1001'];

    for (const scopeInput of scopeInputs) {
      let ctx = null;
      for (let page = 1; page <= maxPages && allRaw.length < rawRows; page += 1) {
        const response = await axios.get(url, {
          headers: {
            authorization: `Bearer ${token}`,
            appkey: process.env.KIS_APP_KEY,
            appsecret: process.env.KIS_APP_SECRET,
            tr_id: trId,
            custtype: String(req.query.custtype ?? process.env.KIS_CUSTTYPE ?? 'P'),
            tr_cont: page === 1 ? 'N' : 'Y',
          },
          params: {
            ...fidQueryParams,
            FID_COND_MRKT_DIV_CODE: fidQueryParams.FID_COND_MRKT_DIV_CODE ?? 'J',
            FID_COND_SCR_DIV_CODE: fidQueryParams.FID_COND_SCR_DIV_CODE ?? String(req.query.scr ?? '20171'),
            FID_INPUT_ISCD: scopeInput,
            FID_DIV_CLS_CODE: fidQueryParams.FID_DIV_CLS_CODE ?? String(req.query.fid_div_cls_code ?? '0'),
            FID_BLNG_CLS_CODE: fidQueryParams.FID_BLNG_CLS_CODE ?? String(req.query.fid_blng_cls_code ?? '0'),
            FID_TRGT_CLS_CODE: fidQueryParams.FID_TRGT_CLS_CODE ?? String(req.query.fid_trgt_cls_code ?? '111111111'),
            FID_TRGT_EXLS_CLS_CODE: fidQueryParams.FID_TRGT_EXLS_CLS_CODE ?? String(req.query.fid_trgt_exls_cls_code ?? '000000'),
            FID_INPUT_PRICE_1: fidQueryParams.FID_INPUT_PRICE_1 ?? String(req.query.fid_input_price_1 ?? '0'),
            FID_INPUT_PRICE_2: fidQueryParams.FID_INPUT_PRICE_2 ?? String(req.query.fid_input_price_2 ?? '0'),
            FID_VOL_CNT: fidQueryParams.FID_VOL_CNT ?? String(req.query.fid_vol_cnt ?? '0'),
            FID_INPUT_CNT_1: fidQueryParams.FID_INPUT_CNT_1 ?? String(req.query.fid_input_cnt_1 ?? Math.max(limit, 100)),
            ...(page === 1 ? {} : (ctx ?? {})),
          },
          timeout: 15_000,
        });

        const data = response.data;
        if (data?.rt_cd && String(data.rt_cd) !== '0') {
          throw new Error(data?.msg1 || '거래대금 랭킹 조회 실패');
        }

        const pageRaw = pickFirstArrayFromResponse(data) || [];
        if (pageRaw.length > 0) allRaw.push(...pageRaw);

        const nextCtx = extractKisContinuationCtx(data);
        if (!nextCtx) break;
        if (ctx && nextCtx.ctx_area_fk200 === ctx.ctx_area_fk200 && nextCtx.ctx_area_nk200 === ctx.ctx_area_nk200) break;
        ctx = nextCtx;
        if (pageRaw.length === 0) break;
      }
    }

    let allowedCodes = null;
    if (market !== 'all') {
      const marketItems = await fetchNaverMarketSumAll(market === 'kospi' ? 0 : 1);
      allowedCodes = new Set(
        (marketItems || [])
          .map((item) => String(item?.code ?? '').trim().padStart(6, '0'))
          .filter((code) => /^[0-9]{6}$/.test(code))
      );
    }

    const deduped = new Map();
    for (const item of allRaw) {
      const code = String(item?.mksc_shrn_iscd ?? item?.stck_shrn_iscd ?? item?.code ?? '').trim().padStart(6, '0');
      if (!/^[0-9]{6}$/.test(code)) continue;
      if (allowedCodes && !allowedCodes.has(code)) continue;
      if (deduped.has(code)) continue;

      const tradingValueNum = parseNumberWithCommas(item?.acml_tr_pbmn);
      const volumeNum = parseNumberWithCommas(item?.acml_vol);
      const pctNum = Number(item?.prdy_ctrt);

      deduped.set(code, {
        code,
        name: item?.hts_kor_isnm ?? item?.stck_name ?? item?.isnm ?? item?.name ?? code,
        stck_prpr: item?.stck_prpr ?? null,
        prdy_vrss: item?.prdy_vrss ?? null,
        prdy_ctrt: Number.isFinite(pctNum) ? String(pctNum) : (item?.prdy_ctrt ?? null),
        acml_vol: Number.isFinite(volumeNum) ? String(Math.round(volumeNum)) : (item?.acml_vol ?? null),
        acml_tr_pbmn: Number.isFinite(tradingValueNum) ? String(Math.round(tradingValueNum)) : (item?.acml_tr_pbmn ?? null),
      });
    }

    const items = Array.from(deduped.values())
      .sort((a, b) => {
        const av = parseNumberWithCommas(a?.acml_tr_pbmn);
        const bv = parseNumberWithCommas(b?.acml_tr_pbmn);
        const aFinite = Number.isFinite(av);
        const bFinite = Number.isFinite(bv);
        if (!aFinite && !bFinite) return String(a?.code ?? '').localeCompare(String(b?.code ?? ''), 'ko', { numeric: true, sensitivity: 'base' });
        if (!aFinite) return 1;
        if (!bFinite) return -1;
        if (bv !== av) return bv - av;
        return String(a?.code ?? '').localeCompare(String(b?.code ?? ''), 'ko', { numeric: true, sensitivity: 'base' });
      })
      .slice(0, limit);

    if (includeSector && items.length > 0) {
      const codes = items
        .map((item) => String(item?.code ?? '').trim().padStart(6, '0'))
        .filter((code) => /^[0-9]{6}$/.test(code));

      const resolved = await mapWithConcurrency(codes, sectorConcurrency, async (code) => {
        try {
          return await getNaverSectorCached(code, sectorTtlMs);
        } catch {
          return { code, sector: null };
        }
      });

      const sectorByCode = new Map();
      for (const item of resolved || []) {
        const code = String(item?.code ?? '').trim().padStart(6, '0');
        if (!/^[0-9]{6}$/.test(code)) continue;
        sectorByCode.set(code, item?.sector ?? null);
      }

      for (const item of items) {
        const code = String(item?.code ?? '').trim().padStart(6, '0');
        item.sector = sectorByCode.has(code) ? sectorByCode.get(code) : null;
      }
    }

    return {
      market,
      count: items.length,
      items,
      sectorIncluded: includeSector,
      updatedAt: new Date().toISOString(),
      source: 'kis-volume-rank',
    };
  })();

  tradingValueStocksCacheByKey.set(cacheKey, {
    value: existing?.value ?? null,
    expiresAtMs: existing?.expiresAtMs ?? 0,
    inFlight,
  });

  try {
    const payload = await inFlight;
    tradingValueStocksCacheByKey.set(cacheKey, {
      value: payload,
      expiresAtMs: Date.now() + ttlMs,
      inFlight: null,
    });
    return res.json(payload);
  } catch (e) {
    const latest = tradingValueStocksCacheByKey.get(cacheKey);
    if (latest?.inFlight === inFlight) {
      tradingValueStocksCacheByKey.set(cacheKey, {
        value: latest?.value ?? null,
        expiresAtMs: latest?.expiresAtMs ?? 0,
        inFlight: null,
      });
    }
    return res.status(500).json({ error: '거래대금 상위 종목 조회 실패', details: e?.message || String(e) });
  }
});

// ── 네이버 fchart(OHLC) 프록시 ─────────────────────────
// 브라우저에서 fchart.stock.naver.com 직접 호출하면 CORS로 막힐 수 있어 서버가 대신 호출합니다.
// GET /api/naver-fchart?code=005930&timeframe=month&count=600
app.get('/api/naver-fchart', async (req, res) => {
  try {
    const symbol = String(req.query.code ?? req.query.symbol ?? '').trim().padStart(6, '0');
    if (!/^[0-9]{6}$/.test(symbol)) {
      return res.status(400).json({ error: '유효하지 않은 code 입니다.', details: { code: req.query.code } });
    }

    const universeTtlMs = clampUniverseTtlMs(req.query.universeTtlMs ?? req.query.ttlMs);
    const ok = await assertUniverseAllowsCodeOrReject(res, symbol, universeTtlMs);
    if (!ok) return;

    const timeframeRaw = String(req.query.timeframe ?? 'month').toLowerCase();
    const timeframe = ['day', 'week', 'month'].includes(timeframeRaw) ? timeframeRaw : 'month';
    const count = Math.max(10, Math.min(2000, Number(req.query.count ?? 600)));
    const ttlMs = Math.max(
      60_000,
      Math.min(12 * 60 * 60 * 1000, Number(req.query.ttlMs ?? NAVER_FCHART_OHLC_TTL_MS_DEFAULT))
    );

    const payload = await getNaverFchartOhlcCached(ttlMs, { symbol, timeframe, count });
    return res.json(payload);
  } catch (e) {
    const diagnostic = {
      message: e.message,
      code: e.code,
      status: e.response?.status,
      data: e.response?.data,
    };
    console.error('네이버 fchart 조회 실패:', diagnostic);
    return res.status(500).json({ error: '네이버 fchart 조회 실패', details: diagnostic });
  }
});

// ── 이동평균/매수·매도/이격도(5일) 배치 조회 ───────────
// GET /api/ma-signals?codes=005930,000660&count=60
// - 매수/매도: MA5 > MA20 이면 '매수', 아니면 '매도'
// - 5일 이격도: (현재가/MA5)*100
//   - >=103%: 과매수, <=97%: 과매도
app.get('/api/ma-signals', async (req, res) => {
  const raw = String(req.query.codes ?? '').trim();
  if (!raw) return res.status(400).json({ error: 'codes 파라미터가 필요합니다.' });

  const codesAll = Array.from(
    new Set(
      raw
        .split(/[,\s]+/)
        .map(s => String(s || '').trim())
        .filter(Boolean)
        .map(s => s.padStart(6, '0'))
        .filter(s => /^[0-9]{6}$/.test(s))
    )
  );
  if (codesAll.length === 0) return res.status(400).json({ error: '유효한 codes가 없습니다.' });
  if (codesAll.length > 200) return res.status(400).json({ error: 'codes는 한 번에 최대 200개까지 가능합니다.' });

  const count = Math.max(25, Math.min(600, Number(req.query.count ?? 60)));
  const ttlMs = Math.max(60_000, Math.min(6 * 60 * 60 * 1000, Number(req.query.ttlMs ?? 10 * 60 * 1000)));
  const concurrency = Math.max(1, Math.min(6, Number(req.query.concurrency ?? 3)));

  try {
    const universeTtlMs = clampUniverseTtlMs(req.query.universeTtlMs ?? RESOLVE_STOCK_UNIVERSE_TTL_MS_DEFAULT);
    const codes = await filterCodesByUniverse(codesAll, universeTtlMs);
    const skippedCount = Math.max(0, codesAll.length - codes.length);

    if (codes.length === 0) {
      return res.json({
        timeframe: 'day',
        count,
        windows: { maShort: 5, maLong: 20 },
        disparity: { overboughtPct: 103, oversoldPct: 97 },
        skippedCount,
        countItems: 0,
        items: [],
        updatedAt: new Date().toISOString(),
      });
    }

    const items = await mapWithConcurrency(codes, concurrency, async (code) => {
      try {
        const payload = await getNaverFchartOhlcCached(ttlMs, {
          symbol: code,
          timeframe: 'day',
          count,
        });
        const sig = computeMaSignalsFromOhlcItems(payload?.items);
        return {
          code,
          ...sig,
          sourceUrl: payload?.sourceUrl ?? `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(code)}`,
        };
      } catch (e) {
        return {
          code,
          asOfDate: null,
          close: null,
          ma5: null,
          ma20: null,
          rsi14: null,
          tradeSignal: null,
          crossSignal: null,
          disparity5Pct: null,
          disparitySignal: null,
          error: e?.message || String(e),
        };
      }
    });

    return res.json({
      timeframe: 'day',
      count,
      windows: { maShort: 5, maLong: 20 },
      disparity: { overboughtPct: 103, oversoldPct: 97 },
      skippedCount,
      countItems: items.length,
      items,
      updatedAt: new Date().toISOString(),
    });
  } catch (e) {
    const diagnostic = {
      message: e.message,
      code: e.code,
      status: e.response?.status,
      data: e.response?.data,
    };
    console.error('ma-signals 배치 조회 실패:', diagnostic);
    return res.status(500).json({ error: '이동평균/이격도 조회 실패', details: diagnostic });
  }
});

// ── 횡보(박스권) 점수 배치 조회 ───────────────────────
// GET /api/sideways-scores?codes=005930,000660&count=90
// 점수(0~100) → 판정:
// - 80~100: 강한 횡보
// - 60~79 : 횡보
// - 40~59 : 약한 횡보
// - 0~39  : 추세
app.get('/api/sideways-scores', async (req, res) => {
  const raw = String(req.query.codes ?? '').trim();
  if (!raw) return res.status(400).json({ error: 'codes 파라미터가 필요합니다.' });

  const codesAll = Array.from(
    new Set(
      raw
        .split(/[\s,]+/)
        .map(s => String(s || '').trim())
        .filter(Boolean)
        .map(s => s.padStart(6, '0'))
        .filter(s => /^[0-9]{6}$/.test(s))
    )
  );
  if (codesAll.length === 0) return res.status(400).json({ error: '유효한 codes가 없습니다.' });
  if (codesAll.length > 200) return res.status(400).json({ error: 'codes는 한 번에 최대 200개까지 가능합니다.' });

  const count = Math.max(60, Math.min(600, Number(req.query.count ?? 90)));
  const ttlMs = Math.max(60_000, Math.min(6 * 60 * 60 * 1000, Number(req.query.ttlMs ?? 10 * 60 * 1000)));
  const concurrency = Math.max(1, Math.min(6, Number(req.query.concurrency ?? 3)));
  const debug = String(req.query.debug ?? '0') === '1';

  try {
    const universeTtlMs = clampUniverseTtlMs(req.query.universeTtlMs ?? RESOLVE_STOCK_UNIVERSE_TTL_MS_DEFAULT);
    const codes = await filterCodesByUniverse(codesAll, universeTtlMs);
    const skippedCount = Math.max(0, codesAll.length - codes.length);

    if (codes.length === 0) {
      return res.json({
        timeframe: 'day',
        count,
        skippedCount,
        countItems: 0,
        items: [],
        updatedAt: new Date().toISOString(),
      });
    }

    const items = await mapWithConcurrency(codes, concurrency, async (code) => {
      try {
        const payload = await getNaverFchartOhlcCached(ttlMs, {
          symbol: code,
          timeframe: 'day',
          count,
        });
        const out = computeSidewaysScoreFromOhlcItems(payload?.items, { lookback: Math.max(60, Math.min(180, count)) });
        const base = {
          code,
          asOfDate: out?.asOfDate ?? null,
          close: out?.close ?? null,
          score: out?.score ?? null,
          label: out?.label ?? null,
          meaning: out?.meaning ?? null,
          sourceUrl: payload?.sourceUrl ?? `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(code)}`,
        };
        if (!debug) return base;
        return {
          ...base,
          debug: {
            lookbackUsed: Math.max(60, Math.min(180, count)),
            inputBars: Array.isArray(payload?.items) ? payload.items.length : 0,
          },
        };
      } catch (e) {
        return {
          code,
          asOfDate: null,
          close: null,
          score: null,
          label: null,
          meaning: null,
          error: e?.message || String(e),
          sourceUrl: `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(code)}`,
        };
      }
    });

    return res.json({
      timeframe: 'day',
      count,
      skippedCount,
      countItems: items.length,
      items,
      updatedAt: new Date().toISOString(),
    });
  } catch (e) {
    const diagnostic = {
      message: e.message,
      code: e.code,
      status: e.response?.status,
      data: e.response?.data,
    };
    console.error('sideways-scores 배치 조회 실패:', diagnostic);
    return res.status(500).json({ error: '횡보 점수 조회 실패', details: diagnostic });
  }
});

// ── 영업이익(최근 5년, 네이버 + FnGuide 보강) ─────────
// GET /api/op-profits?codes=005930,000660
app.get('/api/op-profits', async (req, res) => {
  const raw = String(req.query.codes ?? '').trim();
  if (!raw) return res.status(400).json({ error: 'codes 파라미터가 필요합니다.' });

  const codesAll = Array.from(
    new Set(
      raw
        .split(/[,\s]+/)
        .map(s => String(s || '').trim())
        .filter(Boolean)
        .map(s => s.padStart(6, '0'))
        .filter(s => /^[0-9]{6}$/.test(s))
    )
  );

  if (codesAll.length === 0) return res.status(400).json({ error: '유효한 codes가 없습니다.' });
  if (codesAll.length > 60) return res.status(400).json({ error: 'codes는 한 번에 최대 60개까지 가능합니다.' });

  const ttlMs = Math.max(
    60_000,
    Math.min(48 * 60 * 60 * 1000, Number(req.query.ttlMs ?? NAVER_OP_PROFIT_TTL_MS_DEFAULT))
  );
  const concurrency = Math.max(1, Math.min(3, Number(req.query.concurrency ?? 2)));

  try {
    const universeTtlMs = clampUniverseTtlMs(req.query.universeTtlMs ?? RESOLVE_STOCK_UNIVERSE_TTL_MS_DEFAULT);
    const codes = await filterCodesByUniverse(codesAll, universeTtlMs);
    const skippedCount = Math.max(0, codesAll.length - codes.length);

    if (codes.length === 0) {
      return res.json({ count: 0, skippedCount, unit: '억원', items: [], updatedAt: new Date().toISOString() });
    }

    const items = await mapWithConcurrency(codes, concurrency, async (code) => {
      try {
        return await getNaverOperatingProfitCached(code, ttlMs);
      } catch {
        const nowYear = new Date().getFullYear();
        const annualOpProfits = Array.from({ length: 5 }, (_, idx) => ({
          year: nowYear - (idx + 1),
          label: null,
          value: null,
        }));
        return {
          code,
          unit: '억원',
          annualOpProfits,
          lastYear: annualOpProfits[0].year,
          prevYear: annualOpProfits[1].year,
          thirdYear: annualOpProfits[2].year,
          fourthYear: annualOpProfits[3].year,
          fifthYear: annualOpProfits[4].year,
          lastYearLabel: null,
          prevYearLabel: null,
          thirdYearLabel: null,
          fourthYearLabel: null,
          fifthYearLabel: null,
          opProfitLastYear: null,
          opProfitPrevYear: null,
          opProfitThirdYear: null,
          opProfitFourthYear: null,
          opProfitFifthYear: null,
          eps: null,
          creditRatioPct: null,
          sourceUrl: `https://finance.naver.com/item/main.naver?code=${encodeURIComponent(code)}`,
        };
      }
    });
    return res.json({ count: items.length, skippedCount, unit: '억원', items, updatedAt: new Date().toISOString() });
  } catch (e) {
    const diagnostic = {
      message: e.message,
      code: e.code,
      status: e.response?.status,
      data: e.response?.data,
    };
    console.error('영업이익 배치 조회 실패:', diagnostic);
    return res.status(500).json({ error: '영업이익 배치 조회 실패', details: diagnostic });
  }
});

// ── 외국인 매수/매도(일별) ────────────────────────────
// GET /api/foreign-flows?codes=005930,000660&date=20250812
// - date(YYYYMMDD) 미지정 시 한국시간 오늘
// - 실시간성은 KIS 제공 범위 내(일별/가집계/마감 후 반영 등)에서 동작
app.get('/api/foreign-flows', async (req, res) => {
  // 브라우저/프록시 캐시로 인해 값이 갱신되지 않는 상황을 방지
  res.set('Cache-Control', 'no-store');

  const raw = String(req.query.codes ?? '').trim();
  if (!raw) return res.status(400).json({ error: 'codes 파라미터가 필요합니다.' });

  const codesAll = Array.from(
    new Set(
      raw
        .split(/[,\s]+/)
        .map(s => String(s || '').trim())
        .filter(Boolean)
        .map(s => s.padStart(6, '0'))
        .filter(s => /^[0-9]{6}$/.test(s))
    )
  );
  if (codesAll.length === 0) return res.status(400).json({ error: '유효한 codes가 없습니다.' });
  if (codesAll.length > 120) return res.status(400).json({ error: 'codes는 한 번에 최대 120개까지 가능합니다.' });

  const date = String(req.query.date ?? req.query.ymd ?? '').trim();
  const marketDivParam = req.query.marketDiv ?? req.query.market;
  const marketDivRaw = marketDivParam === undefined ? '' : String(marketDivParam).trim().toUpperCase();
  // marketDiv 미지정 시 AUTO(J→Q 재시도)
  const marketDiv = ['J', 'Q'].includes(marketDivRaw) ? marketDivRaw : null;
  const ttlMs = Math.max(5_000, Math.min(10 * 60 * 1000, Number(req.query.ttlMs ?? FOREIGN_FLOW_TTL_MS_DEFAULT)));
  const concurrency = Math.max(1, Math.min(6, Number(req.query.concurrency ?? 3)));
  const debug = String(req.query.debug ?? '0') === '1';

  try {
    const universeTtlMs = clampUniverseTtlMs(req.query.universeTtlMs ?? RESOLVE_STOCK_UNIVERSE_TTL_MS_DEFAULT);
    const codes = await filterCodesByUniverse(codesAll, universeTtlMs);
    const skippedCount = Math.max(0, codesAll.length - codes.length);

    if (codes.length === 0) {
      return res.json({
        date: date || getKstYmd(),
        marketDiv: marketDiv || 'AUTO',
        skippedCount,
        count: 0,
        items: [],
        updatedAt: new Date().toISOString(),
      });
    }

    const token = await getAccessToken();
    const items = await mapWithConcurrency(codes, concurrency, async (code) => {
      try {
        return await getForeignFlowMaybeAuto(token, code, { ymd: date || null, marketDiv, ttlMs, debug });
      } catch (e) {
        return {
          code,
          date: date || null,
          marketDiv: marketDiv || null,
          mode: 'error',
          frgn_buy_vol: null,
          frgn_sell_vol: null,
          frgn_buy_amt: null,
          frgn_sell_amt: null,
          frgn_net_qty: null,
          error: e?.message || String(e),
        };
      }
    });

    return res.json({
      date: date || getKstYmd(),
      marketDiv: marketDiv || 'AUTO',
      skippedCount,
      count: items.length,
      items,
      updatedAt: new Date().toISOString(),
    });
  } catch (e) {
    const diagnostic = {
      message: e.message,
      code: e.code,
      status: e.response?.status,
      data: e.response?.data,
    };
    console.error('foreign-flows 배치 조회 실패:', diagnostic);
    return res.status(500).json({ error: '외국인 매수/매도 조회 실패', details: diagnostic });
  }
});

// ── 공매도 순보유잔고 금액(배치, KRX) ─────────────────
// GET /api/loan-balances?codes=005930,000660
const handleLoanBalances = async (req, res) => {
  res.set('Cache-Control', 'no-store');

  const raw = String(req.query.codes ?? '').trim();
  if (!raw) return res.status(400).json({ error: 'codes 파라미터가 필요합니다.' });

  const codesAll = Array.from(
    new Set(
      raw
        .split(/[\s,]+/)
        .map(s => String(s || '').trim())
        .filter(Boolean)
        .map(s => s.padStart(6, '0'))
        .filter(s => /^[0-9]{6}$/.test(s))
    )
  );
  if (codesAll.length === 0) return res.status(400).json({ error: '유효한 codes가 없습니다.' });
  if (codesAll.length > 120) return res.status(400).json({ error: 'codes는 한 번에 최대 120개까지 가능합니다.' });

  const ttlMs = Math.max(60_000, Math.min(24 * 60 * 60 * 1000, Number(req.query.ttlMs ?? KRX_SHORT_BALANCE_TTL_MS_DEFAULT)));
  const concurrency = Math.max(1, Math.min(6, Number(req.query.concurrency ?? 3)));

  try {
    const universeTtlMs = clampUniverseTtlMs(req.query.universeTtlMs ?? RESOLVE_STOCK_UNIVERSE_TTL_MS_DEFAULT);
    const codes = await filterCodesByUniverse(codesAll, universeTtlMs);
    const skippedCount = Math.max(0, codesAll.length - codes.length);

    if (codes.length === 0) {
      return res.json({ count: 0, skippedCount, items: [], updatedAt: new Date().toISOString() });
    }

    const items = await mapWithConcurrency(codes, concurrency, async (code) => {
      try {
        return await getKrxShortBalanceCached(code, { ttlMs });
      } catch {
        return {
          code,
          isuCd: null,
          date: null,
          loan_balance_amount: null,
          sourceUrl: `https://data.krx.co.kr/comm/srt/srtLoader/index.cmd?screenId=MDCSTAT300&isuCd=${encodeURIComponent(code)}`,
          updatedAt: new Date().toISOString(),
        };
      }
    });

    return res.json({ count: items.length, skippedCount, items, updatedAt: new Date().toISOString() });
  } catch (e) {
    const diagnostic = {
      message: e.message,
      code: e.code,
      status: e.response?.status,
      data: e.response?.data,
    };
    console.error('loan-balances 배치 조회 실패:', diagnostic);
    return res.status(500).json({ error: '대차거래잔고 조회 실패', details: diagnostic });
  }
};

app.get('/api/loan-balances', handleLoanBalances);
app.get('/api/short-balances', handleLoanBalances);

// ── 목표가(배치) 조회 ─────────────────────────────────
// range-stocks는 종목 리스트만 빠르게 내려주고,
// 목표가/증권사 리포트 기반 목표가는 별도 배치 API로 천천히 채웁니다.
// GET /api/targets?codes=005930,000660&withPerPbr=1&withBrokers=1

async function computePerPbrTargetsForCode(code, params) {
  const c = String(code || '').trim().padStart(6, '0');
  const targetPer = Number(params?.targetPer);
  const targetPbr = Number(params?.targetPbr);
  const priceTtlMs = Math.max(10_000, Math.min(600_000, Number(params?.priceTtlMs ?? 120_000)));
  // 과거 호환: salesTtlMs라는 이름으로 받던 TTL을 epsTtlMs로도 받습니다.
  const epsTtlMs = Math.max(
    60_000,
    Math.min(24 * 60 * 60 * 1000, Number(params?.epsTtlMs ?? params?.salesTtlMs ?? 6 * 60 * 60 * 1000))
  );

  const token = await getAccessToken();
  const price = await getInquirePriceCached(token, c, priceTtlMs);
  const eps = Number(price?.eps);
  const bps = Number(price?.bps);
  const currentPrice = parseKrwPrice(price?.stck_prpr);

  const hasMeaningfulEps = Number.isFinite(eps) && eps > 0;
  const hasMeaningfulBps = Number.isFinite(bps) && bps > 0;

  let epsConsensus = null;
  try {
    const epsInfo = await getNaverConsensusEpsEstimateCached(c, epsTtlMs);
    const parsedConsensus = Number(epsInfo?.epsConsensus);
    epsConsensus = Number.isFinite(parsedConsensus) && parsedConsensus > 0 ? parsedConsensus : null;
  } catch {
    epsConsensus = null;
  }

  // KIS EPS가 비어 있는 종목은 네이버 컨센서스 EPS로 목표가 계산을 보완합니다.
  const effectivePerBase = hasMeaningfulEps ? eps : epsConsensus;
  const currentPer = (Number.isFinite(currentPrice) && currentPrice > 0 && Number.isFinite(epsConsensus) && epsConsensus > 0)
    ? (currentPrice / epsConsensus)
    : null;

  const perTarget = (Number.isFinite(effectivePerBase) && Number.isFinite(targetPer)) ? String(Math.round(effectivePerBase * targetPer)) : null;
  const pbrTarget = (hasMeaningfulBps && Number.isFinite(targetPbr)) ? String(Math.round(bps * targetPbr)) : null;

  return { code: c, target_prc: perTarget, target_prc_pbr: pbrTarget, current_per: currentPer };
}

async function computeBrokerTargetsForCode(code, params) {
  const c = String(code || '').trim().padStart(6, '0');
  const brokerTargetPriceTtlMs = Math.max(
    60_000,
    Math.min(24 * 60 * 60 * 1000, Number(params?.brokerTargetPriceTtlMs ?? NAVER_BROKER_TARGET_PRICE_TTL_MS_DEFAULT))
  );
  const brokerMaxPages = Math.max(1, Math.min(30, Number(params?.brokerMaxPages ?? 10)));
  const brokerMaxNidsPerBroker = Math.max(1, Math.min(10, Number(params?.brokerMaxNidsPerBroker ?? 5)));
  const brokerAllowFallbackAnyBroker = parseBooleanParam(params?.brokerAllowFallbackAnyBroker, true);

  const brokerTps = await getBrokerTargetPricesFromNaverCached(c, brokerTargetPriceTtlMs, {
    maxPages: brokerMaxPages,
    maxNidsPerBroker: brokerMaxNidsPerBroker,
    allowFallbackAnyBroker: brokerAllowFallbackAnyBroker,
  });
  return {
    code: c,
    kb_tp: brokerTps?.kb_tp ?? null,
    nh_tp: brokerTps?.nh_tp ?? null,
    kis_tp: brokerTps?.kis_tp ?? null,
  };
}

app.get('/api/targets', async (req, res) => {
  const raw = String(req.query.codes ?? '').trim();
  if (!raw) return res.status(400).json({ error: 'codes 파라미터가 필요합니다.' });

  const codesAll = Array.from(
    new Set(
      raw
        .split(/[,\s]+/)
        .map(s => String(s || '').trim())
        .filter(Boolean)
        .map(s => s.padStart(6, '0'))
        .filter(s => /^[0-9]{6}$/.test(s))
    )
  );

  if (codesAll.length === 0) return res.status(400).json({ error: '유효한 codes가 없습니다.' });
  if (codesAll.length > 120) return res.status(400).json({ error: 'codes는 한 번에 최대 120개까지 가능합니다.' });

  const withPerPbr = parseBooleanParam(req.query.withPerPbr, true);
  const withBrokers = parseBooleanParam(req.query.withBrokers, true);
  const withLoanBalance = parseBooleanParam(req.query.withLoanBalance, true);
  const cacheOnly = parseBooleanParam(req.query.cacheOnly, false);

  const targetPer = Number(req.query.targetPer ?? process.env.TARGET_PER ?? 15);
  const targetPbr = Number(req.query.targetPbr ?? process.env.TARGET_PBR ?? 1);
  const priceTtlMs = Math.max(10_000, Math.min(600_000, Number(req.query.priceTtlMs ?? 120_000)));

  // PER배수 컬럼(current_per)은 컨센서스 EPS(추정치) 기준으로 계산합니다.
  // - current_per = 현재가 / 컨센서스 EPS
  // - ttl 파라미터는 epsTtlMs(권장) 또는 과거 호환 salesTtlMs를 사용합니다.
  const epsTtlMs = Math.max(
    60_000,
    Math.min(24 * 60 * 60 * 1000, Number(req.query.epsTtlMs ?? req.query.salesTtlMs ?? 6 * 60 * 60 * 1000))
  );

  const brokerTargetPriceTtlMs = Math.max(
    60_000,
    Math.min(24 * 60 * 60 * 1000, Number(req.query.brokerTargetPriceTtlMs ?? NAVER_BROKER_TARGET_PRICE_TTL_MS_DEFAULT))
  );
  const brokerMaxPages = Math.max(1, Math.min(30, Number(req.query.brokerMaxPages ?? 10)));
  const brokerMaxNidsPerBroker = Math.max(1, Math.min(10, Number(req.query.brokerMaxNidsPerBroker ?? req.query.maxNidsPerBroker ?? 5)));
  const brokerAllowFallbackAnyBroker = parseBooleanParam(
    req.query.brokerAllowFallbackAnyBroker ?? req.query.allowFallbackAnyBroker,
    true
  );

  const apiPerTtlMs = Math.max(10_000, Math.min(60 * 60_000, Number(req.query.apiPerTtlMs ?? TARGETS_API_PER_TTL_MS_DEFAULT)));
  const apiBrokerTtlMs = Math.max(10_000, Math.min(6 * 60 * 60_000, Number(req.query.apiBrokerTtlMs ?? TARGETS_API_BROKER_TTL_MS_DEFAULT)));
  const loanBalanceTtlMs = Math.max(60_000, Math.min(24 * 60 * 60 * 1000, Number(req.query.loanBalanceTtlMs ?? KRX_SHORT_BALANCE_TTL_MS_DEFAULT)));

  try {
    const universeTtlMs = clampUniverseTtlMs(req.query.universeTtlMs ?? RESOLVE_STOCK_UNIVERSE_TTL_MS_DEFAULT);
    const codes = await filterCodesByUniverse(codesAll, universeTtlMs);
    const skippedCount = Math.max(0, codesAll.length - codes.length);

    // 최근 화면에 노출된(요청된) 종목을 hot set에 등록 → 백그라운드에서 계속 갱신
    noteTargetsHotCodes(codes);

    if (codes.length === 0) {
      return res.json({ count: 0, skippedCount, items: [], updatedAt: new Date().toISOString() });
    }

    const now = Date.now();
    const items = await mapWithConcurrency(codes, 3, async (code) => {
      const pending = [];

      let perOut = { code, target_prc: null, target_prc_pbr: null, current_per: null };
      if (withPerPbr) {
        const perKey = buildTargetsPerCacheKey(code, targetPer, targetPbr);
        const cached = getCachedValueSWR(targetsApiPerCache, perKey, apiPerTtlMs);
        if (cached.value) perOut = cached.value;
        // 스테일이거나 없으면 백그라운드 갱신을 큐에 넣음
        if (!cached.value || !cached.fresh) {
          if (!cacheOnly) enqueueTargetsApiPerRefresh(code, { targetPer, targetPbr, priceTtlMs, epsTtlMs });
          // 값이 없거나 스테일이면 pending 표시 (프론트가 재시도)
          pending.push('per');
        }
      }

      let brOut = { code, kb_tp: null, nh_tp: null, kis_tp: null };
      if (withBrokers) {
        const cached = getCachedValueSWR(targetsApiBrokerCache, code, apiBrokerTtlMs);
        if (cached.value) brOut = cached.value;
        if (!cached.value || !cached.fresh) {
          if (!cacheOnly) {
            enqueueTargetsApiBrokerRefresh(code, {
              brokerTargetPriceTtlMs,
              brokerMaxPages,
              brokerMaxNidsPerBroker,
              brokerAllowFallbackAnyBroker,
            });
          }
          pending.push('brokers');
        }
      }

      let loanBalanceAmount = null;
      if (withLoanBalance) {
        try {
          const loanOut = await getKrxShortBalanceCached(code, { ttlMs: loanBalanceTtlMs });
          loanBalanceAmount = loanOut?.loan_balance_amount ?? null;
        } catch {
          loanBalanceAmount = null;
        }
      }

      return {
        code,
        target_prc: perOut?.target_prc ?? null,
        target_prc_pbr: perOut?.target_prc_pbr ?? null,
        current_per: (() => {
          const v = perOut?.current_per;
          if (v === null || v === undefined) return null;
          const n = (typeof v === 'number') ? v : Number(v);
          return Number.isFinite(n) ? n : null;
        })(),
        kb_tp: brOut?.kb_tp ?? null,
        nh_tp: brOut?.nh_tp ?? null,
        kis_tp: brOut?.kis_tp ?? null,
        loan_balance_amount: loanBalanceAmount,
        pending,
        serverNowMs: now,
      };
    });

    return res.json({
      count: items.length,
      skippedCount,
      mode: 'swr',
      items,
      updatedAt: new Date().toISOString(),
    });
  } catch (e) {
    const diagnostic = {
      message: e.message,
      code: e.code,
      status: e.response?.status,
      data: e.response?.data,
    };
    console.error('목표가 배치 조회 실패:', diagnostic);
    return res.status(500).json({ error: '목표가 배치 조회 실패', details: diagnostic });
  }
});

// ── 코스피 지수(네이버 파싱) ─────────────────────────
// 브라우저 → /api/kospi
app.get('/api/kospi', async (req, res) => {
  const ttlMs = Math.max(5_000, Math.min(10 * 60 * 1000, Number(req.query.ttlMs ?? KOSPI_TTL_MS_DEFAULT)));
  try {
    const payload = await getKospiCached(ttlMs);
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '코스피 조회 실패', details: e.message });
  }
});

// ✅ VKOSPI 라우트 추가
// 브라우저 → /api/vkospi
app.get('/api/vkospi', async (req, res) => {
  const ttlMs = Math.max(5_000, Math.min(10 * 60 * 1000, Number(req.query.ttlMs ?? VKOSPI_TTL_MS_DEFAULT)));
  try {
    const payload = await getVkospiCached(ttlMs);
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: 'VKOSPI 조회 실패', details: e.message });
  }
});

// ✅ 미국 지수 선물 (Yahoo Finance)
// - 나스닥100선물: NQ=F
// - S&P500선물: ES=F
app.get('/api/us-futures/nq', async (req, res) => {
  const ttlMs = Math.max(5_000, Math.min(10 * 60 * 1000, Number(req.query.ttlMs ?? US_FUTURES_TTL_MS_DEFAULT)));
  try {
    const payload = await getUsFuturesCached('NQ=F', ttlMs);
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '나스닥100선물 조회 실패', details: e.message });
  }
});

app.get('/api/us-futures/es', async (req, res) => {
  const ttlMs = Math.max(5_000, Math.min(10 * 60 * 1000, Number(req.query.ttlMs ?? US_FUTURES_TTL_MS_DEFAULT)));
  try {
    const payload = await getUsFuturesCached('ES=F', ttlMs);
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: 'S&P 500선물 조회 실패', details: e.message });
  }
});

// ✅ 환율(원/달러) (Yahoo Finance)
// - USD/KRW: KRW=X
app.get('/api/usdkrw', async (req, res) => {
  const ttlMs = Math.max(5_000, Math.min(10 * 60 * 1000, Number(req.query.ttlMs ?? FX_USDKRW_TTL_MS_DEFAULT)));
  try {
    const payload = await getFxCached('KRW=X', ttlMs, { nameOverride: '환율(원/달러)', unitOverride: '원' });
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '환율(원/달러) 조회 실패', details: e.message });
  }
});

// ✅ 달러인덱스(DXY) (Yahoo Finance)
// - ICE U.S. Dollar Index: DX-Y.NYB
app.get('/api/dxy', async (req, res) => {
  const ttlMs = Math.max(5_000, Math.min(10 * 60 * 1000, Number(req.query.ttlMs ?? DXY_TTL_MS_DEFAULT)));
  try {
    const payload = await getDxyCached(ttlMs);
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '달러인덱스(DXY) 조회 실패', details: e.message });
  }
});

// ✅ 코스피200 야간선물 (네이버 선물 code=FUT)
// 브라우저 → /api/kospi200-night-futures
app.get('/api/kospi200-night-futures', async (req, res) => {
  const ttlMs = Math.max(5_000, Math.min(10 * 60 * 1000, Number(req.query.ttlMs ?? KOSPI200_NIGHT_FUTURES_TTL_MS_DEFAULT)));
  try {
    const payload = await getKospi200NightFuturesCached(ttlMs);
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '코스피200 야간선물 조회 실패', details: e.message });
  }
});

// ✅ 공포탐욕지수(Fear & Greed Index)
// 브라우저 → /api/fear-greed
app.get('/api/fear-greed', async (req, res) => {
  const ttlMs = Math.max(5_000, Math.min(10 * 60 * 1000, Number(req.query.ttlMs ?? FEAR_GREED_TTL_MS_DEFAULT)));
  try {
    const payload = await getFearGreedCached(ttlMs);
    return res.json(payload);
  } catch (e) {
    return res.status(500).json({ error: '공포탐욕지수 조회 실패', details: e.message });
  }
});

// ── 전일대비 하락률 상위(필터링) ───────────────────────
// 브라우저 → /api/decliners?minDropPct=5&limit=30&market=J
// - minDropPct: 5  => 전일대비 -5% 이하만
// - limit: 최대 반환 개수
// - market: J(코스피) / Q(코스닥) 등
app.get('/api/decliners', async (req, res) => {
  const limit = Math.max(1, Math.min(300, Number(req.query.limit ?? 30)));
  const minDropPct = Math.max(0, Number(req.query.minDropPct ?? 5));
  const market = String(req.query.market ?? 'J');

  const minPctRaw = req.query.minPct;
  const maxPctRaw = req.query.maxPct;
  const minPct = minPctRaw === undefined ? null : Number(minPctRaw);
  const maxPct = maxPctRaw === undefined ? null : Number(maxPctRaw);
  const hasPctRange = Number.isFinite(minPct) && Number.isFinite(maxPct);

  const targetPer = Number(req.query.targetPer ?? process.env.TARGET_PER ?? 15);
  const targetPbr = Number(req.query.targetPbr ?? process.env.TARGET_PBR ?? 1);
  const priceTtlMs = Math.max(10_000, Math.min(600_000, Number(req.query.priceTtlMs ?? 120_000)));

  const withBrokerTargetPrices = String(req.query.withBrokerTargetPrices ?? '1') !== '0';
  const brokerTargetPriceTtlMs = Math.max(
    60_000,
    Math.min(24 * 60 * 60 * 1000, Number(req.query.brokerTargetPriceTtlMs ?? NAVER_BROKER_TARGET_PRICE_TTL_MS_DEFAULT))
  );
  const brokerConcurrency = Math.max(1, Math.min(4, Number(req.query.brokerConcurrency ?? 2)));
  const brokerMaxPages = Math.max(1, Math.min(30, Number(req.query.brokerMaxPages ?? 10)));
  const brokerMaxNidsPerBroker = Math.max(
    1,
    Math.min(10, Number(req.query.brokerMaxNidsPerBroker ?? req.query.maxNidsPerBroker ?? 5))
  );
  const brokerAllowFallbackAnyBroker = parseBooleanParam(
    req.query.brokerAllowFallbackAnyBroker ?? req.query.allowFallbackAnyBroker,
    true
  );

  // KIS 호출 제한을 피하기 위해 동일 요청은 잠깐 캐시
  const cacheTtlMs = Math.max(5_000, Math.min(60_000, Number(req.query.cacheTtlMs ?? 15_000)));

  const now = Date.now();
  const effectiveKey = stableStringify({
    market,
    minDropPct,
    minPct: hasPctRange ? minPct : null,
    maxPct: hasPctRange ? maxPct : null,
    limit,
    cacheTtlMs,
    targetPer,
    targetPbr,
    priceTtlMs,
    withBrokerTargetPrices,
    brokerTargetPriceTtlMs,
    brokerMaxPages,
    brokerMaxNidsPerBroker,
    brokerAllowFallbackAnyBroker,
  });

  const cacheEntry = declinersCacheByKey.get(effectiveKey);
  if (cacheEntry?.value && now < cacheEntry.expiresAtMs) {
    return res.json(cacheEntry.value);
  }
  if (cacheEntry?.inFlight) {
    const awaited = await cacheEntry.inFlight;
    return res.json(awaited);
  }

  try {
    const token = await getAccessToken();

    // KIS 랭킹(등락률) API: 하락률 상위 목록을 반환하는 엔드포인트
    // (환경/계정에 따라 tr_id/파라미터 요구가 다를 수 있어 에러 details를 그대로 내려줍니다.)
    const url = 'https://openapi.koreainvestment.com:9443/uapi/domestic-stock/v1/ranking/fluctuation';
    const trId = process.env.KIS_TR_ID_FLUCTUATION || 'FHPST01700000';

    // KIS 랭킹 API는 fid_* 필수 필드가 계정/문서/환경에 따라 추가로 요구될 수 있어
    // 쿼리의 fid_* 값을 그대로 전달할 수 있게 합니다.
    const fidQueryParams = Object.fromEntries(
      Object.entries(req.query)
        .filter(([key]) => key.toLowerCase().startsWith('fid_'))
        .map(([key, value]) => [key, String(value)])
    );

    const kisParams = {
      ...fidQueryParams,
      // 보편적으로 사용하는 market 구분 값
      'fid_cond_mrkt_div_code': fidQueryParams.fid_cond_mrkt_div_code ?? market,
      // 일부 랭킹 API에서 필수로 요구
      // (현재 테스트 기준: 1001이 더 많은 종목을 반환하는 경향)
      'fid_input_iscd': fidQueryParams.fid_input_iscd ?? '1001',
      'fid_prc_cls_code': fidQueryParams.fid_prc_cls_code ?? '0',
      'fid_input_price_1': fidQueryParams.fid_input_price_1 ?? '0',
      'fid_input_price_2': fidQueryParams.fid_input_price_2 ?? '0',
      'fid_vol_cnt': fidQueryParams.fid_vol_cnt ?? '0',
      'fid_trgt_cls_code': fidQueryParams.fid_trgt_cls_code ?? '0',
      'fid_trgt_exls_cls_code': fidQueryParams.fid_trgt_exls_cls_code ?? '0',
      'fid_div_cls_code': fidQueryParams.fid_div_cls_code ?? '0',
      'fid_rsfl_rate1': fidQueryParams.fid_rsfl_rate1 ?? '0',
      'fid_rsfl_rate2': fidQueryParams.fid_rsfl_rate2 ?? '0',
      // 스크리닝/정렬 (프로젝트 기존 파라미터명(scr/sort)도 호환)
      'fid_cond_scr_div_code': fidQueryParams.fid_cond_scr_div_code ?? String(req.query.scr ?? '20146'),
      'fid_rank_sort_cls_code': fidQueryParams.fid_rank_sort_cls_code ?? String(req.query.sort ?? '0'),
      // 결과 건수
      'fid_input_cnt_1': fidQueryParams.fid_input_cnt_1 ?? String(Math.max(limit, 200)),
    };

    // 랭킹 API는 보통 1페이지에 30개만 내려오고, 연속조회(tr_cont + ctx_area_*)가 필요합니다.
    // 필터(minPct/maxPct) 적용 후에도 충분한 종목을 얻기 위해, 필요 시 여러 페이지를 모읍니다.
    const desiredRawRows = Math.max(
      limit,
      Math.min(2000, Number(req.query.rawRows ?? (hasPctRange ? 1000 : 300)))
    );
    const maxPages = Math.max(1, Math.min(30, Number(req.query.rawPages ?? 15)));

    const doRequest = async () => {
      const delay = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

      const allRaw = [];
      let ctx = null;

      for (let page = 1; page <= maxPages && allRaw.length < desiredRawRows; page += 1) {
        let response;
        for (let attempt = 1; attempt <= 2; attempt += 1) {
          try {
            const params = {
              ...kisParams,
              ...(page === 1 ? {} : (ctx ?? {})),
            };

            response = await axios.get(url, {
              headers: {
                'authorization': `Bearer ${token}`,
                'appkey': process.env.KIS_APP_KEY,
                'appsecret': process.env.KIS_APP_SECRET,
                'tr_id': trId,
                'custtype': String(req.query.custtype ?? process.env.KIS_CUSTTYPE ?? 'P'),
                'tr_cont': page === 1 ? 'N' : 'Y',
              },
              timeout: 15_000,
              params,
            });
            break;
          } catch (e) {
            const code = e?.code;
            const message = String(e?.message || '');
            const isTransient =
              code === 'ECONNRESET' ||
              code === 'ETIMEDOUT' ||
              code === 'EAI_AGAIN' ||
              message.toLowerCase().includes('socket hang up');

            if (!isTransient || attempt >= 2) throw e;
            await delay(300 * attempt);
          }
        }

        if (!response) {
          return {
            _cacheKey: effectiveKey,
            market,
            minDropPct,
            count: 0,
            items: [],
            updatedAt: new Date().toISOString(),
            warning: 'KIS 응답 없음',
            details: { url, trId, page },
          };
        }
        const data = response.data;
        if (data?.rt_cd && String(data.rt_cd) !== '0') {
          return {
            _cacheKey: effectiveKey,
            market,
            minDropPct,
            count: 0,
            items: [],
            updatedAt: new Date().toISOString(),
            warning: 'KIS 에러 응답',
            details: data,
          };
        }

        const pageRaw = pickFirstArrayFromResponse(data) || [];
        if (pageRaw.length > 0) allRaw.push(...pageRaw);

        const nextCtx = extractKisContinuationCtx(data);
        if (!nextCtx) break;
        if (ctx && nextCtx.ctx_area_fk200 === ctx.ctx_area_fk200 && nextCtx.ctx_area_nk200 === ctx.ctx_area_nk200) break;
        ctx = nextCtx;

        if (pageRaw.length === 0) break;
      }

      const raw = allRaw;
      if (!raw || raw.length === 0) {
        return {
          _cacheKey: effectiveKey,
          market,
          minDropPct,
          count: 0,
          items: [],
          updatedAt: new Date().toISOString(),
          warning: '응답 형식 오류',
          details: { url, trId, pages: maxPages, desiredRawRows },
        };
      }

      const filtered = raw
        .map(item => {
          const pctStr = item.prdy_ctrt ?? item.prdy_ctrt_rate ?? item.fluc_rt ?? item.rate ?? item.rt;
          let pct = Number(pctStr);

          // 일부 KIS 응답은 등락률이 절대값으로 오고, 별도 sign 필드로 방향을 알려줍니다.
          // pctStr에 부호가 이미 포함되어 있으면 그대로 사용하고, 아니면 sign에 맞춰 부호를 보정합니다.
          const pctStrTrim = String(pctStr ?? '').trim();
          const hasExplicitSign = pctStrTrim.startsWith('-') || pctStrTrim.startsWith('+');

          if (Number.isFinite(pct) && !hasExplicitSign) {
            const signRaw = item.prdy_vrss_sign ?? item.prdy_vrss_sign_code ?? item.prdy_vrss_sign_cd ?? item.vrss_sign;
            const sign = String(signRaw ?? '').trim();
            const changeNum = Number(item.prdy_vrss);

            const isDownBySign = sign === '4' || sign === '5' || sign.toLowerCase() === 'dn' || sign.toLowerCase() === 'down';
            const isUpBySign = sign === '1' || sign === '2' || sign.toLowerCase() === 'up';

            if (Number.isFinite(changeNum)) {
              if (changeNum < 0) pct = -Math.abs(pct);
              else if (changeNum > 0) pct = Math.abs(pct);
            } else if (isDownBySign) {
              pct = -Math.abs(pct);
            } else if (isUpBySign) {
              pct = Math.abs(pct);
            }
          }

          // ✅ 5,000원 이하 종목 제외 (KIS 랭킹 응답의 현재가 기준)
          const currentPrice = parseKrwPrice(item?.stck_prpr);
          if (Number.isFinite(currentPrice) && currentPrice <= LOW_PRICE_CUTOFF_KRW) return null;

          return {
            name: item.hts_kor_isnm ?? item.stck_name ?? item.isnm ?? item.name,
            code: item.stck_shrn_iscd ?? item.mksc_shrn_iscd ?? item.code,
            stck_prpr: item.stck_prpr,
            prdy_vrss: item.prdy_vrss,
            prdy_ctrt: Number.isFinite(pct) ? String(pct) : (pctStr ?? ''),
            acml_vol: item.acml_vol,
            acml_tr_pbmn: item.acml_tr_pbmn,
            _pct: pct,
          };
        })
        .filter(Boolean);

      // 중복 종목 제거(코드 기준) 후, 하락률(가장 작은 값=가장 크게 하락) 순으로 정렬
      const dedupedByCode = new Map();
      for (const item of filtered) {
        if (!item?.code) continue;
        if (!dedupedByCode.has(item.code)) dedupedByCode.set(item.code, item);
      }

      const sorted = Array.from(dedupedByCode.values()).sort((a, b) => {
        const ap = Number.isFinite(a._pct) ? a._pct : Number.POSITIVE_INFINITY;
        const bp = Number.isFinite(b._pct) ? b._pct : Number.POSITIVE_INFINITY;
        return ap - bp;
      });

      let primary;
      if (hasPctRange) {
        primary = sorted.filter(item => Number.isFinite(item._pct) && item._pct >= minPct && item._pct <= maxPct);
      } else {
        // 전일대비 -minDropPct% 이하만 반환
        primary = sorted.filter(item => Number.isFinite(item._pct) && item._pct <= -minDropPct);
      }

      const items = primary.slice(0, limit).map(({ _pct, ...rest }) => rest);

      // 목표가(PER 기반): 목표가 = EPS * targetPer
      // 목표가(PBR 기반): 목표가 = BPS * targetPbr
      // KIS 호출 제한을 피하기 위해 종목별 inquire-price는 캐시 + 낮은 동시성으로 조회
      const enriched = await mapWithConcurrency(items, 2, async (item) => {
        if (!item?.code) return { ...item, target_prc: null };
        try {
          const price = await getInquirePriceCached(token, item.code, priceTtlMs);
          const eps = Number(price?.eps);
          const bps = Number(price?.bps);

          const perTarget = (Number.isFinite(eps) && Number.isFinite(targetPer))
            ? String(Math.round(eps * targetPer))
            : null;
          const pbrTarget = (Number.isFinite(bps) && Number.isFinite(targetPbr))
            ? String(Math.round(bps * targetPbr))
            : null;

          return { ...item, target_prc: perTarget, target_prc_pbr: pbrTarget };
        } catch {
          return { ...item, target_prc: null, target_prc_pbr: null };
        }
      });

      const enrichedWithBrokers = withBrokerTargetPrices
        ? await mapWithConcurrency(enriched, brokerConcurrency, async (item) => {
            if (!item?.code) return { ...item, kb_tp: null, nh_tp: null, kis_tp: null };
            try {
              const brokerTps = await getBrokerTargetPricesFromNaverCached(item.code, brokerTargetPriceTtlMs, {
                maxPages: brokerMaxPages,
                maxNidsPerBroker: brokerMaxNidsPerBroker,
                allowFallbackAnyBroker: brokerAllowFallbackAnyBroker,
              });
              return { ...item, ...brokerTps };
            } catch {
              return { ...item, kb_tp: null, nh_tp: null, kis_tp: null };
            }
          })
        : enriched;

      return {
        _cacheKey: effectiveKey,
        market,
        minDropPct,
        minPct: hasPctRange ? minPct : null,
        maxPct: hasPctRange ? maxPct : null,
        targetPer,
        targetPbr,
        count: enrichedWithBrokers.length,
        items: enrichedWithBrokers,
        updatedAt: new Date().toISOString(),
      };
    };

    // in-flight dedupe (effectiveKey 단위)
    const inFlight = doRequest();
    declinersCacheByKey.set(effectiveKey, {
      value: cacheEntry?.value ?? null,
      expiresAtMs: cacheEntry?.expiresAtMs ?? 0,
      inFlight,
    });

    let payload;
    try {
      payload = await inFlight;
    } finally {
      const latest = declinersCacheByKey.get(effectiveKey);
      if (latest?.inFlight === inFlight) {
        declinersCacheByKey.set(effectiveKey, { ...latest, inFlight: null });
      }
    }

    // 성공/경고 응답 모두 캐시해서 호출 제한을 완화
    declinersCacheByKey.set(effectiveKey, {
      value: payload,
      expiresAtMs: Date.now() + cacheTtlMs,
      inFlight: null,
    });

    // warning이 있으면 502로 내리되(프론트에서 오류 표시), details를 포함
    if (payload.warning) {
      return res.status(502).json({ error: `하락률 랭킹 조회 실패(${payload.warning})`, details: payload.details });
    }

    return res.json(payload);

  } catch (e) {
    const diagnostic = {
      message: e.message,
      code: e.code,
      status: e.response?.status,
      data: e.response?.data,
    };
    console.error('하락률 랭킹 조회 실패:', diagnostic);

    // KIS 호출 제한/일시 장애 시, 캐시가 있으면 stale 데이터를 반환
    const staleEntry = declinersCacheByKey.get(effectiveKey);
    if (staleEntry?.value && now < staleEntry.expiresAtMs + 60_000) {
      return res.status(200).json({
        ...staleEntry.value,
        stale: true,
        warning: 'KIS 호출 실패로 캐시 사용',
        details: diagnostic,
      });
    }

    res.status(500).json({
      error: '하락률 랭킹 조회 실패',
      details: diagnostic
    });
  }
});

app.listen(PORT, () => {
  console.log('');
  console.log('✅ ================================');
  console.log(`✅  한국투자증권 프록시 서버 실행 완료`);
  console.log(`✅  http://localhost:${PORT} 접속`);
  console.log('✅ ================================');
  console.log('');
});
