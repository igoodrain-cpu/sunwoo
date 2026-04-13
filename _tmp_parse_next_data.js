const fs = require('fs');

const html = fs.readFileSync('./_tmp_vkospi_price.html', 'utf8');
const re = /<script id="__NEXT_DATA__" type="application\/json">([\s\S]*?)<\/script>/;
const m = html.match(re);
if (!m) {
  console.log('no __NEXT_DATA__');
  process.exit(1);
}

let nextData;
try {
  nextData = JSON.parse(m[1]);
} catch (e) {
  console.log('parse fail', e.message);
  console.log(m[1].slice(0, 200));
  process.exit(1);
}

const text = JSON.stringify(nextData);
console.log('contains VKOSPI?', text.includes('VKOSPI'));
console.log('contains KVI?', text.includes('KVI'));
console.log('contains VIX?', text.includes('VIX'));
console.log('len', text.length);

const i = text.indexOf('VKOSPI');
console.log('sample around VKOSPI:', i >= 0 ? text.slice(Math.max(0, i - 150), i + 250) : 'none');

// Try to find likely code fields
function collectMatches(obj, out) {
  if (obj === null || obj === undefined) return;
  if (typeof obj === 'string') {
    if (/VKOSPI|KVI\d+|VIX/i.test(obj)) out.add(obj);
    return;
  }
  if (typeof obj !== 'object') return;
  if (Array.isArray(obj)) {
    for (const x of obj) collectMatches(x, out);
    return;
  }
  for (const [k, v] of Object.entries(obj)) {
    if (typeof v === 'string') {
      if (/code|item|symbol/i.test(k) && /VKOSPI|KVI\d+|VIX/i.test(v)) out.add(`${k}=${v}`);
      if (/VKOSPI|KVI\d+|VIX/i.test(v)) out.add(v);
    }
    collectMatches(v, out);
  }
}

const out = new Set();
collectMatches(nextData, out);
console.log('matches:', Array.from(out).slice(0, 50));
