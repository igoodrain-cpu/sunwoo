const fs = require('fs');

const chunkPath = 'D:\\25server\\project\\_tmp_chunks_all\\7735-9029d00f5a957405.js';
const text = fs.readFileSync(chunkPath, 'utf8');

const re = /\"([^\"\\\n]*thistime[^\"\\\n]*)\"/g;
const found = new Set();
for (const m of text.matchAll(re)) {
  const s = m[1];
  // Only keep URL-ish fragments (avoid arbitrary UI strings)
  if (s.includes('thistime') && (s.includes('=') || s.includes('&') || s.includes('?') || s.includes('/api/'))) {
    found.add(s);
  }
}

const list = Array.from(found).sort();
console.log('count=' + list.length);
for (const s of list) console.log(s);
