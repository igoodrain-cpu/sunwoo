const fs = require('fs');

const chunkPath = 'D:\\25server\\project\\_tmp_chunks_all\\7735-9029d00f5a957405.js';
const text = fs.readFileSync(chunkPath, 'utf8');

// Extract URL-ish strings without printing arbitrary surrounding code.
const patterns = [
  /\"(\/api\/[^\"\\\s]+)\"/g,
  /\"(https?:\/\/[^\"\\\s]+)\"/g,
];

const urls = new Set();
for (const re of patterns) {
  for (const m of text.matchAll(re)) {
    const u = m[1];
    if (u.includes('http://') || u.includes('https://') || u.startsWith('/api/')) {
      urls.add(u);
    }
  }
}

const list = Array.from(urls).sort();
console.log('urlCount=' + list.length);
for (const u of list) console.log(u);
