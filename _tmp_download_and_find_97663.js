const fs = require('fs');
const path = require('path');
const https = require('https');

const htmlPath = 'D:\\25server\\project\\_tmp_vkospi_price.html';
const outDir = 'D:\\25server\\project\\_tmp_chunks_all';
const base = 'https://stock.naver.com';

function ensureDir(p) {
  fs.mkdirSync(p, { recursive: true });
}

function fetchText(url) {
  return new Promise((resolve, reject) => {
    const req = https.get(
      url,
      {
        headers: {
          'User-Agent': 'Mozilla/5.0',
          Accept: '*/*',
          'Accept-Language': 'ko-KR,ko;q=0.9,en;q=0.8',
        },
      },
      (res) => {
        if (res.statusCode && res.statusCode >= 300 && res.statusCode < 400 && res.headers.location) {
          res.resume();
          resolve(fetchText(res.headers.location.startsWith('http') ? res.headers.location : base + res.headers.location));
          return;
        }
        if (res.statusCode !== 200) {
          const chunks = [];
          res.on('data', (d) => chunks.push(d));
          res.on('end', () => {
            reject(new Error(`HTTP ${res.statusCode} for ${url}: ${Buffer.concat(chunks).toString('utf8').slice(0, 200)}`));
          });
          return;
        }
        const chunks = [];
        res.on('data', (d) => chunks.push(d));
        res.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
      }
    );
    req.on('error', reject);
  });
}

async function main() {
  ensureDir(outDir);
  const html = fs.readFileSync(htmlPath, 'utf8');
  const re = /\/_next\/static\/chunks\/[^\s"']+\.js/g;
  const paths = Array.from(new Set(html.match(re) || []));
  console.log(`chunkCount=${paths.length}`);

  for (const p of paths) {
    const fileName = p.split('/').pop();
    const outPath = path.join(outDir, fileName);

    let text;
    if (fs.existsSync(outPath)) {
      text = fs.readFileSync(outPath, 'utf8');
    } else {
      const url = base + p;
      process.stdout.write(`download ${fileName} ... `);
      text = await fetchText(url);
      fs.writeFileSync(outPath, text, 'utf8');
      console.log('ok');
    }

    if (text.includes('97663') && /\b97663\b/.test(text)) {
      // likely candidate (still may include it just as a reference)
      if (text.includes('97663:') || text.includes('97663=(') || text.includes('97663:function') || text.includes('97663:(')) {
        console.log(`FOUND_MODULE_DEF in ${fileName}`);
        const idx = text.indexOf('97663');
        console.log(text.slice(Math.max(0, idx - 120), Math.min(text.length, idx + 220)).replace(/\n/g, '\\n'));
        return;
      }
    }
  }

  console.log('module 97663 definition not found in referenced chunks');
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
