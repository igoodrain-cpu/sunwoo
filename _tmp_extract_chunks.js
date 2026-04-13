const fs = require('fs');

const htmlPath = 'D:\\25server\\project\\_tmp_vkospi_price.html';
const html = fs.readFileSync(htmlPath, 'utf8');

const re = /\/_next\/static\/chunks\/[^\s"']+\.js/g;
const urls = Array.from(new Set(html.match(re) || []));

console.log('chunkCount=' + urls.length);
for (const url of urls) console.log(url);
