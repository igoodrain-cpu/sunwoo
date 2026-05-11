const axios = require('axios');
const cheerio = require('cheerio');

(async () => {
  const url = 'https://comp.fnguide.com/SVO2/ASP/SVD_Main.asp?pGB=1&gicode=A001440&cID=&MenuYn=Y&ReportGB=&NewMenuID=101&stkGb=701';
  const response = await axios.get(url, {
    headers: {
      'User-Agent': 'Mozilla/5.0',
      Referer: 'https://comp.fnguide.com/',
    },
  });
  const $ = cheerio.load(response.data);
  for (const selector of ['#highlight_D_Y table', '#highlight_B_Y table']) {
    const table = $(selector).first();
    console.log('SELECTOR', selector, 'COUNT', table.length);
    if (!table.length) continue;
    const labels = table.find('thead tr').last().find('th').toArray()
      .map((th) => $(th).text().replace(/\s+/g, ' ').trim())
      .filter(Boolean);
    console.log('LABELS', JSON.stringify(labels));
    const rows = table.find('tbody tr').toArray()
      .map((tr) => $(tr).find('th[scope="row"]').first().text().replace(/\s+/g, ' ').trim())
      .filter(Boolean);
    console.log('HAS_OP', rows.includes('영업이익'));
    console.log('ROW_SAMPLE', JSON.stringify(rows.slice(0, 20)));
    const opRow = table.find('tbody tr').filter((_, tr) => $(tr).find('th[scope="row"]').first().text().replace(/\s+/g, ' ').trim() === '영업이익').first();
    if (opRow.length) {
      const opCells = opRow.find('td').toArray().map((td) => $(td).text().replace(/\s+/g, ' ').trim());
      console.log('OP_CELLS', JSON.stringify(opCells));
    }
  }
})().catch((error) => {
  console.error(error);
  process.exit(1);
});
