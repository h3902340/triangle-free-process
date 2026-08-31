const katex = require('katex');
const { chromium } = require('playwright-core');
const fs = require('fs');
const path = require('path');

const src = fs.readFileSync('content.md', 'utf8');

// ---- tiny markdown-with-LaTeX renderer -------------------------------------
function mathify(s) {
  const out = [];
  s = s.replace(/\$\$([\s\S]+?)\$\$/g, (_, tex) => {
    out.push(katex.renderToString(tex.trim(), { displayMode: true, throwOnError: true, strict: false }));
    return ' ' + (out.length - 1) + ' ';
  });
  s = s.replace(/\$([^$\n]+?)\$/g, (_, tex) => {
    out.push(katex.renderToString(tex.trim(), { displayMode: false, throwOnError: true, strict: false }));
    return '' + (out.length - 1) + '';
  });
  return { s, out };
}
function inlineFmt(s) {
  return s.replace(/\*\*(.+?)\*\*/g, '<strong>$1</strong>')
          .replace(/(^|[^*])\*([^*]+?)\*/g, '$1<em>$2</em>')
          .replace(/`(.+?)`/g, '<code>$1</code>');
}

function makeRestore(out) {
  return t => t.replace(/(\d+)/g, (_, n) => out[+n]);
}

function renderInner(md, restore) {
  const lines = md.split('\n');
  let html = '', i = 0;
  while (i < lines.length) {
    if (lines[i].trim() === '') { i++; continue; }
    if (/^\s*[-*]\s+/.test(lines[i])) {
      html += '<ul>';
      while (i < lines.length && /^\s*[-*]\s+/.test(lines[i])) {
        html += restore(inlineFmt('<li>' + lines[i].replace(/^\s*[-*]\s+/, '') + '</li>')); i++;
      }
      html += '</ul>'; continue;
    }
    if (/^\s*\d+\.\s+/.test(lines[i])) {
      const st = parseInt(lines[i].match(/^\s*(\d+)\./)[1], 10);
      html += st === 1 ? '<ol>' : '<ol start="' + st + '">';
      while (i < lines.length && /^\s*\d+\.\s+/.test(lines[i])) {
        html += restore(inlineFmt('<li>' + lines[i].replace(/^\s*\d+\.\s+/, '') + '</li>')); i++;
      }
      html += '</ol>'; continue;
    }
    if (/^\s*\|/.test(lines[i])) {
      const rows = [];
      while (i < lines.length && /^\s*\|/.test(lines[i])) rows.push(lines[i++]);
      html += renderTable(rows, restore); continue;
    }
    const para = [];
    while (i < lines.length && lines[i].trim() !== '' && !/^(\s*[-*]\s|\s*\d+\.\s|\s*\|)/.test(lines[i])) para.push(lines[i++]);
    html += restore(inlineFmt('<p>' + para.join(' ') + '</p>'));
  }
  return html;
}

function renderTable(rows, restore) {
  const cells = r => r.trim().replace(/^\||\|$/g, '').split('|').map(c => c.trim());
  const head = cells(rows[0]);
  const body = rows.slice(/^\s*\|[\s:-]+\|/.test(rows[1] || '') ? 2 : 1).map(cells);
  let h = '<table><thead><tr>' + head.map(c => '<th>' + restore(inlineFmt(c)) + '</th>').join('') + '</tr></thead><tbody>';
  body.forEach(r => { h += '<tr>' + r.map(c => '<td>' + restore(inlineFmt(c)) + '</td>').join('') + '</tr>'; });
  return h + '</tbody></table>';
}

function render(md) {
  const { s, out } = mathify(md);
  const restore = makeRestore(out);
  const lines = s.split('\n');
  let html = '', i = 0;
  const emit = t => { html += restore(inlineFmt(t)); };
  const labels = { theorem: 'Theorem', lemma: 'Lemma', prop: 'Proposition', def: 'Definition',
                   cor: 'Corollary', proof: 'Proof', idea: 'The idea', note: 'Note', warn: 'Caveat' };

  while (i < lines.length) {
    const L = lines[i];
    const m = L.match(/^:::\s*(\w+)\s*(.*)$/);
    if (m) {
      const kind = m[1], title = m[2];
      const body = [];
      i++;
      while (i < lines.length && !/^:::\s*$/.test(lines[i])) body.push(lines[i++]);
      i++;
      const label = labels[kind] || kind;
      if (kind === 'proof') {
        let inner = renderInner(body.join('\n'), restore);
        const cut = inner.lastIndexOf('</p>');
        inner = cut >= 0 ? inner.slice(0, cut) + '<span class="qed">∎</span>' + inner.slice(cut)
                         : inner + '<span class="qed">∎</span>';
        html += '<div class="proof"><span class="plab">' + label + (title ? ' ' + title : '') + '.</span> ' + inner + '</div>';
      } else if (kind === 'idea' || kind === 'note' || kind === 'warn') {
        html += '<div class="box ' + kind + '"><div class="blab">' + (title || label) + '</div>';
        html += renderInner(body.join('\n'), restore) + '</div>';
      } else {
        html += '<div class="thm ' + kind + '"><div class="tlab">' + label +
                (title ? ' <span class="tname">(' + title + ')</span>' : '') + '</div>';
        html += renderInner(body.join('\n'), restore) + '</div>';
      }
      continue;
    }
    if (/^#{1,4}\s/.test(L)) {
      const n = L.match(/^#+/)[0].length;
      emit('<h' + n + '>' + L.slice(n + 1) + '</h' + n + '>'); i++; continue;
    }
    if (/^\\pagebreak/.test(L)) { html += '<div class="pb"></div>'; i++; continue; }
    if (/^---+$/.test(L)) { html += '<hr>'; i++; continue; }
    if (/^\s*[-*]\s+/.test(L)) {
      html += '<ul>';
      while (i < lines.length && /^\s*[-*]\s+/.test(lines[i])) { emit('<li>' + lines[i].replace(/^\s*[-*]\s+/, '') + '</li>'); i++; }
      html += '</ul>'; continue;
    }
    if (/^\s*\d+\.\s+/.test(L)) {
      const st = parseInt(L.match(/^\s*(\d+)\./)[1], 10);
      html += st === 1 ? '<ol>' : '<ol start="' + st + '">';
      while (i < lines.length && /^\s*\d+\.\s+/.test(lines[i])) { emit('<li>' + lines[i].replace(/^\s*\d+\.\s+/, '') + '</li>'); i++; }
      html += '</ol>'; continue;
    }
    if (/^\s*\|/.test(L)) {
      const rows = [];
      while (i < lines.length && /^\s*\|/.test(lines[i])) rows.push(lines[i++]);
      html += renderTable(rows, restore); continue;
    }
    if (/^>\s?/.test(L)) {
      const q = [];
      while (i < lines.length && /^>\s?/.test(lines[i])) q.push(lines[i++].replace(/^>\s?/, ''));
      html += '<blockquote>' + renderInner(q.join('\n'), restore) + '</blockquote>'; continue;
    }
    if (L.trim() === '') { i++; continue; }
    const para = [];
    while (i < lines.length && lines[i].trim() !== '' &&
           !/^(#{1,4}\s|:::|---+$|\s*[-*]\s|\s*\d+\.\s|\s*\||>\s|\\pagebreak)/.test(lines[i])) para.push(lines[i++]);
    emit('<p>' + para.join(' ') + '</p>');
  }
  return html;
}

const css = fs.readFileSync('node_modules/katex/dist/katex.min.css', 'utf8')
  .replace(/url\(fonts\//g, 'url(' + path.resolve('node_modules/katex/dist/fonts') + '/');

const style = `
@page { size: A4; margin: 20mm 22mm 18mm 22mm; }
html { font-size: 10.7pt; }
body { font-family: Georgia,"Times New Roman",serif; color:#191919; line-height:1.55; margin:0;
       hyphens:auto; text-align:justify; }
h1 { font-size:1.9rem; line-height:1.18; margin:0 0 .25rem; text-align:left; letter-spacing:-.01em; }
h2 { font-size:1.28rem; margin:2.1rem 0 .55rem; text-align:left; color:#7d2b24;
     border-bottom:1px solid #d8d2c8; padding-bottom:.22rem; break-after:avoid; }
h3 { font-size:1.05rem; margin:1.5rem 0 .4rem; text-align:left; break-after:avoid; }
h4 { font-size:.97rem; margin:1.1rem 0 .3rem; text-align:left; font-style:italic; break-after:avoid; }
p { margin:0 0 .62rem; }
ul,ol { margin:.3rem 0 .7rem; padding-left:1.25rem; }
li { margin:.22rem 0; }
code { font-family:"DejaVu Sans Mono",monospace; font-size:.86em; background:#f2f0ec; padding:0 .2em; }
hr { border:0; border-top:1px solid #d8d2c8; margin:1.6rem 0; }
.pb { break-after:page; }
.thm { border-left:2.5px solid #7d2b24; padding:.45rem 0 .1rem .8rem; margin:1rem 0;
       background:#faf8f5; break-inside:avoid; }
.tlab { font-variant:small-caps; letter-spacing:.04em; font-weight:bold; color:#7d2b24; margin-bottom:.15rem; }
.tname { font-variant:normal; font-style:italic; font-weight:normal; color:#5a5148; }
.thm.def { border-left-color:#2b4f7d; background:#f5f7fa; }
.thm.def .tlab { color:#2b4f7d; }
.proof { margin:.2rem 0 1rem; font-size:.96rem; color:#2a2a2a; }
.proof > p:first-of-type { display:inline; }
.plab { font-style:italic; color:#7d2b24; }
.qed { float:right; margin-left:.6em; }
.box { background:#f4f1ea; border:1px solid #e0d9cb; border-radius:2px; padding:.6rem .8rem;
       margin:1rem 0; break-inside:avoid; }
.box .blab { font-variant:small-caps; letter-spacing:.05em; font-weight:bold; font-size:.9rem;
             color:#6b5a2e; margin-bottom:.25rem; }
.box.warn { background:#fdf4f2; border-color:#e8cfc9; }
.box.warn .blab { color:#8a3a2c; }
.box.note { background:#f3f6f9; border-color:#cfdae4; }
.box.note .blab { color:#2b4f7d; }
.box p:last-child { margin-bottom:0; }
.katex-display { margin:.75rem 0; }
.katex { font-size:1.03em; }
strong { color:#000; }
blockquote { margin:.9rem 0 .9rem 1.1rem; padding-left:.9rem; border-left:2px solid #c9c1b4;
             font-style:italic; color:#3a352f; }
blockquote p:last-child { margin-bottom:0; }
table { border-collapse:collapse; width:100%; margin:.6rem 0 .8rem; font-size:.93rem; }
th { text-align:left; font-weight:bold; font-size:.85rem; border-bottom:1px solid #8a8177;
     padding:.25rem .5rem .25rem 0; }
td { padding:.25rem .5rem .25rem 0; border-bottom:1px solid #e2ded6; vertical-align:top; }
tr:last-child td { border-bottom:0; }
.subtitle { font-size:1rem; color:#5a5148; font-style:italic; text-align:left; margin:.1rem 0 1.4rem; }
`;

const page = '<!doctype html><html><head><meta charset="utf-8"><style>' + css + style +
             '</style></head><body>' + render(src) + '</body></html>';

fs.writeFileSync('doc.html', page);
(async () => {
  const b = await chromium.launch({ executablePath: '/opt/pw-browsers/chromium-1194/chrome-linux/chrome', args: ['--no-sandbox'] });
  const p = await b.newPage();
  await p.goto('file://' + path.resolve('doc.html'), { waitUntil: 'load' });
  await p.pdf({ path: 'R3k-proofs.pdf', format: 'A4', printBackground: true,
    margin: { top: '20mm', bottom: '18mm', left: '22mm', right: '22mm' },
    displayHeaderFooter: true,
    headerTemplate: '<div></div>',
    footerTemplate: '<div style="width:100%;font-family:Georgia,serif;font-size:8pt;color:#8a8177;text-align:center;"><span class="pageNumber"></span></div>' });
  await b.close();
  console.log('built R3k-proofs.pdf');
})();
