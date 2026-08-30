import re, markdown, html, io

src = open('/home/user/triangle-free-process/TALK.md').read()

# drop the masthead lines (we rebuild them) : first 5 lines up to the first ---
lines = src.split('\n')
i = lines.index('---')
body_md = '\n'.join(lines[i+1:])

md = markdown.Markdown(extensions=['tables','fenced_code','attr_list'])
body = md.convert(body_md)

# --- post-processing -------------------------------------------------------
# whiteboard cues
body = re.sub(r'<p><strong>\[WB([^<]*?)\]</strong>',
              lambda m: '<p class="wb"><span class="wb-tag">Whiteboard</span><strong>%s</strong>' %
                        (m.group(1).lstrip(' —–-') or ''), body)
# [CHECK] flags
body = re.sub(r'<strong>\[CHECK([^\]]*)\]</strong>',
              lambda m: '<span class="check">check%s</span>' % html.escape(m.group(1)), body)
body = re.sub(r'\[CHECK\]', '<span class="check">check</span>', body)
# stage directions in italics starting with (
body = re.sub(r'<p><em>\(', '<p class="note"><em>(', body)
# part headers:  <h1>Part 0 — 14:00 — Title</h1>
def parthdr(m):
    txt = m.group(1)
    p = txt.split('—')
    if txt.startswith('Appendix') and len(p) == 2:
        return ('<header class="part" id="%s"><h1><span class="pnum">%s</span>%s</h1></header>'
                % (re.sub(r'[^a-z0-9]+','-',txt.lower()).strip('-')[:24],
                   p[0].strip(), p[1].strip()))
    if len(p) >= 3:
        return ('<header class="part" id="%s"><span class="time">%s</span>'
                '<h1><span class="pnum">%s</span>%s</h1></header>'
                % (p[0].strip().lower().replace(' ','-'), p[1].strip(),
                   p[0].strip(), p[2].strip()))
    return '<header class="part" id="%s"><h1>%s</h1></header>' % (
        re.sub(r'[^a-z0-9]+','-',txt.lower()).strip('-'), txt)
body = re.sub(r'<h1>(.*?)</h1>', parthdr, body)
# code blocks -> boards
body = body.replace('<pre><code>', '<pre class="board"><code>')
# warning section
body = body.replace('<h2>⚠️ Read this first (author\'s note)</h2>',
                    '<h2 class="warn">Read this first</h2>')
# tables get a scroll wrapper
body = re.sub(r'<table>', '<div class="tw"><table>', body)
body = re.sub(r'</table>', '</table></div>', body)

nav = ''.join('<a href="#part-%d">%d</a>' % (k,k) for k in range(8))

CSS = """
<title>Two Bites at R(3,k)</title>
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Spectral:ital,wght@0,300;0,400;0,600;1,400&family=IBM+Plex+Mono:wght@400;500&family=IBM+Plex+Sans:wght@400;500;600&display=swap">
<style>
:root{
  --bg:#F6F7FA; --surface:#FFFFFF; --sunk:#EEF1F6;
  --ink:#171B24; --ink-2:#39414F; --muted:#69728A; --line:#DDE2EB;
  --red:#AE3A31; --red-soft:#F6ECEA; --blue:#2B5CA5; --blue-soft:#EAF0F9;
  --amber:#8A6212; --amber-soft:#F8F0DC;
  --serif:"Spectral",Georgia,"Times New Roman",serif;
  --sans:"IBM Plex Sans",system-ui,-apple-system,Segoe UI,sans-serif;
  --mono:"IBM Plex Mono",ui-monospace,SFMono-Regular,Menlo,monospace;
}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){
  --bg:#111419; --surface:#181C23; --sunk:#1E232C;
  --ink:#E6E9EF; --ink-2:#C3C9D5; --muted:#939CAF; --line:#2A303B;
  --red:#E58377; --red-soft:#2A1D1B; --blue:#84AAE6; --blue-soft:#161F2C;
  --amber:#D6AC5A; --amber-soft:#241F14;
}}
:root[data-theme="dark"]{
  --bg:#111419; --surface:#181C23; --sunk:#1E232C;
  --ink:#E6E9EF; --ink-2:#C3C9D5; --muted:#939CAF; --line:#2A303B;
  --red:#E58377; --red-soft:#2A1D1B; --blue:#84AAE6; --blue-soft:#161F2C;
  --amber:#D6AC5A; --amber-soft:#241F14;
}
*{box-sizing:border-box}
body{background:var(--bg);color:var(--ink);font-family:var(--serif);
  font-size:17px;line-height:1.65;-webkit-font-smoothing:antialiased;margin:0}
.wrap{max-width:47rem;margin:0 auto;padding:0 1.5rem 6rem}

/* masthead */
.mast{border-bottom:1px solid var(--line);padding:3.5rem 0 2rem;margin-bottom:2.5rem}
.kicker{font-family:var(--sans);font-size:.72rem;letter-spacing:.14em;text-transform:uppercase;
  color:var(--muted);margin:0 0 1rem}
.mast h1{font-size:clamp(2rem,5vw,2.9rem);line-height:1.1;margin:0 0 .6rem;font-weight:600;
  text-wrap:balance;letter-spacing:-.015em}
.mast h1 em{font-style:italic;font-weight:400}
.mast .by{color:var(--ink-2);margin:0 0 1.6rem;font-size:1.02rem}
.facts{display:flex;flex-wrap:wrap;gap:.5rem}
.facts span{font-family:var(--sans);font-size:.78rem;padding:.3rem .65rem;border:1px solid var(--line);
  border-radius:2px;color:var(--ink-2);background:var(--surface)}

/* sticky nav */
.bar{position:sticky;top:0;z-index:5;background:color-mix(in srgb,var(--bg) 88%,transparent);
  backdrop-filter:blur(8px);border-bottom:1px solid var(--line);font-family:var(--sans)}
.bar div{max-width:47rem;margin:0 auto;padding:.5rem 1.5rem;display:flex;align-items:center;gap:.15rem;
  font-size:.78rem;color:var(--muted)}
.bar b{font-weight:500;margin-right:auto;letter-spacing:.02em}
.bar a{color:var(--muted);text-decoration:none;padding:.2rem .5rem;border-radius:2px}
.bar a:hover,.bar a:focus-visible{color:var(--ink);background:var(--sunk);outline:none}

/* part headers */
.part{margin:4.5rem 0 1.75rem;padding-top:1.25rem;border-top:2px solid var(--ink)}
.part .time{font-family:var(--mono);font-size:.8rem;color:var(--red);letter-spacing:.02em;
  display:block;margin-bottom:.4rem}
.part h1{font-size:1.75rem;font-weight:600;margin:0;line-height:1.2;letter-spacing:-.01em;text-wrap:balance}
.part .pnum{font-family:var(--sans);font-size:.7rem;letter-spacing:.14em;text-transform:uppercase;
  color:var(--muted);display:block;margin-bottom:.3rem;font-weight:600}

h2{font-size:1.22rem;font-weight:600;margin:2.6rem 0 .8rem;line-height:1.3;text-wrap:balance}
h2.warn{color:var(--amber);border-left:3px solid var(--amber);padding-left:.7rem}
h3{font-family:var(--sans);font-size:.98rem;font-weight:600;margin:2rem 0 .6rem}
p{margin:0 0 1rem;color:var(--ink-2)}
strong{color:var(--ink);font-weight:600}
a{color:var(--blue)}
hr{border:0;border-top:1px solid var(--line);margin:3rem 0}
hr + hr{display:none}
ul,ol{padding-left:1.2rem;color:var(--ink-2)}li{margin:.35rem 0}

/* the spoken script */
blockquote{margin:1.4rem 0;padding:.1rem 0 .1rem 1.15rem;border-left:3px solid var(--red);
  background:none}
blockquote p{color:var(--ink);font-size:1.06rem;line-height:1.7}
blockquote p:last-child{margin-bottom:0}

/* whiteboard cues */
p.wb{background:var(--blue-soft);border:1px solid color-mix(in srgb,var(--blue) 22%,transparent);
  border-radius:3px;padding:.7rem .85rem;margin:1.2rem 0;font-family:var(--sans);font-size:.92rem;
  color:var(--ink-2)}
p.wb strong{color:var(--blue)}
.wb-tag{display:block;font-size:.66rem;letter-spacing:.15em;text-transform:uppercase;
  color:var(--blue);font-weight:600;margin-bottom:.25rem}
p.note{font-family:var(--sans);font-size:.88rem;color:var(--muted);
  border-left:2px solid var(--line);padding-left:.8rem;margin:1.2rem 0}
p.note em{font-style:normal}
.check{font-family:var(--sans);font-size:.68rem;letter-spacing:.1em;text-transform:uppercase;
  background:var(--amber-soft);color:var(--amber);border:1px solid color-mix(in srgb,var(--amber) 30%,transparent);
  border-radius:2px;padding:.1rem .35rem;font-weight:600;white-space:nowrap}

/* boards */
pre.board{background:var(--sunk);border:1px solid var(--line);border-radius:3px;
  padding:1rem 1.1rem;overflow-x:auto;margin:1.4rem 0}
pre.board code{font-family:var(--mono);font-size:.83rem;line-height:1.6;color:var(--ink);
  white-space:pre;font-variant-ligatures:none}
code{font-family:var(--mono);font-size:.86em;background:var(--sunk);padding:.1em .32em;border-radius:2px}
pre code{background:none;padding:0}

/* tables */
.tw{overflow-x:auto;margin:1.4rem 0}
table{border-collapse:collapse;width:100%;font-family:var(--sans);font-size:.87rem;
  font-variant-numeric:tabular-nums}
th{text-align:left;font-weight:600;font-size:.72rem;letter-spacing:.08em;text-transform:uppercase;
  color:var(--muted);border-bottom:1px solid var(--ink);padding:.5rem .6rem}
td{padding:.5rem .6rem;border-bottom:1px solid var(--line);color:var(--ink-2)}
tr:hover td{background:var(--sunk)}

@media (max-width:640px){body{font-size:16px}.wrap{padding:0 1.1rem 4rem}}
@media print{
  .bar{display:none}body{background:#fff;font-size:11pt}
  .part{break-before:page}pre.board,p.wb,.tw{break-inside:avoid}
}
</style>
"""

HEAD = """
<div class="bar"><div><b>Two bites at R(3,k)</b><span style="margin-right:.4rem">parts</span>%s</div></div>
<div class="wrap">
<header class="mast">
  <p class="kicker">Speaker's script · 2 hours · whiteboard</p>
  <h1><em>Improving R(3,k)</em> in just two bites</h1>
  <p class="by">Zion Hefty, Paul Horn, Dylan King, Florian Pfender — arXiv:2510.19718, October 2025</p>
  <div class="facts"><span>1 Sept 2026, 14:00–16:00</span><span>No background assumed</span>
  <span>Break at 15:08</span><span>Red rule = say this aloud</span></div>
</header>
""" % nav

open('/home/user/triangle-free-process/talk.html','w').write(CSS + HEAD + body + "\n</div>\n")
print('ok', len(CSS+HEAD+body))
