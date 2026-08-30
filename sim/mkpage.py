import json, html
D = json.load(open('script.json'))

HEAD = r"""<title>Talk Teleprompter</title>
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Spectral:ital,wght@0,300;0,400;0,600;1,400&family=IBM+Plex+Mono:wght@400;500&family=IBM+Plex+Sans:wght@400;500;600&display=swap">
<style>
:root{
  --bg:#F6F7FA; --surface:#FFFFFF; --sunk:#EEF1F6; --dim:#E4E8EF;
  --ink:#171B24; --ink-2:#39414F; --muted:#69728A; --line:#DDE2EB;
  --red:#AE3A31; --red-soft:#F6ECEA; --blue:#2B5CA5; --blue-soft:#EAF0F9;
  --ok:#2E6B4F; --warn:#8A6212; --warn-soft:#F8F0DC;
  --serif:"Spectral",Georgia,serif; --sans:"IBM Plex Sans",system-ui,sans-serif;
  --mono:"IBM Plex Mono",ui-monospace,Menlo,monospace;
}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){
  --bg:#111419; --surface:#181C23; --sunk:#1E232C; --dim:#242A34;
  --ink:#E6E9EF; --ink-2:#C3C9D5; --muted:#939CAF; --line:#2A303B;
  --red:#E58377; --red-soft:#2A1D1B; --blue:#84AAE6; --blue-soft:#161F2C;
  --ok:#7FC0A0; --warn:#D6AC5A; --warn-soft:#241F14;
}}
:root[data-theme="dark"]{
  --bg:#111419; --surface:#181C23; --sunk:#1E232C; --dim:#242A34;
  --ink:#E6E9EF; --ink-2:#C3C9D5; --muted:#939CAF; --line:#2A303B;
  --red:#E58377; --red-soft:#2A1D1B; --blue:#84AAE6; --blue-soft:#161F2C;
  --ok:#7FC0A0; --warn:#D6AC5A; --warn-soft:#241F14;
}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font-family:var(--serif);line-height:1.6}
.wrap{max-width:46rem;margin:0 auto;padding:2.5rem 1.4rem 13rem}
h1{font-size:1.9rem;font-weight:600;margin:0 0 .3rem;letter-spacing:-.015em}
.sub{font-family:var(--sans);font-size:.86rem;color:var(--muted);margin:0 0 1.6rem}
.hint{font-family:var(--sans);font-size:.83rem;color:var(--ink-2);background:var(--sunk);
  border:1px solid var(--line);border-radius:3px;padding:.7rem .85rem;margin:0 0 1.6rem}
.hint b{color:var(--ink)}
kbd{font-family:var(--mono);font-size:.78em;background:var(--surface);border:1px solid var(--line);
  border-bottom-width:2px;border-radius:3px;padding:.05em .35em}

/* pacing table */
details{margin:0 0 2rem;border:1px solid var(--line);border-radius:3px;background:var(--surface)}
summary{font-family:var(--sans);font-size:.85rem;font-weight:600;padding:.7rem .85rem;cursor:pointer}
summary::marker{color:var(--muted)}
table{border-collapse:collapse;width:100%;font-family:var(--sans);font-size:.82rem;
  font-variant-numeric:tabular-nums}
th{text-align:right;font-size:.68rem;letter-spacing:.08em;text-transform:uppercase;color:var(--muted);
  padding:.45rem .85rem;border-bottom:1px solid var(--line)}
th:first-child,td:first-child{text-align:left}
td{padding:.4rem .85rem;border-bottom:1px solid var(--line);color:var(--ink-2);text-align:right}
tr:last-child td{border-bottom:0}
.bar{display:inline-block;height:.45rem;border-radius:2px;background:var(--red);vertical-align:middle}
.bar.rest{background:var(--dim)}
td.tight{color:var(--warn);font-weight:600}

/* script items */
.it{margin:0 0 1.1rem;padding:.35rem .9rem;border-left:3px solid transparent;border-radius:2px;
  transition:background .18s,border-color .18s}
.it.say{font-size:1.12rem;color:var(--ink-2)}
.it.cur{border-left-color:var(--red);background:var(--red-soft);color:var(--ink)}
.it.done{opacity:.42}
.it.part{border-left:0;margin:3rem 0 1.2rem;padding:1rem 0 0;border-top:2px solid var(--ink)}
.it.part h2{font-size:1.35rem;margin:.2rem 0 0;font-weight:600}
.it.part .t{font-family:var(--mono);font-size:.78rem;color:var(--red)}
.it.sub{font-family:var(--sans);font-weight:600;font-size:.95rem;color:var(--ink);margin-top:1.8rem}
.it.wb{background:var(--blue-soft);border:1px solid color-mix(in srgb,var(--blue) 22%,transparent);
  border-left-width:3px;border-left-color:var(--blue);font-family:var(--sans);font-size:.88rem;
  color:var(--ink-2);padding:.65rem .85rem}
.it.wb .lab{display:block;font-size:.64rem;letter-spacing:.15em;text-transform:uppercase;
  color:var(--blue);font-weight:600;margin-bottom:.2rem}
.it.note{font-family:var(--sans);font-size:.82rem;color:var(--muted)}
.it.brk{background:var(--warn-soft);color:var(--warn);font-family:var(--sans);font-weight:600;
  font-size:.9rem;text-align:center;border-radius:3px;padding:.8rem}
pre{background:var(--sunk);border:1px solid var(--line);border-radius:3px;padding:.8rem .9rem;
  overflow-x:auto;margin:0 0 1.1rem;font-family:var(--mono);font-size:.78rem;line-height:1.55;
  color:var(--ink)}

/* control bar */
.ctl{position:fixed;left:0;right:0;bottom:0;background:color-mix(in srgb,var(--surface) 94%,transparent);
  backdrop-filter:blur(10px);border-top:1px solid var(--line);font-family:var(--sans);z-index:10}
.ctl .in{max-width:46rem;margin:0 auto;padding:.7rem 1.4rem .9rem;display:flex;flex-wrap:wrap;
  gap:.6rem .8rem;align-items:center}
button{font-family:var(--sans);font-size:.85rem;font-weight:500;color:var(--ink);background:var(--surface);
  border:1px solid var(--line);border-radius:3px;padding:.4rem .7rem;cursor:pointer}
button:hover{background:var(--sunk)}
button:focus-visible{outline:2px solid var(--blue);outline-offset:1px}
button.play{background:var(--red);border-color:var(--red);color:#fff;min-width:5.5rem;font-weight:600}
button.play:hover{filter:brightness(1.08);background:var(--red)}
select,input[type=range]{font-family:var(--sans);font-size:.8rem;color:var(--ink);
  background:var(--surface);border:1px solid var(--line);border-radius:3px;padding:.3rem}
input[type=range]{padding:0;width:6rem;accent-color:var(--red)}
label.f{font-size:.78rem;color:var(--muted);display:flex;align-items:center;gap:.35rem}
.clock{margin-left:auto;font-family:var(--mono);font-size:.85rem;color:var(--ink);
  font-variant-numeric:tabular-nums}
.clock span{color:var(--muted)}
.pos{flex-basis:100%;font-size:.75rem;color:var(--muted);margin-top:-.2rem}
.nosupport{background:var(--warn-soft);color:var(--warn);padding:.6rem .85rem;border-radius:3px;
  font-family:var(--sans);font-size:.82rem;margin-bottom:1.5rem}
.prose{padding:.1rem 1rem 1.1rem;font-family:var(--sans);font-size:.85rem;color:var(--ink-2)}
.prose ul{padding-left:1.1rem;margin:.6rem 0}
.prose li{margin:.4rem 0}
.prose b{color:var(--ink)}
.prose i{color:var(--ink-2)}
.prose pre{font-size:.78rem;margin:.6rem 0}
.prose code{font-family:var(--mono);background:var(--sunk);padding:.05em .3em;border-radius:2px;font-size:.9em}
.foot{font-family:var(--sans);font-size:.8rem;color:var(--muted);padding:.2rem .85rem .9rem;margin:0}
optgroup{font-style:normal;font-weight:600}
#voice{max-width:11rem}
.ctl .in{row-gap:.55rem}
@media(max-width:640px){.wrap{padding:1.6rem 1rem 17rem}.it.say{font-size:1.05rem}
  .clock{margin-left:0}.pos{margin-top:0}}
</style>"""

items = D['items']; allot = D['allot']; words = D['words']

rows = []
tot_w = tot_s = 0
for k in sorted(allot):
    w = words.get(k, 0); sp = w / 145.0; slot = allot[k]; slack = slot - sp
    tot_w += w; tot_s += slot
    pct = max(2, min(100, round(100 * sp / slot)))
    cls = ' class="tight"' if slack < 2 else ''
    rows.append(
        '<tr><td>%s</td><td>%d</td><td>%.1f</td><td>%d</td><td%s>%.1f</td>'
        '<td style="width:7rem"><span class="bar" style="width:%d%%"></span>'
        '<span class="bar rest" style="width:%d%%"></span></td></tr>'
        % (k, w, sp, slot, cls, slack, pct, 100 - pct))
rows.append('<tr><td><b>Total</b></td><td><b>%d</b></td><td><b>%.0f</b></td><td><b>%d</b></td>'
            '<td><b>%.0f</b></td><td></td></tr>' % (tot_w, tot_w/145.0, tot_s, tot_s - tot_w/145.0))

body = []
for n, x in enumerate(items):
    k = x['k']; t = html.escape(x['t'])
    if k == 'part':
        body.append('<div class="it part" id="i%d" data-i="%d"><span class="t">%s · %s</span>'
                    '<h2>%s</h2></div>' % (n, n, x['time'], html.escape(x['n']), t))
    elif k == 'sub':
        body.append('<div class="it sub" id="i%d" data-i="%d">%s</div>' % (n, n, t))
    elif k == 'say':
        body.append('<div class="it say" id="i%d" data-i="%d">%s</div>' % (n, n, t))
    elif k == 'wb':
        import re as _re
        def _lab(m):
            g = m.group(1).strip()
            return ('<b>%s</b> \u2014 ' % g) if g else ''
        lab = _re.sub(r'^\[WB\s*[\u2014\-]?\s*([^\]]*)\]\s*', _lab, t)
        body.append('<div class="it wb" id="i%d" data-i="%d"><span class="lab">Whiteboard</span>%s</div>'
                    % (n, n, lab))
    elif k == 'board':
        body.append('<pre id="i%d" data-i="%d">%s</pre>' % (n, n, t))
    elif k == 'note':
        body.append('<div class="it note" id="i%d" data-i="%d">%s</div>' % (n, n, t))
    elif k == 'brk' or k == 'break':
        body.append('<div class="it brk" id="i%d" data-i="%d">%s</div>' % (n, n, t))

SPEECH = [{'i': n, 's': x['s'], 'p': x.get('p', '')} for n, x in enumerate(items) if x['k'] == 'say']


# ---- plain-text script for external / neural TTS ----
txt = []
for x in items:
    if x['k'] == 'part': txt.append('\n\n[%s — %s]\n' % (x['n'], x['t']))
    elif x['k'] == 'break': txt.append('\n[BREAK]\n')
    elif x['k'] == 'say': txt.append(x['s'] + '\n')
open('/home/user/triangle-free-process/script-spoken.txt', 'w').write('\n'.join(txt))

PAGE = HEAD + """
<div class="wrap">
<h1>Talk teleprompter</h1>
<p class="sub">Improving R(3,k) in just two bites — 1 Sept 2026, 14:00–16:00. Press play and listen; the script scrolls itself.</p>
<div id="ns"></div>
<p class="hint"><b>How to use it:</b> <kbd>space</kbd> play / pause, <kbd>←</kbd> <kbd>→</kbd> skip a paragraph, or click any
paragraph to start from there. Only the spoken lines are read aloud — whiteboard cues and board panels scroll past in
silence, which is roughly what your audience will experience while you're drawing.</p>

<details id="vt"><summary>The voice sounds robotic — how to fix that</summary>
<div class="prose">
<p>The voice comes from your browser, not from this page, and the built-in default is usually the worst one installed.
The picker below is sorted best-first and labelled; if the <b>Most natural</b> group is empty, your browser has only basic
voices and it's worth spending two minutes installing better ones:</p>
<ul>
<li><b>Windows</b> — open this page in <b>Edge</b>. It exposes “Microsoft … Online (Natural)” voices (Aria, Guy, Emma) that are
near-human and free. Or add them system-wide: Settings → Time&nbsp;&amp;&nbsp;Language → Speech → Manage voices.</li>
<li><b>macOS</b> — System Settings → Accessibility → Spoken Content → System Voice → <i>Manage Voices…</i>, and download a
<b>Premium</b> or <b>Siri</b> English voice (Ava, Zoe, Evan). Then use <b>Safari</b>: Chrome on macOS often hides the
premium voices, Safari lists them.</li>
<li><b>Android / iOS</b> — Chrome and Safari both expose the system voices; install a “natural” voice pack in the OS
text-to-speech settings.</li>
</ul>
<p>If you want a genuinely broadcast-quality read — for rehearsing with headphones on a walk — take
<code>script-spoken.txt</code> (the plain, maths-normalised script) and run it through a neural TTS. On macOS you can do
it locally with no account:</p>
<pre>say -v "Ava (Premium)" -f script-spoken.txt -o talk.aiff</pre>
<p>Everything below the voice picker — the pauses between sentences, the breath between paragraphs, the speed — is this
page's doing, and those matter about as much as the voice itself.</p>
</div>
</details>

<details><summary>Pacing check — where the time actually goes</summary>
<table><thead><tr><th>Part</th><th>Words</th><th>Speaking</th><th>Slot</th><th>Slack</th><th></th></tr></thead>
<tbody>""" + ''.join(rows) + """</tbody></table>
<p class="foot">Minutes, at 145 words per minute. “Slack” is what's left for drawing, pauses and questions —
the red bar is talking, the grey bar is everything else.</p>
</details>

""" + '\n'.join(body) + """
</div>

<div class="ctl"><div class="in">
  <button id="prev" title="Previous paragraph">◀</button>
  <button class="play" id="play">▶ Play</button>
  <button id="next" title="Next paragraph">▶</button>
  <label class="f">Voice <select id="voice"></select></label>
  <button id="test" title="Hear a sample line">Test</button>
  <label class="f">Speed <input type="range" id="rate" min="0.7" max="1.4" step="0.05" value="0.95"><span id="rateV">0.95×</span></label>
  <label class="f">Pitch <input type="range" id="pitch" min="0.8" max="1.2" step="0.05" value="1"></label>
  <label class="f">Breath <select id="gap"><option value="1">natural</option><option value="1.8">slow</option><option value="0.4">brisk</option></select></label>
  <label class="f"><input type="checkbox" id="stopwb"> pause at board work</label>
  <span class="clock" id="clock">00:00 <span>/ ~47m</span></span>
  <div class="pos" id="pos">Ready — Part 0, paragraph 1 of """ + str(len(SPEECH)) + """</div>
</div></div>

<script>
const SP = """ + json.dumps(SPEECH, ensure_ascii=False) + """;
const WORDS = """ + str(tot_w) + """;
const synth = window.speechSynthesis;
let idx = 0, playing = false, voices = [], chunks = [], ci = 0, t0 = null, elapsed = 0, tick = null, keepAlive = null;
const $ = s => document.querySelector(s);

if (!synth) $('#ns').innerHTML = '<div class="nosupport">This browser has no speech synthesis, so nothing will be read aloud. The page still works as a scroll-along teleprompter.</div>';

function fmt(ms){const s=Math.floor(ms/1000);return String(Math.floor(s/60)).padStart(2,'0')+':'+String(s%60).padStart(2,'0');}
function est(){ return Math.round(WORDS / (145 * parseFloat($('#rate').value))); }
function showClock(ms){ $('#clock').innerHTML = fmt(ms) + ' <span>/ ~' + est() + 'm</span>'; }

/* rank voices: the built-in default is usually the worst one installed */
function rank(v){
  const n = v.name + ' ' + (v.voiceURI||'');
  let s = 0;
  if(/natural|neural|premium|enhanced|siri/i.test(n)) s += 4;
  if(/\\b(ava|zoe|evan|allison|samantha|serena|daniel|karen|moira|tessa|fiona|nicky|aaron|joelle)\\b/i.test(n)) s += 2;
  if(/google/i.test(n)) s += 2;
  if(v.localService === false) s += 1;
  if(/espeak|compact|eloquence|pico|festival/i.test(n)) s -= 4;
  return s;
}
function loadVoices(){
  if(!synth) return;
  const all = synth.getVoices().filter(v => v.lang && v.lang.toLowerCase().startsWith('en'));
  if(!all.length) return;
  voices = all.map(v => ({v, s: rank(v)})).sort((a,b) => b.s - a.s || a.v.name.localeCompare(b.v.name)).map(o => o.v);
  const sel = $('#voice'); const keep = sel.value; sel.innerHTML = '';
  const groups = [['Most natural', v => rank(v) >= 4], ['Good', v => rank(v) >= 2 && rank(v) < 4], ['Basic', v => rank(v) < 2]];
  groups.forEach(([label, test]) => {
    const list = voices.filter(test); if(!list.length) return;
    const g = document.createElement('optgroup'); g.label = label;
    list.forEach(v => { const o = document.createElement('option');
      o.value = voices.indexOf(v);
      o.textContent = v.name.replace(/\\s*\\(.*?\\)\\s*$/, '') + (v.lang.match(/GB/i) ? ' · UK' : '');
      g.appendChild(o); });
    sel.appendChild(g);
  });
  sel.value = keep && voices[keep] ? keep : 0;
  if(rank(voices[0]) < 4) $('#vt').open = true;   // nudge them to install a better one
}
if(synth){ loadVoices(); synth.onvoiceschanged = loadVoices; }

function mark(){
  document.querySelectorAll('.it.cur').forEach(e => e.classList.remove('cur'));
  const el = document.getElementById('i' + SP[idx].i); if(!el) return;
  el.classList.add('cur');
  document.querySelectorAll('[data-i]').forEach(e => e.classList.toggle('done', playing && +e.dataset.i < SP[idx].i));
  el.scrollIntoView({behavior:'smooth', block:'center'});
  $('#pos').textContent = SP[idx].p + ' — paragraph ' + (idx+1) + ' of ' + SP.length;
}
/* one utterance per sentence, so the engine phrases instead of droning */
function split(t){
  const sents = t.match(/[^.!?:;]+[.!?:;]*\\s*/g) || [t];
  const out = []; let cur = '';
  sents.forEach(s => { s = s.trim(); if(!s) return;
    if(cur && (cur + ' ' + s).length > 150){ out.push(cur); cur = s; } else cur = cur ? cur + ' ' + s : s; });
  if(cur) out.push(cur); return out;
}
/* a breath after full stops, a shorter one after commas — this is most of what "natural" means */
function gapFor(c){
  if(!c) return 120;
  const last = c.trim().slice(-1);
  const base = '.!?'.includes(last) ? 300 : (',;:'.includes(last) ? 150 : 120);
  return base * parseFloat($('#gap').value) / parseFloat($('#rate').value);
}
function dress(u){
  if(voices.length) u.voice = voices[$('#voice').value] || voices[0];
  u.rate = parseFloat($('#rate').value);
  u.pitch = parseFloat($('#pitch').value);
  return u;
}
function speak(){
  if(!synth || !playing) return;
  if(ci >= chunks.length){ advance(); return; }
  const u = dress(new SpeechSynthesisUtterance(chunks[ci]));
  const done = () => { const prev = chunks[ci]; ci++; if(playing) setTimeout(speak, gapFor(prev)); };
  u.onend = done; u.onerror = done;
  synth.speak(u);
}
function load(i){ idx = Math.max(0, Math.min(SP.length-1, i)); chunks = split(SP[idx].s); ci = 0; mark(); }
function advance(){
  if(idx + 1 >= SP.length){ stop(); $('#pos').textContent = 'End of talk.'; return; }
  const from = SP[idx].i, to = SP[idx+1].i;
  load(idx + 1);
  if($('#stopwb').checked){
    for(let n = from + 1; n < to; n++){ const e = document.getElementById('i' + n);
      if(e && (e.classList.contains('wb') || e.tagName === 'PRE')){ stop(); return; } }
  }
  setTimeout(speak, 650 / parseFloat($('#rate').value));   // breath between paragraphs
}
function start(){
  playing = true; $('#play').textContent = '⏸ Pause'; t0 = Date.now();
  tick = setInterval(() => showClock(elapsed + (Date.now() - t0)), 500);
  keepAlive = setInterval(() => { if(playing && !synth.paused){ synth.pause(); synth.resume(); } }, 10000);
  speak();
}
function stop(){
  playing = false; $('#play').textContent = '▶ Play';
  if(synth) synth.cancel();
  if(t0){ elapsed += Date.now() - t0; t0 = null; }
  clearInterval(tick); clearInterval(keepAlive);
  document.querySelectorAll('.done').forEach(e => e.classList.remove('done'));
}
$('#play').onclick = () => playing ? stop() : (ci = 0, start());
$('#next').onclick = () => { const p = playing; stop(); load(idx + 1); if(p) start(); };
$('#prev').onclick = () => { const p = playing; stop(); load(idx - 1); if(p) start(); };
$('#test').onclick = () => { if(!synth) return; const p = playing; stop();
  synth.speak(dress(new SpeechSynthesisUtterance(
    'Every triangle-free graph on n vertices has an independent set of size root n log n. That is the whole game.'))); };
$('#rate').oninput = e => { $('#rateV').textContent = (+e.target.value).toFixed(2) + '×'; showClock(elapsed); };
$('#rate').onchange = $('#pitch').onchange = $('#voice').onchange = () => { if(playing){ stop(); start(); } };
document.querySelectorAll('.it.say').forEach(el => el.onclick = () => {
  const j = SP.findIndex(s => s.i === +el.dataset.i); if(j < 0) return;
  const p = playing; stop(); load(j); if(p) start();
});
document.addEventListener('keydown', e => {
  if(e.target.tagName === 'SELECT' || e.target.tagName === 'INPUT') return;
  if(e.code === 'Space'){ e.preventDefault(); $('#play').click(); }
  if(e.code === 'ArrowRight'){ e.preventDefault(); $('#next').click(); }
  if(e.code === 'ArrowLeft'){ e.preventDefault(); $('#prev').click(); }
});
window.addEventListener('beforeunload', () => { if(synth) synth.cancel(); });
load(0); showClock(0);
</script>
"""
open('/home/user/triangle-free-process/listen.html','w').write(PAGE)
print('written', len(PAGE), 'bytes;', len(SPEECH), 'spoken blocks')
