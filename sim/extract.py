import re, json

S = open('/home/user/triangle-free-process/TALK.md').read()
lines = S.split('\n')

# ---------- speech normalisation ----------
FRAC = {'1/2':'one half','1/3':'one third','1/4':'one quarter','1/√2':'one over root two',
        '2/3':'two thirds','3/2':'three halves','1/√6':'one over root six','1/160':'one over one sixty',
        '1/(2√2)':'one over two root two','1/(2A²)':'one over two A squared','1/162':'one over one sixty two'}
GREEK = {'α':'alpha','Δ':'Delta','ε':'epsilon','π':'pi','κ':'kappa','β':'beta','ℓ':'ell','σ':'sigma','θ':'theta'}
SYM = {'⟺':' if and only if ','⟹':' which gives ','⇒':' implies ','≈':' approximately ','≥':' at least ',
       '≤':' at most ','≪':' much smaller than ','≫':' much bigger than ','→':' tends to ','∈':' in ',
       '∪':' union ','∩':' intersect ','⊆':' inside ','∼':' is asymptotic to ','·':' times ','×':' by ',
       '∅':' the empty set ','∂':' partial ','Θ':'theta','Ω':'omega','∀':' for all ','∃':' there is '}

def say(t):
    t = re.sub(r'\*\*(.+?)\*\*', r'\1', t)
    t = re.sub(r'\*(.+?)\*', r'\1', t)
    t = re.sub(r'`(.+?)`', r'\1', t)
    t = re.sub(r'\[(.+?)\]\(.+?\)', r'\1', t)
    # named patterns first
    t = re.sub(r'\bR\(([^)]*)\)', lambda m: 'R ' + m.group(1).replace(',', ' '), t)
    t = re.sub(r'\bG\(([^)]*)\)', lambda m: 'G ' + m.group(1).replace(',', ' '), t)
    t = re.sub(r'\bC\((\w+),(\w+)\)', r'\1 choose \2', t)
    t = re.sub(r'\bα\(([^)]*)\)', r'alpha of \1', t)
    t = t.replace('o(1)', 'little oh of one').replace('O(', 'big oh of ')
    t = re.sub(r'√\(([^)]*)\)', r' root \1 ', t)
    t = re.sub(r'√(\w+)', r' root \1 ', t)
    t = t.replace('√', ' root ')
    for k, v in FRAC.items(): t = t.replace(k, v)
    t = t.replace('k²/log k', 'k squared over log k')
    t = re.sub(r'(\S+)\s*/\s*(\S+)',
               lambda m: (m.group(1) + ' over ' + m.group(2))
               if re.search(r'[0-9²³√()]', m.group(1) + m.group(2)) else (m.group(1) + ' ' + m.group(2)), t)
    t = t.replace('²', ' squared ').replace('³', ' cubed ').replace('⁴', ' to the fourth ')
    t = t.replace('⁻', ' minus ').replace('^', ' to the ')
    t = t.replace('_R', ' red ').replace('_B', ' blue ')
    t = re.sub(r'_(\w)', r' sub \1 ', t)
    for k, v in GREEK.items(): t = t.replace(k, v)
    for k, v in SYM.items(): t = t.replace(k, v)
    t = t.replace('—', ', ').replace('–', ', ').replace('‑', '-')
    t = t.replace('−', ' minus ').replace(' ,', ',').replace(' .', '.')
    t = re.sub(r'to the \(([^)]*)\)', r'to the \1', t)
    t = re.sub(r'\s+', ' ', t).strip()
    return t

def disp(t):
    t = t.replace('`', '')
    t = re.sub(r'\*\*(.+?)\*\*', r'\1', t)   # bold first, then italics
    t = re.sub(r'\*(.+?)\*', r'\1', t)
    return t.strip()

# ---------- walk the document ----------
items, part, i = [], None, 0
in_code, code, skip = False, [], False
while i < len(lines):
    L = lines[i]
    if L.startswith('```'):
        if in_code:
            items.append({'k':'board','t':'\n'.join(code),'p':part}); code, in_code = [], False
        else: in_code = True
        i += 1; continue
    if in_code:
        code.append(L); i += 1; continue
    m = re.match(r'^# (Part \d+) — (\d\d:\d\d) — (.+)$', L)
    if m:
        part = m.group(1); skip = False
        items.append({'k':'part','t':m.group(3),'time':m.group(2),'n':part,'p':part}); i += 1; continue
    if re.match(r'^# Appendix', L) or L.startswith('## Practical notes') or L.startswith('## ⚠️'):
        skip = True; i += 1; continue
    if L.startswith('## ☕'):
        items.append({'k':'break','t':'Break — 10 minutes','p':part}); i += 1; continue
    if skip or part is None: i += 1; continue
    if L.startswith('## '):
        items.append({'k':'sub','t':disp(L[3:]),'p':part}); i += 1; continue
    if L.startswith('> '):
        buf = []
        while i < len(lines) and lines[i].startswith('>'):
            buf.append(lines[i].lstrip('>').strip()); i += 1
        txt = ' '.join(x for x in buf if x)
        if txt: items.append({'k':'say','t':disp(txt),'s':say(txt),'p':part})
        continue
    if L.startswith('**[WB'):
        items.append({'k':'wb','t':disp(L),'p':part}); i += 1; continue
    if L.startswith('*(') or L.startswith('**[If') or L.startswith('*(If'):
        items.append({'k':'note','t':disp(L),'p':part}); i += 1; continue
    i += 1

words = sum(len(x['s'].split()) for x in items if x['k'] == 'say')
print('items', len(items), 'spoken blocks', sum(1 for x in items if x['k']=='say'), 'words', words,
      'minutes @145wpm', round(words/145))
ALLOT = {'Part 0':10,'Part 1':15,'Part 2':20,'Part 3':10,'Part 4':13,
         'Part 5':15,'Part 6':22,'Part 7':5}
stats = {}
for x in items:
    if x['k']=='say':
        stats[x['p']] = stats.get(x['p'],0) + len(x['s'].split())
out = {'items':items,'allot':ALLOT,'words':stats}
json.dump(out, open('script.json','w'), ensure_ascii=False)
print('%-8s %6s %7s %7s %8s' % ('part','words','speak','slot','board+Q'))
for k in sorted(ALLOT):
    w = stats.get(k,0); sp = w/145
    print('%-8s %6d %6.1fm %6dm %7.1fm' % (k, w, sp, ALLOT[k], ALLOT[k]-sp))
for x in items[:4] + [y for y in items if y['k']=='say'][20:23]:
    print('---', x['k'], '|', x.get('s', x['t'])[:150])
