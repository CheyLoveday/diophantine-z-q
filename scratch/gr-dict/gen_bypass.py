"""gr-dict: generate scratch/gr-dict/BypassFold.lean, the bypass fold that removes `gonzalezRotgerProp56X6`.

Adapted from scratch/st-qbar/gen_bypass.py. Every research-bundle generation on the live path of
`sixContactMin_of_open35` (and `ResearchLeaves3`) is copied with suffix `S`, with its count field
(`gonzalezRotgerProp56X6`, `gonzalezRotgerCountX6Ab`, `gonzalezRotgerCountX6` or `r5count`) replaced by
`r5le : GR56.R5fpCountLe`; every theorem on the path whose signature mentions one of them is copied verbatim
with suffix `_S`, the forwarding line of the count field replaced by `r5le := <bundle>.r5le`, and TailK's consumer
`FS5NoCM.fibreComTrivialFull_of_leaves'' … r.r5count` replaced by gr56-prove's
`FS5NoCM.fibreComTrivialFull_of_leaves''_le … r.r5le`. The new top bundle `OpenResearchLeaves26E` is
`OpenResearchLeaves26` with `gonzalezRotgerProp56X6` replaced by `eichlerOptEmbCount6`; it maps to
`OpenResearchLeaves26S` by `GR56.r5fpCountLe_of_eichler` and the three textbook fields."""
import re, glob, collections, sys
H = 'ZInQKernel/OneProof/H/'
FIELDS = ('gonzalezRotgerProp56X6', 'gonzalezRotgerCountX6Ab', 'gonzalezRotgerCountX6', 'r5count')
START = re.compile(r'^(private )?(theorem|structure|def|noncomputable def|abbrev|lemma) ([A-Za-z_][\w\'.]*)')
STOP = re.compile(r'^(private |@\[|theorem|lemma|structure|def|noncomputable|abbrev|end |namespace |section |/-|open |set_option|variable|#|attribute|instance|export|universe)')
blocks = collections.defaultdict(list)
fileopens = collections.defaultdict(list)
for fn in sorted(glob.glob(H + '*.lean')) + ['ZInQKernel/Contrib/OneProof/SGRFold.lean']:
    L = open(fn).read().split('\n')
    ns = []
    scopes = [[]]
    i = 0
    while i < len(L):
        l = L[i]
        m0 = re.match(r'^namespace (\S+)$', l)
        if m0: ns.append(m0.group(1)); scopes.append([])
        if re.match(r'^(noncomputable )?section( \S+)?$', l): scopes.append([])
        m1 = re.match(r'^end( \S+)?$', l)
        if m1:
            if len(scopes) > 1: scopes.pop()
            if m1.group(1) and ns and ns[-1] == m1.group(1).strip(): ns.pop()
        if re.match(r'^open \S', l) and not l.rstrip().endswith(' in'):
            ol = [l.rstrip()]
            k = i + 1
            while k < len(L) and L[k].startswith('  ') and not START.match(L[k]):
                ol.append(L[k].rstrip()); k += 1
            scopes[-1].append('\n'.join(ol))
        m = START.match(l)
        if m:
            j = i + 1
            while j < len(L) and not STOP.match(L[j]):
                j += 1
            pre = L[i - 1] if i > 0 and re.match(r'^open .* in$', L[i - 1]) else None
            blocks[m.group(3)].append(dict(fn=fn, ln=i + 1, ns='.'.join(ns), pre=pre, opens=[o for sc in scopes for o in sc],
                                           text='\n'.join(L[i:j]).rstrip()))
            i = j
        else:
            i += 1

def struct_has_field(text):
    return any(re.search(r'^  ' + f + r' :', text, re.M) for f in FIELDS)

SN = [n for n, b in blocks.items() if b[0]['text'].startswith('structure') and
      re.match(r'(Open)?ResearchLeaves\d*$', n) and struct_has_field(b[0]['text'])]

def sig(text):
    return re.split(r':=| where', text, 1)[0]

def mentions(text, names):
    return any(re.search(r'(?<![\w])' + re.escape(s) + r'(?![\w\'])', text) for s in names)

TOP = 'sixContactMin_of_open35'
todo = [TOP]
copied = []
while todo:
    n = todo.pop()
    if n in copied:
        continue
    copied.append(n)
    text = blocks[n][0]['text']
    ids = set()
    for q in re.findall(r'(?<![\w.])[A-Za-z_][\w\'.]*[\w\']', text):
        ids.add(q); ids.add(q.split('.')[-1])
    for ident in ids:
        if ident in blocks and ident not in copied and ident != n:
            b = blocks[ident][0]['text']
            if b.split()[0] in ('theorem', 'def', 'lemma') and mentions(sig(b), SN):
                todo.append(ident)
for n in copied:
    if len(blocks[n]) > 1:
        sys.exit('ambiguous name ' + n)
used_structs = sorted({s for n in copied for s in SN if mentions(blocks[n][0]['text'], [s])},
                      key=lambda s: (blocks[s][0]['fn'], blocks[s][0]['ln']))

for s_ in used_structs:
    for nm in list(blocks):
        if nm.startswith(s_ + '.') and nm not in copied:
            copied.append(nm)
rename = {s: s + 'S' for s in used_structs}
for n in copied:
    if '.' not in n:
        rename[n] = n + '_S'

def do_rename(text):
    for a, b in rename.items():
        text = re.sub(r'(?<![\w])' + re.escape(a) + r'(?![\w\'])', b, text)
    return text

def replace_field_lines(text):
    L = text.split('\n')
    out = []
    i = 0
    n_rep = 0
    while i < len(L):
        l = L[i]
        m = re.match(r'^(\s+)(' + '|'.join(FIELDS) + r') :=(.*)$', l)
        if m:
            ind = m.group(1)
            chunk = [l]
            j = i + 1
            while j < len(L) and len(L[j]) - len(L[j].lstrip()) > len(ind) and L[j].strip():
                chunk.append(L[j]); j += 1
            c = '\n'.join(chunk)
            v = re.search(r'(?<![\w.])(\w+)\.(' + '|'.join(FIELDS) + r')\b', c)
            if not v:
                sys.exit('no source bundle in ' + c)
            comma = ',' if c.rstrip().endswith(',') else ''
            out.append(f'{ind}r5le := {v.group(1)}.r5le{comma}')
            n_rep += 1
            i = j
            continue
        out.append(l)
        i += 1
    return '\n'.join(out), n_rep

def struct_copy(s):
    L = blocks[s][0]['text'].split('\n')
    out = [L[0]]
    pending = []
    i = 1
    while i < len(L):
        l = L[i]
        if l.lstrip().startswith('/--'):
            doc = [l]
            while '-/' not in L[i]:
                i += 1
                doc.append(L[i])
            pending = doc
            i += 1
            continue
        m = re.match(r'^  (' + '|'.join(FIELDS) + r') :', l)
        if m:
            i += 1
            while i < len(L) and L[i].startswith('    ') and not L[i].lstrip().startswith('/--'):
                i += 1
            out.append(f'  /-- gr-dict bypass: replaces `{m.group(1)}`; the upper bound `#CM(R) ≤ 2^b·h(R)`, the only')
            out.append('  half of the count the chain reads (`FS5NoCM.nocm_on_witness`). -/')
            out.append('  r5le : _root_.GR56.R5fpCountLe')
            pending = []
            continue
        out += pending + [l]
        pending = []
        i += 1
    return do_rename('\n'.join(out))

def file_rank(fn):
    base = fn.split('/')[-1]
    order = ['LPrefix', 'TailA', 'TailB', 'TailC', 'TailD', 'TailE', 'TailF', 'TailG', 'TailH', 'TailI', 'TailJ',
             'TailK', 'TailL', 'TailM', 'TailN', 'TailO', 'TailP', 'TailQ', 'TailR', 'TailS', 'TailT', 'TailU',
             'TailV', 'TailW', 'TailX', 'TailY', 'TailZ']
    stem = base[:-5]
    if stem == 'SGRFold':
        return (len(order), 38.5)
    m = re.match(r'TailZ(\d+)$', stem)
    if m:
        return (len(order), int(m.group(1)))
    return (order.index(stem), 0)

items = [(file_rank(blocks[n]['fn'] if False else blocks[n][0]['fn']), blocks[n][0]['ln'], 'thm', n) for n in copied]
items += [(file_rank(blocks[s][0]['fn']), blocks[s][0]['ln'], 'struct', s) for s in used_structs]
items.sort()

opens = ['open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj',
         'open NumberField']

hdr = '''import ZInQKernel.OneProof.H.TailZ42
import ZInQKernel.OneProof.TYZSplit
import ZInQKernel.OneProof.TopChain
import ZInQKernel.Contrib.TYZChain.Main
import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2
import ZInQKernel.Contrib.OneProof.FHNonvanishing
import ZInQKernel.Contrib.OneProof.ThetaWeierstrass8
import ZInQKernel.Contrib.OneProof.GR56Lattice

/-! # gr-dict: the bypass fold that removes `gonzalezRotgerProp56X6` (generated by `scratch/gr-dict/gen_bypass.py`)

The chain reads González–Rotger's count only as the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` in
`FS5NoCM.nocm_on_witness` (TailC), through the field `r5count : R5fpCount` of the research bundles of generations
2..8, which generations 9..26 fill from `gonzalezRotgerCountX6`, `gonzalezRotgerCountX6Ab` and
`gonzalezRotgerProp56X6`. gr56-prove proved the bound from Eichler's count and three textbook fields
(`GR56.r5fpCountLe_of_eichler`). A weaker field cannot fill `r5count`, so this module copies each research
generation on the live path (suffix `S`) with the count field replaced by `r5le : GR56.R5fpCountLe`, and every map
on the path that takes one (suffix `_S`, verbatim but for the forwarding line `r5le := _.r5le` and TailK's consumer).
-/

set_option linter.all false
set_option maxHeartbeats 1000000

namespace HDec

namespace HSyn

'''
parts = [hdr]
cur_ns = 'HDec.HSyn'
def switch(ns):
    global cur_ns
    out = []
    if ns == cur_ns:
        return out
    a = cur_ns.split('.'); b = ns.split('.')
    k = 0
    while k < min(len(a), len(b)) and a[k] == b[k]:
        k += 1
    for x in reversed(a[k:]):
        out.append(f'end {x}\n')
    for x in b[k:]:
        out.append(f'namespace {x}\n')
    cur_ns = ns
    return out
counts = {}
for _, ln, kind, n in items:
    b = blocks[n][0]
    ns = b['ns'] if b['ns'].startswith('HDec') and '`' not in b['ns'] else 'HDec.HSyn'
    parts += switch(ns)
    if kind == 'struct':
        parts.append(f'-- copied from {b["fn"]} L{b["ln"]}, count field replaced by `r5le`')
        parts.append(struct_copy(n) + '\n')
        continue
    t, k = replace_field_lines(b['text'])
    counts[n] = k
    if n == 'gluePieces_of_open4':
        assert "FS5NoCM.fibreComTrivialFull_of_leaves''" in t and 'r.r5count)' in t
        t = t.replace("FS5NoCM.fibreComTrivialFull_of_leaves''", "FS5NoCM.fibreComTrivialFull_of_leaves''_le")
        t = t.replace('r.r5count)', 'r.r5le)')
    if re.search(r'\.(' + '|'.join(FIELDS) + r')\b', t):
        sys.exit('unreplaced read of a count field in ' + n)
    parts.append(f'-- copied from {b["fn"]} L{b["ln"]}')
    parts.append('section')
    parts += b['opens']
    if b['pre']:
        parts.append(b['pre'])
    parts.append(do_rename(t) + '\n')
    parts.append('end\n')
parts += switch('HDec.HSyn')
top26 = blocks['OpenResearchLeaves26'][0]
parts.append('''/-- **The next research bundle** (gr-dict): `OpenResearchLeaves26` with `gonzalezRotgerProp56X6` replaced by
Eichler's count `eichlerOptEmbCount6`. -/''')
L = struct_copy('OpenResearchLeaves26').split('\n')
L[0] = 'structure OpenResearchLeaves26E : Prop where'
txt = '\n'.join(L)
txt = re.sub(r'  /-- gr-dict bypass: replaces.*?\n.*?-/\n  r5le : _root_.GR56.R5fpCountLe',
             '''  /-- gr-dict, printed form (Eichler 1955; Vignéras LNM 800 III.5.11-5.12; Voight 30.7.3; numbers UNVERIFIED):
  the number of `𝒪^×`-classes of optimal embeddings of an order `R` of conductor prime to 6 in an imaginary
  quadratic field into the maximal order of `B = (2, −3 | ℚ)` is `h(R) ∏_{p ∣ 6} (1 − (k/p))`. Replaces
  `gonzalezRotgerProp56X6` (bypass: the chain needs only the upper bound, `GR56.r5fpCountLe_of_eichler`). -/
  eichlerOptEmbCount6 : _root_.GRCountX6.EichlerOptEmbCount6''', txt, flags=re.S)
parts.append(txt + '\n')
fields26 = re.findall(r'^  ([A-Za-z_][\w\']*) :', blocks['OpenResearchLeaves26'][0]['text'], re.M)
lines = ['/-- `OpenResearchLeaves26S` from `OpenResearchLeaves26E`: the bound from Eichler and the textbook fields. -/',
         'theorem openResearchLeaves26S_of_26E (n : OpenResearchLeaves26E) (t : OpenTextbookLeaves12) :',
         '    OpenResearchLeaves26S where']
for f in fields26:
    if f == 'gonzalezRotgerProp56X6':
        lines.append('  r5le := _root_.GR56.r5fpCountLe_of_eichler n.eichlerOptEmbCount6 t.uniformizationLeafAll')
        lines.append('    t.gagaMorphism t.mumfordTorsionAlgClosed')
    else:
        lines.append(f'  {f} := n.{f}')
parts.append('\n'.join(lines) + '\n')
parts.append('''/-- **G0 without `gonzalezRotgerProp56X6`** (gr-dict bypass fold). -/
theorem sixContactMin_of_open35E (r : OpenResearchLeaves26E) (t : OpenTextbookLeaves12) (l : OpenAddedLeaves17)
    (g : OpenGlue8) : ZInQ.SixContactMin :=
  sixContactMin_of_open35_S (openResearchLeaves26S_of_26E r t) t l g

end HSyn

end HDec

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- `ZInQ.OneProof.frozenTarget` (Main.lean) with `OpenResearchLeaves26E` (no `gonzalezRotgerProp56X6`; Eichler's
count instead). -/
theorem frozenTarget_E
    (r : HDec.HSyn.OpenResearchLeaves26E) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8)
    (h11 : TYZThm11Integral)
    (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hT21 : H29Split.TYZThm21At31) (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open35E r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves hL3s hJP hfx hL29 hT21 hP23) hCM h33)
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3

end ZInQ.Contrib.TYZChain

#print axioms HDec.HSyn.sixContactMin_of_open35E
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_E
''')
out = '\n'.join(parts)
out = out.replace('namespace HDec\n\nnamespace HSyn\n\n', 'namespace HDec\n\nnamespace HSyn\n\n' + '\n'.join(opens) + '\n\n', 1)
open('scratch/gr-dict/BypassFold.lean', 'w').write(out)
print('structs', used_structs)
print('theorems', len(copied), {n: counts.get(n) for n in copied if counts.get(n)})
print('opens', opens)
