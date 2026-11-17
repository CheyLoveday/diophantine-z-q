"""Generate TailZ66 (coeff-field-tc fold, regenerated on main after leaf-fold33 / fold34-eichler / leaf-fold33-batch-w96).

On this base the research bundles that carry the two coeff-rational leaves `gamma1IntegralSpan`,
`heckePrimeIntegralToRational` and lie on frozenTarget's proof are the copies `OpenResearchLeaves32EB`-`38EB`
(EichlerBoundCopy.lean), `OpenResearchLeaves39` (TailZ63) and `OpenResearchLeaves40` (TailZ65). The two leaves are
read only through `_root_.CoeffRational.eigenformCoeffFieldFinite_of_heckePrime n.gamma1IntegralSpan
n.heckePrimeIntegralToRational`, which proves `DSCoeffExt.EigenformCoeffFieldFinite`, now proved outright by
`_root_.eigenformCoeffFieldFinite_proof`.

The module copies those structures and their conversions verbatim up to the renaming
  OpenResearchLeaves<j>EB -> OpenResearchLeaves<j>EBCF (j = 32..38), OpenResearchLeaves39 -> OpenResearchLeaves39CF,
  OpenResearchLeaves40 -> OpenResearchLeaves41, and each conversion name gets the suffix `_cf`,
with the two fields and their pass-through lines deleted and every reading replaced by the proof. The bottom copy
still produces the unchanged `OpenResearchLeaves31EB`, so the new top theorem ends in the unchanged
`sixContactMin_of_open48_eb`. The intermediate `sixContactMin_of_open<N>(_eb)` theorems are not copied: the new
top theorem composes the copied conversions exactly as they do (parsed from their bodies below).
"""
import re, sys

H = sys.argv[1]
FIELDS = ('gamma1IntegralSpan', 'heckePrimeIntegralToRational')
OLD = '_root_.CoeffRational.eigenformCoeffFieldFinite_of_heckePrime n.gamma1IntegralSpan n.heckePrimeIntegralToRational'
NEW = '_root_.eigenformCoeffFieldFinite_proof'


def ren(s):
    s = re.sub(r'\bOpenResearchLeaves(3[2-8])EB\b', r'OpenResearchLeaves\1EBCF', s)
    s = re.sub(r'\bOpenResearchLeaves39\b', 'OpenResearchLeaves39CF', s)
    s = re.sub(r'\bOpenResearchLeaves40\b', 'OpenResearchLeaves41', s)
    return s


def strip_fields(block):
    """delete the two fields (with their doc comments) from a structure body, and pass-through lines elsewhere"""
    lines = block.split('\n')
    out, i = [], 0
    while i < len(lines):
        l = lines[i]
        if l.startswith('  /--'):
            doc = [l]
            while not doc[-1].rstrip().endswith('-/'):
                i += 1
                doc.append(lines[i])
            i += 1
            fld = lines[i] if i < len(lines) else ''
            if fld.strip().split(' ')[0] in FIELDS:
                i += 1
                continue
            out += doc
            continue
        if l.strip().split(' ')[0] in FIELDS:
            i += 1
            continue
        out.append(l)
        i += 1
    return '\n'.join(out)


counts = {'reads_replaced': 0, 'structures': 0, 'conversions': 0}


def take(src, kind, name):
    """the declaration text (with its doc comment) of `kind name` in src, up to the next blank line"""
    m = re.search(r'(/-- (?:(?!-/).)*?-/\n)?(' + kind + r' ' + re.escape(name) + r'\b.*?)\n(?=\n|end HSyn)', src, re.S)
    assert m, (kind, name)
    doc = m.group(1) or ''
    body = m.group(2)
    return doc, body


eb = open(H + 'EichlerBoundCopy.lean', encoding='utf-8').read()
z63 = open(H + 'TailZ63.lean', encoding='utf-8').read()
z64 = open(H + 'TailZ64.lean', encoding='utf-8').read()
z65 = open(H + 'TailZ65.lean', encoding='utf-8').read()

decls = []
# structures
for j in range(32, 39):
    doc, body = take(eb, 'structure', 'OpenResearchLeaves%dEB' % j)
    decls.append(('structure', 'OpenResearchLeaves%dEB' % j, 'EichlerBoundCopy.lean', doc, body))
doc, body = take(z63, 'structure', 'OpenResearchLeaves39')
decls.append(('structure', 'OpenResearchLeaves39', 'TailZ63.lean', doc, body))
doc, body = take(z65, 'structure', 'OpenResearchLeaves40')
decls.append(('structure', 'OpenResearchLeaves40', 'TailZ65.lean', doc, body))
# conversions
convs = [('openResearchLeaves%d_of_OpenResearchLeaves%d_eb' % (j - 1, j), 'EichlerBoundCopy.lean', eb) for j in range(32, 39)]
convs.append(('openResearchLeaves38EB_of_OpenResearchLeaves39', 'TailZ63.lean', z63))
convs.append(('openResearchLeaves39_of_OpenResearchLeaves40', 'TailZ65.lean', z65))
for name, f, src in convs:
    doc, body = take(src, 'theorem', name)
    decls.append(('theorem', name, f, doc, body))

newname = {}
for kind, name, f, doc, body in decls:
    if kind == 'theorem':
        newname[name] = name + '_cf'

out = []
for kind, name, f, doc, body in decls:
    nb = body
    k = nb.count(OLD)
    counts['reads_replaced'] += k
    nb = nb.replace(OLD, NEW)
    nb = strip_fields(nb)
    assert not any(x in nb for x in FIELDS), (name, 'field left')
    nb = ren(nb)
    if kind == 'theorem':
        counts['conversions'] += 1
        assert nb.startswith('theorem ' + name + ' '), name
        nb = 'theorem ' + newname[name] + nb[len('theorem ' + name):]
    else:
        counts['structures'] += 1
    d = '/-- Copy of `%s` (`%s`) without `gamma1IntegralSpan` and `heckePrimeIntegralToRational` (coeff-field-tc). -/\n' % (name, f)
    out.append(d + nb + '\n')

# compose the conversions as the sixContactMin chain does: parse each step's body
steps = {}
for n in range(49, 56):
    m = re.search(r'theorem sixContactMin_of_open%d_eb \(r : (\w+)\) \(t : OpenTextbookLeaves16\) \(l : OpenAddedLeaves25\) : ZInQ\.SixContactMin :=\n  sixContactMin_of_open%d_eb \((\w+) r( t)?( l)?\) t l\n' % (n, n - 1), eb)
    assert m, n
    steps[m.group(1)] = (m.group(2), (m.group(3) or '') + (m.group(4) or ''))
m = re.search(r'theorem sixContactMin_of_open56 \(r : OpenResearchLeaves39\) \(t : OpenTextbookLeaves16\) \(l : OpenAddedLeaves25\) : ZInQ\.SixContactMin :=\n  sixContactMin_of_open55_eb \(openResearchLeaves38EB_of_OpenResearchLeaves39 r t\) t l\n', z63)
assert m
steps['OpenResearchLeaves39'] = ('openResearchLeaves38EB_of_OpenResearchLeaves39', ' t')
m = re.search(r'theorem sixContactMin_of_open57 \(r : OpenResearchLeaves39\) \(t : OpenTextbookLeaves17\) \(l : OpenAddedLeaves25\) : ZInQ\.SixContactMin :=\n  sixContactMin_of_open56 r \(openTextbookLeaves16_of_OpenTextbookLeaves17 t\) l\n', z64)
assert m
m = re.search(r'theorem sixContactMin_of_open58 \(r : OpenResearchLeaves40\) \(t : OpenTextbookLeaves17\) \(l : OpenAddedLeaves25\) : ZInQ\.SixContactMin :=\n  sixContactMin_of_open57 \(openResearchLeaves39_of_OpenResearchLeaves40 r\) t l\n', z65)
assert m
m = re.search(r'theorem sixContactMin_of_open48_eb \(r : OpenResearchLeaves31EB\) \(t : OpenTextbookLeaves16\) \(l : OpenAddedLeaves25\) : ZInQ\.SixContactMin :=', eb)
assert m
T16 = '(openTextbookLeaves16_of_OpenTextbookLeaves17 t)'
expr = '(%s r)' % newname['openResearchLeaves39_of_OpenResearchLeaves40']
bundle = 'OpenResearchLeaves39'
order = ['OpenResearchLeaves39'] + ['OpenResearchLeaves%dEB' % j for j in range(38, 31, -1)]
for b in order:
    conv, extra = steps[b]
    args = extra.replace(' t', ' ' + T16).replace(' l', ' l')
    expr = '(%s %s%s)' % (newname[conv], expr, args)
top = ('/-- **G0 with only the open leaves and the open glue** (coeff-field-tc): `sixContactMin_of_open58` without the leaves\n'
       '`gamma1IntegralSpan` and `heckePrimeIntegralToRational` (`eigenformCoeffFieldFinite` proved outright), through the\n'
       'copied conversions, composed as in `sixContactMin_of_open49_eb`-`58`. -/\n'
       'theorem sixContactMin_of_open59 (r : OpenResearchLeaves41) (t : OpenTextbookLeaves17) (l : OpenAddedLeaves25) : ZInQ.SixContactMin :=\n'
       '  sixContactMin_of_open48_eb %s %s l\n' % (expr, T16))

hdr = '''import ZInQKernel.OneProof.H.TailZ65
import ZInQKernel.Contrib.OneProof.EigenformCoeffFieldFiniteProof

/-! # OneProof H, coeff-field-tc: `sixContactMin_of_open59`

`eigenformCoeffFieldFinite` (`DSCoeffExt.EigenformCoeffFieldFinite`: `K_f` is a number field), which coeff-rational's
fold (`TailZ56`) replaced by the leaves `gamma1IntegralSpan` and `heckePrimeIntegralToRational`, is proved outright by
`eigenformCoeffFieldFinite_proof` (`ZInQKernel/Contrib/OneProof/EigenformCoeffFieldFiniteProof.lean`, from Tau Ceti's
finiteness over `ℤ` of the cusp-form Hecke algebra; docs/research/coeff-field-tc.md). On `frozenTarget`'s proof the two
leaves are carried by `OpenResearchLeaves32EB`-`38EB` (`EichlerBoundCopy`), `OpenResearchLeaves39` (`TailZ63`) and
`OpenResearchLeaves40` (`TailZ65`), and read only through
`CoeffRational.eigenformCoeffFieldFinite_of_heckePrime n.gamma1IntegralSpan n.heckePrimeIntegralToRational` (in
`openResearchLeaves31_of_OpenResearchLeaves32_eb`, `openResearchLeaves32_of_OpenResearchLeaves33_eb` and twice in
`openResearchLeaves39_of_OpenResearchLeaves40`).

This module copies those structures and conversions verbatim up to the renaming `OpenResearchLeaves<j>EB ↦
OpenResearchLeaves<j>EBCF`, `OpenResearchLeaves39 ↦ OpenResearchLeaves39CF`, `OpenResearchLeaves40 ↦
OpenResearchLeaves41` and the suffix `_cf` on conversions, with the two fields and their pass-through lines deleted
and every reading replaced by `_root_.eigenformCoeffFieldFinite_proof`. The bottom copy produces the unchanged
`OpenResearchLeaves31EB`, and `sixContactMin_of_open59` ends in the unchanged `sixContactMin_of_open48_eb`. The
originals are unchanged. No new leaf. Generated by `scratch/coeff-field-tc/gen_fold2.py`. -/

set_option linter.style.longLine false

namespace HDec

namespace HSyn

'''
ftr = '''
end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open59
'''
text = hdr + '\n'.join(out) + '\n' + top + ftr
assert counts == {'reads_replaced': 4, 'structures': 9, 'conversions': 9}, counts
assert not any(x in text.split('-/', 1)[1].replace('`gamma1IntegralSpan` and `heckePrimeIntegralToRational`', '') .replace('without `gamma1IntegralSpan`', '') for x in ['n.gamma1IntegralSpan', 'n.heckePrimeIntegralToRational', 'gamma1IntegralSpan :', 'heckePrimeIntegralToRational :'])
sys.stderr.write('%s\n' % counts)
print(text, end='')
