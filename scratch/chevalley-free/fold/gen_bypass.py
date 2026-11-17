#!/usr/bin/env python3
"""chevalley-free fold: write the bypass top module (TailZ65 shape) that removes the research field
`chevalleyPerfect` with no new leaf.

Reads ZInQKernel/OneProof/H/TailZ63.lean (OpenResearchLeaves39) and writes `TailZ65.lean.txt` next to this script:
  * `OpenResearchLeaves40` = `OpenResearchLeaves39` without the field `chevalleyPerfect` (fields and docstrings
    copied verbatim);
  * `openResearchLeaves36EB_of_OpenResearchLeaves40`, the composite of the three existing conversions
    39 -> 38EB (TailZ63), 38EB -> 37EB and 37EB -> 36EB (EichlerBoundCopy), with the three readers of
    `chevalleyPerfect` replaced by chevalley-free's theorems (no field);
  * `sixContactMin_of_open58 (r : OpenResearchLeaves40) (t : OpenTextbookLeaves17) (l : OpenAddedLeaves25)`.
Every existing declaration stays unchanged.  Usage: python3 gen_bypass.py REPO_ROOT [IMPORT_OF_CONTRIB]
"""
import re, sys, os

root = sys.argv[1]
contrib = sys.argv[2] if len(sys.argv) > 2 else 'ZInQKernel.Contrib.OneProof.ChevalleyFree'
src = open(os.path.join(root, 'ZInQKernel/OneProof/H/TailZ63.lean')).read()

# the structure block of OpenResearchLeaves39
m = re.search(r'structure OpenResearchLeaves39 : Prop where\n(.*?)\n\n', src, re.S)
body = m.group(1).split('\n')
# split into (doc, field) entries; a field line is "  name : type"
entries, doc = [], []
for line in body:
    if re.match(r'^  [A-Za-z0-9_]+ : ', line):
        entries.append((doc, line))
        doc = []
    else:
        doc.append(line)
assert not doc, doc
fields = [re.match(r'^  ([A-Za-z0-9_]+) : ', l).group(1) for _, l in entries]
assert 'chevalleyPerfect' in fields
kept = [(d, l) for d, l in entries if not l.startswith('  chevalleyPerfect :')]
kept_fields = [f for f in fields if f != 'chevalleyPerfect']
assert len(kept_fields) == len(fields) - 1

# fields of OpenResearchLeaves36EB (as in EichlerBoundCopy's 37EB -> 36EB conversion)
eb = open(os.path.join(root, 'ZInQKernel/OneProof/H/EichlerBoundCopy.lean')).read()
m36 = re.search(r'theorem openResearchLeaves36_of_OpenResearchLeaves37_eb .*? : OpenResearchLeaves36EB where\n(.*?)\nend HSyn', eb, re.S)
f36 = [re.match(r'^  ([A-Za-z0-9_]+) := ', l).group(1) for l in m36.group(1).split('\n') if l.strip()]

special = {
    'bostLowerBound': '_root_.ZInQ.ChevFree.bostLowerBound_of_printed_free n.bostLowerBoundPrinted '
                      '_root_.uniformizationLeafAll_proof t.mumfordTorsionAlgClosed',
    'gaudronRemondThm14': '_root_.ZInQ.ChevFree.gaudronRemondThm14_of_printed_free n.gaudronRemondThm14Printed '
                          '_root_.uniformizationLeafAll_proof t.mumfordTorsionAlgClosed',
    'javanpeykarBound': '_root_.JavanpeykarRebase.javanpeykarBound_of_printed_rebase_final n.javanpeykarPrintedMapHF '
                        'n.constantFieldExtensionUnramifiedFinite t.mumfordTorsionAlgClosed '
                        '_root_.ZInQ.ChevFree.semiAbelianDescendsPerfect_proof',
    'gonzalezRotgerProp56X6': '_root_.EichlerBound.r5fpCountLe_of_two t.gagaMorphism t.mumfordTorsionAlgClosed',
}
conv = []
for f in f36:
    if f in special:
        conv.append(f'  {f} := {special[f]}')
    else:
        assert f in kept_fields, f
        conv.append(f'  {f} := n.{f}')

out = []
out.append(f'import ZInQKernel.OneProof.H.TailZ64\nimport {contrib}\n')
out.append('''/-! # OneProof H, chevalley-free: `sixContactMin_of_open58`

Field removed: the research field `chevalleyPerfect` (LEAF, Chevalley's structure theorem over a perfect field,
semiab-descend). Fields added: none. Its only use was `ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley`,
and chevalley-free proved `ZInQ.HeightFix.SemiAbelianDescendsPerfect` outright
(`ZInQ.ChevFree.semiAbelianDescendsPerfect_proof`: spreading out to a finite subextension, rigidity of tori in
abelian varieties, effective finite flat descent). The field's three readers sit in the conversions
`38EB → 37EB` (`javanpeykarBound`) and `37EB → 36EB` (`bostLowerBound`, `gaudronRemondThm14`), so the new bundle maps
straight to `OpenResearchLeaves36EB` through the composite of the three existing conversions (bypass), with those
readers replaced. Every existing declaration is unchanged. -/

namespace HDec

namespace HSyn

/-- **The research leaves still open** (chevalley-free): `OpenResearchLeaves39` without `chevalleyPerfect` (no
replacement field). ''' + f'{len(kept_fields)} fields. -/\nstructure OpenResearchLeaves40 : Prop where')
stale = 'the leaf chevalleyPerfect (semiab-descend)'
for d, l in kept:
    out.extend([x.replace(stale, 'semiAbelianDescendsPerfect, proved by chevalley-free') for x in d])
    out.append(l)
out.append('')
out.append('/-- `OpenResearchLeaves36EB` from `OpenResearchLeaves40`: the conversions `39 → 38EB → 37EB → 36EB` composed, '
           'with `semiAbelianDescendsPerfect` proved (chevalley-free) where they read `chevalleyPerfect`. -/')
out.append('theorem openResearchLeaves36EB_of_OpenResearchLeaves40 (n : OpenResearchLeaves40) (t : OpenTextbookLeaves16) :\n'
           '    OpenResearchLeaves36EB where')
out.extend(conv)
out.append('')
out.append('/-- **G0 with only the open leaves** (chevalley-free; `chevalleyPerfect` removed with no new leaf). -/')
out.append('theorem sixContactMin_of_open58 (r : OpenResearchLeaves40) (t : OpenTextbookLeaves17) (l : OpenAddedLeaves25) :\n'
           '    ZInQ.SixContactMin :=\n'
           '  sixContactMin_of_open53_eb\n'
           '    (openResearchLeaves36EB_of_OpenResearchLeaves40 r (openTextbookLeaves16_of_OpenTextbookLeaves17 t))\n'
           '    (openTextbookLeaves16_of_OpenTextbookLeaves17 t) l')
out.append('\nend HSyn\n\nend HDec\n\n#print axioms HDec.HSyn.sixContactMin_of_open58')
text = '\n'.join(out) + '\n'
assert 'chevalleyPerfect :' not in text and 'n.chevalleyPerfect' not in text
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'TailZ65.lean.txt'), 'w').write(text)
print(f'fields: 39 has {len(fields)}, 40 has {len(kept_fields)}; 36EB conversion {len(f36)} lines')
