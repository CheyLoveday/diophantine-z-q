"""Emit the dry-run wrapper, closure check and a preview of kinds.tsv with the NOS row removed."""
import csv
import importlib.util
from pathlib import Path
import re

from copylib import decl_extent, find_decl, lines
from gen_chain import strip_field

here = Path(__file__).parent
base = 'ZInQKernel/OneProof/H/TailZ87.lean'
idx, = find_decl(base, 'OpenResearchLeaves61', ('structure',))
_, end = decl_extent(base, idx)
struct = strip_field('\n'.join(lines(base)[idx:end]) + '\n')
struct = struct.replace('OpenResearchLeaves61', 'OpenResearchLeaves62', 1)
fields = re.findall(r'^  ([\w\']+) :', struct, flags=re.M)

text = '''import ZInQKernel.Contrib.OneProof.NOSNarrowChain

/-! Integration dry run: replace `OpenResearchLeaves61` and `sixContactMin_of_open80`
in Main with the following bundle and theorem. -/

namespace HDec.HSyn

/-- The research bundle after removing the NOS field. -/
'''
text += struct + '''
/-- Pass the retained fields into the copied chain. -/
theorem openResearchLeaves61NOS_of_OpenResearchLeaves62
    (r : OpenResearchLeaves62) : OpenResearchLeaves61NOS where
'''
text += ''.join(f'  {f} := r.{f}\n' for f in fields)
text += '''
/-- Six-contact height estimate with the NOS row removed. -/
theorem sixContactMin_of_open81 (r : OpenResearchLeaves62) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves28) : ZInQ.SixContactMin :=
  sixContactMin_of_open80_nos (openResearchLeaves61NOS_of_OpenResearchLeaves62 r) t l

end HDec.HSyn

#print axioms HDec.HSyn.sixContactMin_of_open81
'''
(here / 'BypassFold.lean.txt').write_text(text)
(here / 'ClosureCheck.lean.txt').write_text(text + (here / 'closure-check.txt').read_text())

spec = importlib.util.spec_from_file_location('autofold', 'scripts/one_proof/autofold.py')
autofold = importlib.util.module_from_spec(spec)
spec.loader.exec_module(autofold)
rows, cols = autofold.load_kinds()
new = [r for r in rows if r['field'] != 'neronOggShafarevichSep']
assert len(new) == len(rows) - 1
assert autofold.counts(rows) == (29, 5, 24, 5, 24)
assert autofold.counts(new) == (28, 5, 23, 5, 23)
with (here / 'kinds-rows.tsv').open('w') as out:
    writer = csv.DictWriter(out, cols, delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows(new)
print('H strict and strictest LEAF/GLUE: 5/24 on 29 → 5/23 on 28.')
