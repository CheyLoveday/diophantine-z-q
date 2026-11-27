"""Generate ZInQKernel/Contrib/OneProof/CMFibreSplit/Fold.lean (cm-fibre-split fold dry run).

* the chain open6 .. open48 of CMBranch/R5Prune.lean with c : CMInputs2 -> CMInputsFS (gen_chain.py);
* the base open4: cm-branch2's base with `cmFibreSplit` supplied by `cmFibreSplit_of` from the open4 bundles
  and the remaining glue `CMMatrixUnitSplit`;
* the next generation `OpenResearchLeaves54CMFS` = cm-branch2's `OpenResearchLeaves54CM` (CMBranch/Open73.lean) with the
  field `cmFibreSplit` removed, the conversion `openResearchLeaves36EBCF_cm_of_54fs`
  (verbatim copy of `openResearchLeaves36EBCF_cm_of_54`, type changed), and the top `sixContactMin_of_open73_cmfs`."""
import re, subprocess
chain = subprocess.run(['python3', 'scratch/cm-fibre-split/gen/gen_chain.py'], capture_output=True, text=True).stdout
o73 = open('ZInQKernel/Contrib/OneProof/CMBranch/Open73.lean').read().split('\n')
def block(start_pat):
    i = next(k for k, l in enumerate(o73) if l.startswith(start_pat))
    j = i + 1
    while j < len(o73) and o73[j].strip() != '' and not o73[j].startswith(('structure', 'theorem', '/--', 'def')):
        j += 1
    return o73[i:j]
s54 = block('structure OpenResearchLeaves54CM ')
s54 = '\n'.join(s54).replace('structure OpenResearchLeaves54CM ', 'structure OpenResearchLeaves54CMFS ')
old = ('  /-- cm-branch (glue, open): A8 at a CM fibre and the matrix units (diophantine_zq.tex L520-562, L582-586). -/\n'
       '  cmFibreSplit : CMBranch.CMFibreSplit')
assert old in s54
s54 = s54.replace(old + '\n', '')
conv = '\n'.join(block('theorem openResearchLeaves36EBCF_cm_of_54 '))
conv = conv.replace('theorem openResearchLeaves36EBCF_cm_of_54 (n : OpenResearchLeaves54CM)',
                    'theorem openResearchLeaves36EBCF_cm_of_54fs (n : OpenResearchLeaves54CMFS)')
assert 'cmFibreSplit' not in conv
tmpl = open('scratch/cm-fibre-split/gen/Fold.template.lean').read()
out = tmpl.replace('@@CHAIN@@', chain).replace('@@S54@@', s54).replace('@@CONV@@', conv)
open('ZInQKernel/Contrib/OneProof/CMFibreSplit/Fold.lean', 'w').write(out)
print(len(out))
