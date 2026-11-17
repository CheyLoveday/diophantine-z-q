"""Generate the cm-fibre-split chain: R5Prune's one-line chain open6 .. open48 with the CM inputs
`CMBranch.CMInputs2` replaced by `CMBranch.FibreSplit.CMInputsFS` and the theorem suffix `_cm2_r5` by `_cmfs`.
The base (open4) and the top (open73) are written by hand in the template."""
import re, sys
src = open('ZInQKernel/Contrib/OneProof/CMBranch/R5Prune.lean').read().split('\n')
# chain region: from the open6 block to the end of the open48 block
start = next(i for i, l in enumerate(src) if 'Top2 50-55' in l)
end = next(i for i, l in enumerate(src) if 'Top2 216-220' in l)
chunk = '\n'.join(src[start:end])
chunk = re.sub(r'sixContactMin_of_(\w+?)_cm2_r5\b', r'sixContactMin_of_\1_cmfs', chunk)
chunk = chunk.replace('CMBranch.CMInputs2', 'CMBranch.FibreSplit.CMInputsFS')
chunk = chunk.replace('(cm-branch2)', '(cm-fibre-split)')
sys.stdout.write(chunk + '\n')
