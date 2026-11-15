#!/usr/bin/env python3
"""Assemble ZInQKernel/Contrib/OneProof/RingClassLattice.lean =
header (imports of t5-glue + module doc) + t5-glue's T5Glue.lean body (verbatim, footer dropped)
+ scratch/gt-ringclass/RCL.lean (the proof of RingClassLattice) + Final.lean."""
import os
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.abspath(os.path.join(here, '..', '..'))
t5 = open(os.path.join(root, 'scratch/t5-glue/T5Glue.lean')).read()
imports, rest = t5.split('\n\n/-!', 1)
body = t5.split('\n-- ===== Elliptic.lean body (verbatim) =====\n', 1)[1]
body = body.split('\n-- ===== parts/Footer.lean =====\n', 1)[0]
doc = open(os.path.join(here, 'ModDoc.lean')).read()
rcl = open(os.path.join(here, 'RCL.lean')).read()
fin = open(os.path.join(here, 'Final.lean')).read()
# RCL section lives in namespace T5Glue with the opens of parts/Scale.lean
opens = '''noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

'''
out = (imports + '\n\n' + doc + '\n-- ===== t5-glue (origin/wip/t5-glue 39bb3cd2, scratch/t5-glue/T5Glue.lean), verbatim =====\n'
       + body + '\n-- ===== gt-ringclass: proof of RingClassLattice =====\n\n' + opens + rcl + '\nend T5Glue\n' + fin)
dst = os.path.join(root, 'ZInQKernel/Contrib/OneProof/RingClassLattice.lean')
open(dst, 'w').write(out)
print('wrote', dst, len(out.splitlines()), 'lines', len(out.encode()), 'bytes')
