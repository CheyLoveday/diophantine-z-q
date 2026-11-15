import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges

/-! Positive and negative controls for `#discharges` (task contrib-kit). Expected:
`t1` discharges `quotientP1Coordinate` and still assumes it; `t2` discharges nothing;
`t3` discharges `cartierSmooth` and is flagged for `sorry`. Its saved output, `DischargesTest-output.txt`, is
the worked example of `docs/one-proof/CONTRIBUTING.md`; rerun it after a fold. -/

theorem t1 (h : HDec.MCRGlue.QuotientP1Coordinate) : HDec.MCRGlue.QuotientP1Coordinate := h

theorem t2 : True := trivial

theorem t3 : _root_.AVGlue.CartierSmooth := sorry

#discharges
