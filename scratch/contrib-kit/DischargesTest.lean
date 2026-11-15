import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges

/-! Positive and negative controls for `#discharges` (task contrib-kit). Expected:
`t1` discharges `OpenAddedLeaves11.x6ConicModel` and still assumes it; `t2` discharges nothing;
`t3` discharges `OpenTextbookLeaves10.bdRInvariants` and is flagged for `sorry`. -/

open HDec in
theorem t1 (h : X6Kummer.X6ConicModel) : X6Kummer.X6ConicModel := h

theorem t2 : True := trivial

theorem t3 : ∀ (p : ℕ) [Fact p.Prime], _root_.ZInQ.Contrib.HodgeSplit.BdRInvariants p := sorry

#discharges
