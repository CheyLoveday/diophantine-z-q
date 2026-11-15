import ZInQKernel.OneProof.H.TailZ26
open HDec
set_option pp.coercions false
#print FibreQMNorm.qmMatB
example (x : LeafQM.B) (w : Fin 2 → ℂ) : QMSplit.CNO.act x w 1 = 0 := by
  simp only [QMSplit.CNO.act, FibreQMNorm.qmMatB, BPAnalytic.QM.iota, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Matrix.add_apply]
  trace_state
  sorry
