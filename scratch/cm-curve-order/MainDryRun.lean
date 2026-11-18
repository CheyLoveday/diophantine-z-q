import ZInQKernel.Contrib.OneProof.CMCurveOrder.Fold
import ZInQKernel.MainGreenTao

namespace ZInQ.OneProof

/-- Dry run of the hand fold: replace Main's H argument and keep its pole-completeness argument. -/
theorem frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves59CMFS) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves27) (hPC : ZInQ.PoleCompleteness) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open78_cm r t l) hPC

end ZInQ.OneProof

#print axioms HDec.CMBranch.FibreSplit.cmCurveOrder324_of
#print axioms HDec.CMBranch.FibreSplit.cmCurveOrder_of_324
#print axioms HDec.CMBranch.FibreSplit.cmFibreSplit_of_curveOrder324
#print axioms HDec.HSyn.sixContactMin_of_open78_cm
#print axioms ZInQ.OneProof.frozenTarget
