import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.CMCurveOrder.Fold
import ZInQKernel.MainGreenTao

/-! Both the live Main (open76) and the discharge tool's bundle-module filter hide the
CM field from the stock check. Expose exactly the pre-fold open77 telescope for the
diagnostic, by currying out `cmFibreSplit` and putting it back into the open77 bundle. -/

namespace ZInQ.OneProof

theorem frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves59CMFS) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves27) (cmFibreSplit : HDec.CMBranch.CMFibreSplit)
    (hPC : ZInQ.PoleCompleteness) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open77_cm { r with cmFibreSplit := cmFibreSplit } t l) hPC

end ZInQ.OneProof

#discharges
