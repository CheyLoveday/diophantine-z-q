import ZInQKernel.Contrib.OneProof.CMCurveOrder.FoldOpen84
import ZInQKernel.OneProof.Discharges
import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal

/-! The same open83 call with the CM field made a separate binder, so the
discharge checker also reports the short field label. `Discharges.lean` checks
the actual, unchanged Main with its qualified bundle field. -/

namespace ZInQ.OneProof

theorem frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves65) (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves28)
    (cmFibreSplit : HDec.CMBranch.CMFibreSplit)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (h54 : ZInQ.Manuscript.PoleS12.Lemma54) (hB : ZInQ.Manuscript.PoleS12.BCDTThmA)
    (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open83
      { HDec.HSyn.openResearchLeaves64_of_OpenResearchLeaves65 r with cmFibreSplit := cmFibreSplit } t l)
    (ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_final hRC h54 hB hK)

end ZInQ.OneProof

#discharges
