import ZInQKernel.Contrib.OneProof.CMCurveOrder.FoldOpen84
import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal

namespace ZInQ.OneProof

/-- **Theorem 1.1, from every statement still open:** the open H bundles, the manuscript's Theorem 5.3 (the restricted
converse) and Lemma 5.4 (both lemmas of the manuscript), the printed leaf BCDT Theorem A and a consequence of
Kolyvagin's Theorem 1 (through Shimura's construction and Faltings' isogeny theorem). Pole completeness PC (the
manuscript's Theorem 5.2) is proved from the last four
(`ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_final`). -/
theorem _root_.ZInQ.OneProof.cmPort2FrozenTarget
    (r : HDec.HSyn.OpenResearchLeaves65) (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves28)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (h54 : ZInQ.Manuscript.PoleS12.Lemma54) (hB : ZInQ.Manuscript.PoleS12.BCDTThmA)
    (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open84 r t l)
    (ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_final hRC h54 hB hK)

end ZInQ.OneProof

#print axioms ZInQ.OneProof.cmPort2FrozenTarget
