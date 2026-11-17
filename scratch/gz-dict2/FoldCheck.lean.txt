import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.GrossZagierPlane

/-! gz-dict2 manual fold check (scratch; not part of the build). -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, manual fold of gz-dict2**: `Main.lean`'s `frozenTarget` with `hGZ` retyped from
`GZAlg.GrossZagierAlgOptCd` to `GZDict2.GrossZagierPlaneOptCd` (values of `φ` read on the plane model). -/
theorem _root_.ZInQ.OneProof.frozenTarget_gzdict2
    (r : HDec.HSyn.OpenResearchLeaves31) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves20)
    (h11 : TYZThm11Integral)
    (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZDict2.GrossZagierPlaneOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open43 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists hL29 ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZDict2.grossZagierAlgOptCd_of_plane hGZ) ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.OneProof.frozenTarget_gzdict2
#print axioms ZInQ.GZDict2.grossZagierAlgOptCd_of_plane
#print axioms ZInQ.GZDict2.grossZagierFormulaCd_of_plane
#print axioms ZInQ.GZDict2.modPt_eq_ratFn
