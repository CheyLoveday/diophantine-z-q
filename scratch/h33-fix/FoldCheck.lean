import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.TYZThm33Alg

/-! h33-fix: the manual fold of `h33`, checked. `ZInQ.OneProof.frozenTarget` (OneProof/Main.lean at 222c98bf) with
the binder `(h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)` replaced by `(h33a : ZInQ.H33Fix.TYZThm33Alg)` and the
argument `h33` of `ThetaWP8.tyzThm35ReadingA_noHX` by
`(ZInQ.H33Fix.tyzThm33_of_alg (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33a)`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_h33Alg
    (r : HDec.HSyn.OpenResearchLeaves31) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h11 : TYZThm11Integral)
    (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33a : ZInQ.H33Fix.TYZThm33Alg)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open48 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists hL29 ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM)
      (ZInQ.H33Fix.tyzThm33_of_alg (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33a))
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

/-- The fold is the old theorem composed with the contribution. -/
theorem frozenTarget_h33Alg_eq
    (r : HDec.HSyn.OpenResearchLeaves31) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25)
    (h11 : TYZThm11Integral)
    (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33a : ZInQ.H33Fix.TYZThm33Alg)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    frozenTarget_h33Alg r t l h11 hL29 hCM h33a hBFH hGZ =
      ZInQ.OneProof.frozenTarget r t l h11 hL29 hCM
        (ZInQ.H33Fix.tyzThm33_of_alg (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33a) hBFH hGZ := rfl

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_h33Alg
