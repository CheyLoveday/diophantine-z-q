import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.TYZThm33

/-! h33-dict: the manual fold of `h33`, checked. `ZInQ.OneProof.frozenTarget` (OneProof/Main.lean at 2880fef1) with
the binder `(h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)` replaced by
`(h33p : ZInQ.Contrib.TYZGenus.H33Dict.TYZThm33Printed)` and the subterm `h33` by
`(ZInQ.Contrib.TYZGenus.H33Dict.tyzThm33_of_printed hCM h33p)`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

theorem frozenTarget_h33Printed
    (r : HDec.HSyn.OpenResearchLeaves26) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8)
    (h11 : TYZThm11Integral)
    (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hT21 : H29Split.TYZThm21At31) (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33p : ZInQ.Contrib.TYZGenus.H33Dict.TYZThm33Printed)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open35 r t l g)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves hL3s hJP hfx hL29 hT21 hP23) hCM
      (ZInQ.Contrib.TYZGenus.H33Dict.tyzThm33_of_printed hCM h33p))
    ZInQ.GZTheta.Frontier.heckeThetaNewform (ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH) hL3

/-- The fold is the old theorem composed with the contribution. -/
theorem frozenTarget_h33Printed_eq
    (r : HDec.HSyn.OpenResearchLeaves26) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8)
    (h11 : TYZThm11Integral)
    (hL3s : H29Split.LegendreThreeSquares) (hJP : H29Split.JonesPallX2Y2Z16)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hT21 : H29Split.TYZThm21At31) (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33p : ZInQ.Contrib.TYZGenus.H33Dict.TYZThm33Printed)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    frozenTarget_h33Printed r t l g h11 hL3s hJP hfx hL29 hT21 hP23 hCM h33p hFH hL3 =
      ZInQ.OneProof.frozenTarget r t l g h11 hL3s hJP hfx hL29 hT21 hP23 hCM
        (ZInQ.Contrib.TYZGenus.H33Dict.tyzThm33_of_printed hCM h33p) hFH hL3 := rfl

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_h33Printed
