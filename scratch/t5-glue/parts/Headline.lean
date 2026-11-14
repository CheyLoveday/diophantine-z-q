
namespace T5Glue

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1 from every statement still open, with row T-5 replaced by two printed leaves and
two glue Props** (`ShimuraMainCM`, `X0ModuliGalois`; `AbsArtinSurjectiveQNeg`, `IdeleLatticeScale`).
The kernel's `ZInQ.OneProof.frozenTarget` with `hS : Shimura.ShimuraReciprocityModFn` discharged by
`shimuraReciprocityModFn_of_final`. -/
theorem frozenTarget_t5
    (r : HDec.HSyn.OpenResearchLeaves9) (t : HDec.HSyn.OpenTextbookLeaves9) (l : HDec.HSyn.OpenAddedLeaves8)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : ShimuraMainCM) (hX : X0ModuliGalois) (hA : AbsArtinSurjectiveQNeg) (hS : IdeleLatticeScale)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l g h11 h29 (shimuraReciprocityModFn_of_final hCM hX hA hS) h33 hL2 hL3

end T5Glue

#print axioms T5Glue.frozenTarget_t5
