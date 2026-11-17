import ZInQKernel.Contrib.OneProof.SGA7IX33SHPre

/-! Verbatim copy of the field's statement `DictModels.SGA7Pre.SGA7_IX_3_3_SHpre`
(ZInQKernel/Contrib/OneProof/SGA7IX33SHPre.lean), with an `rfl` check against the original. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue CToPrinted

namespace SGA33StepsCopy

def SGA7_IX_3_3_SHpre : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], IsStrictlyHenselianDVR O' →
    ∀ (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
    ∀ c : bcO hO 𝒩.G ⟶ 𝒩'.G, IsMonHom c → IsIso ((Over.pullback (jO O')).map c) →
    ∀ U : (bcO hO 𝒩.G).left.Opens,
      (U : Set (bcO hO 𝒩.G).left) =
        pullback.fst 𝒩.G.hom (Spec.map (CommRingCat.ofHom (comapHom hO))) ⁻¹' idCompSet 𝒩.G →
      IsOpenImmersion (U.ι ≫ c.left) ∧ Set.range (U.ι ≫ c.left).base = idCompSet 𝒩'.G

example : SGA7_IX_3_3_SHpre = DictModels.SGA7Pre.SGA7_IX_3_3_SHpre := rfl

end SGA33StepsCopy
