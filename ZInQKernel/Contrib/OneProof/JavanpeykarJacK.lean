import ZInQKernel.Contrib.OneProof.JavanpeykarAnRetype

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonObj
open LeafModCurves (IsCurve)
open JavanpeykarDict JavanpeykarFix JavanpeykarDirect JavanpeykarAnRetype
open ZInQ.LeafPush2 (javanpeykarBound)
open ZInQ.SemistabAssembly

namespace JavanpeykarJacK

/-- Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*,
Theorem 1.1.1: `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`. Section 2.3 identifies
`h_Fal(X)` with the stable Faltings height of the Jacobian of `X_K`.
Here `X₀` is that curve over the number field `K`, `X = X₀ ×_K K̄`, and
`V/K` represents its degree-zero Picard functor with the tensor group law.
The bound uses the least Belyi degree of `X`. The height of `V` is expressed
by `IsAnStableHeightSS` in the original normalization. This is the composite
cited in diophantine_zq.tex L870 (provenance (b)), restricted to these objects. -/
def JavanpeykarThm111JacK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X₀ : Over (Spec (CommRingCat.of K))) [IsCurve X₀]
    [IsIntegral (baseChangeCurve X₀ (AlgebraicClosure K)).left],
    (∃ (n : Type) (_ : Finite n)
      (i : (baseChangeCurve X₀ (AlgebraicClosure K)).left ⟶ ℙ(n; Spec (CommRingCat.of (AlgebraicClosure K)))),
      IsClosedImmersion i ∧ i ≫ ℙ(n; Spec (CommRingCat.of (AlgebraicClosure K))) ↘
        Spec (CommRingCat.of (AlgebraicClosure K)) = (baseChangeCurve X₀ (AlgebraicClosure K)).hom) →
    1 ≤ genusBar X₀ →
    ∀ (V : AbelianVariety K)
      (rep : (picardFunctorDegree X₀.hom 0).obj.RepresentableBy V.group.X),
      PicardTensorCompatible X₀.hom V.group rep →
    ∀ (hB : ∃ d, HasBelyiMapOfDegree (baseChangeCurve X₀ (AlgebraicClosure K)) d),
    ∀ x : ℝ, IsAnStableHeightSS (ofVendored V) x →
      x ≤ javanpeykarBound (genusBar X₀) (belyiDegree (baseChangeCurve X₀ (AlgebraicClosure K)) hB)

/-- Specialize the old row at the algebraic closure of `K` and use `V/K` itself
as the model of the geometric Jacobian. -/
theorem javanpeykarThm111JacK_of_an (h : JavanpeykarThm111An) : JavanpeykarThm111JacK := by
  intro K _ _ X₀ hX _ hproj hg V rep htc hB x hx
  have := isCurve_baseChange X₀ (AlgebraicClosure K)
  obtain ⟨W, repW, htcW, hVW⟩ := exists_jacBar X₀ hX V rep htc (AlgebraicClosure K)
  exact h (AlgebraicClosure K) (baseChangeCurve X₀ (AlgebraicClosure K)) hproj hg W repW htcW hB x
    ⟨K, inferInstance, inferInstance, inferInstance, V, hVW, hx⟩

end JavanpeykarJacK
