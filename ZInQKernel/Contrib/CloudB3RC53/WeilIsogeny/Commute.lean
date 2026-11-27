import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.Fibre
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom

/-!
# A separable isogeny commutes with multiplication by `n`

`φ ∘ [n] = [n] ∘ φ` for a separable isogeny `φ` over a separably closed field (`comp_mulByInt`):
in the group of morphisms `[n]` is `n • id` (Tau Ceti's `ofIsogeny_mulByIntIsogeny`), composition
is additive in the outer variable (`zsmul_comp`), and in the inner variable it is checked on points
by rigidity, `φ` acting additively on points (`pointMap_ofIsogeny_eq_toPointHom`). Hence
`[n]^* ∘ φ^* = φ^* ∘ [n]^*` on function fields (`fieldPullback_mulByInt_comm`).

Classification: PROVED.
-/

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti TauCeti.Isogeny

namespace ZInQ.Contrib.CloudB3RC53.WeilIsogeny

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁ W₂)
  [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

/-- **`φ ∘ [n] = [n] ∘ φ`.** PROVED. -/
theorem comp_mulByInt {n : ℤ} (h₁ : psiFunctionField W₁ n ≠ 0) (h₂ : psiFunctionField W₂ n ≠ 0) :
    φ.comp (mulByIntIsogeny W₁ h₁) = (mulByIntIsogeny W₂ h₂).comp φ := by
  have := W₂.isIntegrallyClosed_coordinateRing
  apply Isogeny.Hom.ofIsogeny_injective
  rw [← Isogeny.Hom.ofIsogeny_comp_ofIsogeny, ← Isogeny.Hom.ofIsogeny_comp_ofIsogeny,
    ofIsogeny_mulByIntIsogeny, ofIsogeny_mulByIntIsogeny, Isogeny.Hom.zsmul_comp,
    Isogeny.Hom.id_comp]
  refine Isogeny.Hom.ext_pointMap fun P => ?_
  rw [Isogeny.Hom.comp_pointMap, Isogeny.Hom.zsmul_pointMap, Isogeny.Hom.zsmul_pointMap,
    Isogeny.Hom.id_pointMap, Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom,
    Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom, map_zsmul]

/-- **`[n]^* ∘ φ^* = φ^* ∘ [n]^*`** on function fields. PROVED. -/
theorem fieldPullback_mulByInt_comm {n : ℤ} (h₁ : psiFunctionField W₁ n ≠ 0)
    (h₂ : psiFunctionField W₂ n ≠ 0) (z : W₂.FunctionField) :
    (mulByIntIsogeny W₁ h₁).fieldPullback (φ.fieldPullback z) =
      φ.fieldPullback ((mulByIntIsogeny W₂ h₂).fieldPullback z) := by
  have h := congrArg (fun ψ : Isogeny W₁ W₂ => ψ.fieldPullback z) (comp_mulByInt φ h₁ h₂)
  simpa only [Isogeny.comp_fieldPullback, AlgHom.comp_apply] using h

end ZInQ.Contrib.CloudB3RC53.WeilIsogeny
