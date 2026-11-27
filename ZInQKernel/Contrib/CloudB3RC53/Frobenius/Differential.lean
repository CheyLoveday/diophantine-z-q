import ZInQKernel.Contrib.CloudB3RC53.Frobenius.Points
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential

/-!
# The Frobenius kills the invariant differential

The (base-changed) Frobenius pulls the invariant differential `ω = dx / (2y + a₁x + a₃)` back to
`(π^* (2y + a₁x + a₃))⁻¹ d(x^q) = 0`, since `d(x^q) = q x^{q-1} dx` and `q = 0` in characteristic
`p` (`pullbackDifferential_frobeniusMap`). This is the input of Tau Ceti's separability criterion
for `r π − s` (`isSeparable_toIsogeny_zsmul_sub_zsmul_id_iff_of_pullbackDifferential_eq_zero`).

Classification: PROVED.
-/

noncomputable section

open WeierstrassCurve.Affine

namespace ZInQ.Contrib.CloudB3RC53.Frobenius

open TauCeti

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve.Affine F)
  {K : Type*} [Field K] (f : F →+* K)

/-- **The base-changed Frobenius pulls the invariant differential back to `0`.** PROVED. -/
theorem pullbackDifferential_frobeniusMap :
    (frobeniusMap W f).pullbackDifferential (invariantDifferential (W.map f)) = 0 := by
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' F
  let _ := f.toAlgebra
  have : CharP K p := charP_of_injective_algebraMap' F p
  have : CharP (W.map f).FunctionField p := charP_of_injective_algebraMap' K p
  rw [invariantDifferential_def, Isogeny.pullbackDifferential_smul,
    Isogeny.pullbackDifferential_D, frobeniusMap_fieldPullback_genericX,
    Derivation.leibniz_pow, hcard]
  have h0 : ((p ^ (n : ℕ) : ℕ) : (W.map f).FunctionField) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by exact_mod_cast (PNat.pos n).ne')]
  rw [← Nat.cast_smul_eq_nsmul (W.map f).FunctionField, h0, zero_smul, smul_zero]

/-- The same for the morphism `ofIsogeny π` of Tau Ceti's `Hom` group. PROVED. -/
theorem hom_pullbackDifferential_frobeniusMap :
    (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pullbackDifferential
      (invariantDifferential (W.map f)) = 0 := by
  rw [Isogeny.Hom.pullbackDifferential_ofIsogeny, pullbackDifferential_frobeniusMap]

end ZInQ.Contrib.CloudB3RC53.Frobenius
