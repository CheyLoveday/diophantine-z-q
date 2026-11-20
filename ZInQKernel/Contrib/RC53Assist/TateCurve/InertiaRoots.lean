import ZInQKernel.Contrib.RC53Assist.GlobalTrace.CoinvariantReadings

/-!
# Prime-to-residue-characteristic roots of unity and inertia

Reduction is injective on roots of unity of order invertible in the residue
field. Therefore the inertia subgroup fixes those roots. The proof is the
geometric-sum identity, not an unramified-character reading as an input.

Reference: elementary local-field theory; Silverman, *The Arithmetic of
Elliptic Curves*, III.8.1 for the later Weil-pairing application.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open IsLocalRing

section Reduction

variable {R k : Type*} [CommRing R] [IsDomain R] [Field k]

/-- **PROVED**: a torsion element reducing to one is one, if its order is
invertible in the residue field. Locator: `(x-1)∑x^i = x^N-1`. -/
theorem torsion_eq_one_of_residue (f : R →+* k) (N : ℕ) (hN : (N : k) ≠ 0)
    (x : R) (hx : x ^ N = 1) (hres : f x = 1) : x = 1 := by
  by_contra hne
  have hprod : (x - 1) * ∑ i ∈ Finset.range N, x ^ i = 0 := by
    rw [mul_geom_sum, hx, sub_self]
  have hsum := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
  have hf := congrArg f hsum
  have hz : (N : k) = 0 := by
    simpa only [map_sum, map_pow, hres, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using hf
  exact hN hz

/-- **PROVED**: reduction is injective on the `N`-torsion units when `N`
is nonzero in the residue field. Locator: `torsion_eq_one_of_residue`. -/
theorem torsion_units_eq_of_residue (f : R →+* k) (N : ℕ) (hN : (N : k) ≠ 0)
    (x y : Rˣ) (hx : x ^ N = 1) (hy : y ^ N = 1)
    (hres : f (x : R) = f (y : R)) : x = y := by
  let z := x * y⁻¹
  have hz : z ^ N = 1 := by simp only [z, mul_pow, hx, inv_pow, hy, inv_one, mul_one]
  have hzR : (z : R) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]
  have hfy : f (y : R) ≠ 0 := (y.isUnit.map f).ne_zero
  have hzf : f (z : R) = 1 := by
    change f ((x : R) * (↑y⁻¹ : R)) = 1
    rw [map_mul, hres]
    exact Units.mul_inv (Units.map f.toMonoidHom y)
  have hz1 : z = 1 := Units.ext (torsion_eq_one_of_residue f N hN (z : R) hzR hzf)
  exact mul_inv_eq_one.mp hz1

end Reduction

section Inertia

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **PROVED**: every root of unity has valuation one.
Locator: injectivity of a positive integral power in an ordered value group. -/
theorem valuation_of_torsion_unit (A : ValuationSubring F) (N : ℕ) (hN : N ≠ 0)
    (x : Fˣ) (hx : x ^ N = 1) : A.valuation (x : F) = 1 := by
  apply (pow_left_inj₀ zero_le zero_le_one hN).mp
  rw [← map_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, map_one, one_pow]

/-- **PROVED**: inertia fixes roots of unity of order prime to the residue
characteristic, for any valuation subring. Locator: inertia is the kernel of
the residue-field action and `torsion_units_eq_of_residue`. -/
theorem inertia_fixes_torsion_unit (A : ValuationSubring F) (N : ℕ) (hN : N ≠ 0)
    (hNk : (N : ResidueField A) ≠ 0) (x : Fˣ) (hx : x ^ N = 1)
    (i : A.inertiaSubgroup K) : ((i : A.decompositionSubgroup K) : F ≃ₐ[K] F) (x : F) = x := by
  classical
  let g : A.decompositionSubgroup K := i
  let X : Aˣ := A.unitGroupMulEquiv ⟨x, valuation_of_torsion_unit A N hN x hx⟩
  let Y : Aˣ := Units.map (MulSemiringAction.toRingAut (A.decompositionSubgroup K) A g)
    X
  have hX : ((X : A) : F) = (x : F) := rfl
  have hXN : X ^ N = 1 := by
    apply Units.ext
    apply Subtype.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    change A.subtype ((X : A) ^ N) = A.subtype 1
    rw [map_pow, map_one]
    change ((X : A) : F) ^ N = 1
    rw [hX]
    exact congrArg Units.val hx
  have hYN : Y ^ N = 1 := by
    change Units.map _ X ^ N = 1
    rw [← map_pow, hXN, map_one]
  have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (ResidueField A) g = 1 := i.property
  have hres : residue A (Y : A) = residue A (X : A) := by
    change g • residue A (X : A) = residue A (X : A)
    change MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (ResidueField A) g (residue A (X : A)) = _
    rw [hker]
    rfl
  have hXY : Y = X := torsion_units_eq_of_residue (residue A) N hNk Y X hYN hXN hres
  have hval := congrArg (fun u : Aˣ => ((u : A) : F)) hXY
  exact hval

end Inertia

end ZInQ.Contrib.RC53Assist.TateCurve
