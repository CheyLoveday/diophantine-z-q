import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Triangular
import ZInQKernel.Contrib.OneProof.RC.Skeleton.Setup

/-!
# Common coordinate, part 3: bridges to the fields `h47` and `hunit` of `CommonCoordinateModel`

Lane RC0's wiring (`RC/Wiring/Central.lean`) takes (4.7) through `CommonCoordinateModel`, whose
fields include

```
h47 : (∏ q ∈ U, chi (l q)) * urel = (∏ q ∈ U, chi (e q) ^ 2 * eps q) * D.uPrim Fam x
hunit : ∀ q ∈ U, LamUnit (eps q)
```

(tex L4166–4193; "ELLIOT + GLUE (Nekovář 6.4.1–6.4.3)"). This file proves both in their exact
types, over `PowerSeries ℚ_[2]`, with `eps q = q⁻⁴`:

* `commonCoordinate_h47_of_models`: from triangular models of the support triangle at each
  relaxation step (`prod_relax_of_models`, `Triangular.lean`), whose old-part cycle and functional
  relations are the norm identity and `λ_R ∘ i = e_q λ_P` (hypotheses of the models;
  the headline does not import `Naturality.lean`, so on the headline's route they are assumed);
* `lamUnit_inv_odd_pow`: for odd `q`, `ε_q = q⁻⁴` is a `Λ`-unit (tex L4192–4193: "`q^{-4}` is one
  also").

**Classification.** PROVED (GLUE to RC0's wiring).
-/

namespace ZInQ.Contrib.CloudB3RC53.CommonCoordinate

open Matrix ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central

/-- **RC0's field `h47`, from the triangular models** (tex L4166–4193). Let `chi : R → ℚ₂[[t]]` be
the character at the address, `U` the unused primes, and for `p ∈ U` let the images of `l_p`, `e_p`
be the quotient and point factors of a Frobenius matrix `F p` (trace `a p`, determinant `q p`,
`q p · qi p = 1`) and the scalar `z p` (`zi p = z p⁻¹`). If the coordinates `u T` relaxed at
`T ⊆ U` (with `u U = u_rel`, `u ∅ = u_prim`) are related at each step by a triangular model of the
support triangle, then `(∏_U chi(l_p)) u_rel = (∏_U chi(e_p)² ε_p) u_prim` with `ε_p = qi p ⁴`. -/
theorem commonCoordinate_h47_of_models {R : Type*} [CommRing R] (chi : R →+* PowerSeries ℚ_[2])
    (U : Finset ℕ) (l e : ℕ → R) (urel uprim : PowerSeries ℚ_[2])
    (F : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])) (q qi a z zi : ℕ → PowerSeries ℚ_[2])
    (u : Finset ℕ → PowerSeries ℚ_[2])
    (hl : ∀ p ∈ U, chi (l p) = quotientFactor (F p) (qi p) (z p) (zi p))
    (he : ∀ p ∈ U, chi (e p) = pointFactor (a p) (z p) (zi p))
    (hrel : u U = urel) (hprim : u ∅ = uprim)
    (hq : ∀ p ∈ U, q p * qi p = 1) (ha : ∀ p ∈ U, (F p).trace = a p)
    (hd : ∀ p ∈ U, (F p).det = q p)
    (hmodel : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T → ∃ (n : ℕ) (DP : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2]))
      (X : Matrix (Fin n) (Fin 2 ⊕ Fin 2) (PowerSeries ℚ_[2])) (zP wP : Fin n → PowerSeries ℚ_[2])
      (zR wR : Fin n ⊕ (Fin 2 ⊕ Fin 2) → PowerSeries ℚ_[2]),
      (∀ i, zR (Sum.inl i) = pointFactor (a p) (z p) (zi p) * zP i) ∧
      (∀ i, wR (Sum.inl i) = pointFactor (a p) (z p) (zi p) * wP i) ∧
      IsCoordOn (fromBlocks DP X 0 (twoPlaceBlock (F p) (q p) (z p) (zi p))) zR wR (u (insert p T)) ∧
      IsClassFunctionalCoord DP zP wP (u T) ∧ DP.adjugate ≠ 0) :
    (∏ q ∈ U, chi (l q)) * urel = (∏ q ∈ U, chi (e q) ^ 2 * qi q ^ 4) * uprim := by
  have h := prod_relax_of_models U F q qi a z zi u hq ha hd hmodel
  rw [hrel, hprim] at h
  have e1 : ∏ q ∈ U, chi (l q) = ∏ p ∈ U, quotientFactor (F p) (qi p) (z p) (zi p) :=
    Finset.prod_congr rfl hl
  have e2 : ∏ q ∈ U, chi (e q) ^ 2 * qi q ^ 4 =
      ∏ p ∈ U, pointFactor (a p) (z p) (zi p) ^ 2 * qi p ^ 4 :=
    Finset.prod_congr rfl fun p hp => by rw [he p hp]
  rw [e1, e2]
  exact h

/-- **`ε_q = q⁻⁴` is a `Λ`-unit** for odd `q` (tex L4192–4193): RC0's field `hunit` for
`eps q = C(q⁻¹)⁴`. -/
theorem lamUnit_inv_odd_pow (q : ℕ) (hq : Odd q) :
    LamUnit (PowerSeries.C ((q : ℚ_[2])⁻¹) ^ 4) := by
  have hcop : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hq
  have hu : IsUnit (q : ℤ_[2]) := PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
  obtain ⟨w, hw⟩ := hu
  refine ⟨(Units.map (PowerSeries.C : ℤ_[2] →+* PowerSeries ℤ_[2]).toMonoidHom w⁻¹) ^ 4, ?_⟩
  have hw' : ((w⁻¹ : ℤ_[2]ˣ) : ℚ_[2]) = (q : ℚ_[2])⁻¹ := by
    have h1 : ((w : ℤ_[2]) : ℚ_[2]) * ((w⁻¹ : ℤ_[2]ˣ) : ℚ_[2]) = 1 := by
      rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]
    rw [hw, PadicInt.coe_natCast] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, map_pow, PowerSeries.map_C]
  rw [← hw']
  rfl

end ZInQ.Contrib.CloudB3RC53.CommonCoordinate
