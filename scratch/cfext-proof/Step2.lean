import Mathlib

open scoped TensorProduct
open IsLocalRing Polynomial

set_option linter.style.haveILetI false

namespace CFExtProof

/-- In a function field of transcendence degree one, every element is algebraic over `K[π]` for
any transcendental `π`. -/
theorem isAlgebraic_adjoin_of_transcendental {K F : Type} [Field K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t) (hfin : FiniteDimensional (IntermediateField.adjoin K {t}) F)
    (π : F) (hπ : Transcendental K π) : Algebra.IsAlgebraic (Algebra.adjoin K {π}) F := by
  let xt : Unit → F := fun _ => t
  let xπ : Unit → F := fun _ => π
  have it : AlgebraicIndependent K xt := algebraicIndependent_unique_type_iff.mpr ht
  have iπ : AlgebraicIndependent K xπ := algebraicIndependent_unique_type_iff.mpr hπ
  have hrt : Set.range xt = {t} := Set.range_const
  have hrπ : Set.range xπ = {π} := Set.range_const
  have halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range xt)) F := by
    rw [hrt, ← IntermediateField.isAlgebraic_adjoin_iff_top]
    exact Algebra.IsAlgebraic.of_finite _ _
  have bt : IsTranscendenceBasis K xt := it.isTranscendenceBasis_iff_isAlgebraic.mpr halg
  have htr : Cardinal.mk Unit = Algebra.trdeg K F := bt.cardinalMk_eq_trdeg
  have bπ : IsTranscendenceBasis K xπ :=
    iπ.isTranscendenceBasis_of_trdeg_le_of_finite htr.symm.le
  have := bπ.isAlgebraic
  rwa [hrπ] at this

/-- The archimedean step: a nonzero `d ∈ O` divides a power of `π`. -/
theorem exists_pow_eq_mul {K F : Type} [Field K] [Field F] [Algebra K F] (O : ValuationSubring F)
    (hK : ∀ c : K, algebraMap K F c ∈ O) (π : F) (hπ : π ∈ O.nonunits)
    (d : F) (hd : d ∈ O) (hd0 : d ≠ 0) (halg : IsAlgebraic (Algebra.adjoin K {π}) d) :
    ∃ m : ℕ, ∃ y ∈ O, π ^ m = d * y := by
  let O' : Subalgebra K F := { O.toSubring with algebraMap_mem' := hK }
  have hπO : π ∈ O := O.nonunits_subset hπ
  have hadj : Algebra.adjoin K {π} ≤ O' := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hπO)
  have hev : ∀ P : (Algebra.adjoin K {π})[X], aeval d P ∈ O := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a =>
      rw [aeval_monomial]
      exact mul_mem (hadj a.2) (pow_mem hd n)
  obtain ⟨Q, hQ0, hQ⟩ := halg
  obtain ⟨Q', hQeq, hndvd⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQ0 0
  rw [map_zero, sub_zero] at hQeq hndvd
  have hQ'd : aeval d Q' = 0 := by
    rw [hQeq, map_mul, map_pow, aeval_X] at hQ
    exact (mul_eq_zero.mp hQ).resolve_left (pow_ne_zero _ hd0)
  have hc0 : Q'.coeff 0 ≠ 0 := fun h => hndvd (X_dvd_iff.mpr h)
  obtain ⟨T, hT⟩ := X_dvd_sub_C (p := Q')
  have hcT : ((Q'.coeff 0 : Algebra.adjoin K {π}) : F) = -(d * aeval d T) := by
    have := congrArg (aeval d) hT
    rw [map_sub, aeval_C, hQ'd, map_mul, aeval_X] at this
    rw [← this]; simp [Subalgebra.algebraMap_eq]
  -- write the constant coefficient as P(π)
  obtain ⟨P, hP⟩ : ∃ P : K[X], aeval π P = ((Q'.coeff 0 : Algebra.adjoin K {π}) : F) := by
    have key : ∀ z ∈ Algebra.adjoin K {π}, ∃ P : K[X], aeval π P = z := by
      intro z hz
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
      exact hz
    exact key _ (Q'.coeff 0).2
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [map_zero] at hP
    exact hc0 (Subtype.ext hP.symm)
  obtain ⟨R, hReq, hRndvd⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP0 0
  rw [map_zero, sub_zero] at hReq hRndvd
  have hR0 : R.coeff 0 ≠ 0 := fun h => hRndvd (X_dvd_iff.mpr h)
  obtain ⟨S, hS⟩ := X_dvd_sub_C (p := R)
  have hRπ : aeval π R = algebraMap K F (R.coeff 0) + π * aeval π S := by
    have := congrArg (aeval π) hS
    rw [map_sub, aeval_C, map_mul, aeval_X] at this
    rw [← this]; ring
  have hSO : aeval π S ∈ O := hadj (Polynomial.aeval_mem_adjoin_singleton K π)
  have hvc : O.valuation (algebraMap K F (R.coeff 0)) = 1 := by
    apply le_antisymm ((O.valuation_le_one_iff _).mpr (hK _))
    have h1 := (O.valuation_le_one_iff _).mpr (hK (R.coeff 0)⁻¹)
    rw [map_inv₀, map_inv₀] at h1
    have hne : O.valuation (algebraMap K F (R.coeff 0)) ≠ 0 := by simpa using hR0
    exact (inv_le_one₀ (zero_lt_iff.mpr hne)).mp h1
  have hvR : O.valuation (aeval π R) = 1 := by
    rw [hRπ, Valuation.map_add_eq_of_lt_left, hvc]
    rw [hvc, map_mul]
    calc O.valuation π * O.valuation (aeval π S) ≤ O.valuation π :=
          mul_le_of_le_one_right' ((O.valuation_le_one_iff _).mpr hSO)
      _ < 1 := (O.mem_nonunits_iff).mp hπ
  set m := rootMultiplicity 0 P
  have hvd : O.valuation (π ^ m) ≤ O.valuation d := by
    have e1 : O.valuation (aeval π P) = O.valuation (π ^ m) := by
      rw [hReq, map_mul, map_pow, aeval_X, map_mul, hvR, mul_one]
    rw [← e1, hP, hcT, Valuation.map_neg, map_mul]
    exact mul_le_of_le_one_right' ((O.valuation_le_one_iff _).mpr (hev T))
  refine ⟨m, π ^ m / d, ?_, by field_simp⟩
  rw [← O.valuation_le_one_iff, map_div₀]
  have hv0 : O.valuation d ≠ 0 := by simpa using hd0
  exact (div_le_one₀ (zero_lt_iff.mpr hv0)).mpr hvd

end CFExtProof
