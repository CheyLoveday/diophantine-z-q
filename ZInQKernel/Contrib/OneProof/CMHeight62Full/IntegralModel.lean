import ZInQKernel.Contrib.OneProof.CMHeight62Full.WeierstrassDVR
import ZInQKernel.Contrib.OneProof.CMHeight62Full.GroupCurveNotP1

/-!
# An integral Weierstrass model with unit discriminant (node N10)

Pure algebra (Mathlib and the earlier `CMHeight62Full` files). Let `R` be a discrete valuation
ring with perfect residue field `k`, `F` its fraction field, `Ω ⊇ F` a field and `w` a valuation
on `Ω` with `w ≤ 1` on `R` and `w < 1` on the maximal ideal of `R`. Let `κ_w` be the residue field
of `w`, viewed as a `k`-algebra through `residueHom w hR hm`, and `ē` a place of `κ_w/k` with a
uniformizer `π`.

Suppose `x, y ∈ Ω` are `w`-integral, the seven monomials `1, x, y, x², xy, y², x³` lie in an
`F`-subspace `V` of dimension at most `6`, the residues `x̄, ȳ` have exact pole orders `2` and `3`
at `ē`, `x̄` has no other pole, and no element of `κ_w` has polar divisor exactly `1·ē`. Then
there are `W0 : WeierstrassCurve R` with `IsUnit W0.Δ` and a unit `e` of `R` such that
`(e x, e y)` lies on `W0` (`exists_integralModel`).

Proof.
* The seven monomials are `F`-linearly dependent; clearing denominators and dividing by a
  generator of the ideal of the coefficients gives an `R`-relation with a unit coefficient
  (`exists_relation_of_finrank_lt`, `exists_unit_coeff_relation`).
* Its reduction is a nontrivial relation in `κ_w`. The monomials have pole orders
  `0, 2, 3, 4, 5, 6, 6` at `ē`, so the `y²`- and `x³`-coefficients are nonzero
  (`coeff_ne_zero_of_poleOrders`): both are units of `R`.
* `weierstrass_normalization_dvr` gives `W0` and `e`. If `W0.Δ` were not a unit, the parameter
  `t` of `IsSingularParam` would have a simple pole at `ē` and no other pole, a contradiction.

`exists_integralModel_of_baseChange` discharges the last hypothesis by
`not_hasSimplePoleOnlyAt_of_baseChange`. The finite-span (lattice) hypothesis of the general
route is not needed here: the dimension bound on `V` alone gives the relation.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

universe uR uF uΩ uΓ

open IsLocalRing Module

namespace IntegralModel

/-! ### A relation with a unit coefficient -/

/-- A family indexed by `ι` in a subspace of dimension less than `Fintype.card ι`
satisfies a nontrivial `R`-relation. -/
theorem exists_relation_of_finrank_lt {R : Type*} [CommRing R] [IsDomain R] {F : Type*}
    [Field F] [Algebra R F] [IsFractionRing R F] {Ω : Type*} [Field Ω] [Algebra F Ω]
    [Algebra R Ω] [IsScalarTower R F Ω] (V : Submodule F Ω) [FiniteDimensional F V]
    {ι : Type*} [Fintype ι] (v : ι → Ω) (hv : ∀ i, v i ∈ V)
    (hcard : finrank F V < Fintype.card ι) :
    ∃ c : ι → R, (∃ i, c i ≠ 0) ∧ ∑ i, algebraMap R Ω (c i) * v i = 0 := by
  have hli : ¬ LinearIndependent F (fun i => (⟨v i, hv i⟩ : V)) := fun h =>
    absurd h.fintype_card_le_finrank (not_le.mpr hcard)
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hli
  have hg' : ∑ i, algebraMap F Ω (g i) * v i = 0 := by
    have h := congrArg ((↑) : V → Ω) hg
    rw [Submodule.coe_sum, Submodule.coe_zero] at h
    simpa only [Submodule.coe_smul, Algebra.smul_def] using h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) g
  have hb' : ∀ i, ∃ c : R, algebraMap R F c = (b : R) • g i := fun i => hb i
  choose c hc using hb'
  have hb0 : algebraMap R F (b : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  refine ⟨c, ⟨i₀, fun h => ?_⟩, ?_⟩
  · have h1 := hc i₀
    rw [h, map_zero, Algebra.smul_def] at h1
    exact (mul_ne_zero hb0 hi₀) h1.symm
  · have hterm : ∀ i, algebraMap R Ω (c i) * v i =
        algebraMap F Ω (algebraMap R F (b : R)) * (algebraMap F Ω (g i) * v i) := by
      intro i
      rw [IsScalarTower.algebraMap_apply R F Ω, hc i, Algebra.smul_def, map_mul, mul_assoc]
    simp only [hterm]
    rw [← Finset.mul_sum, hg', mul_zero]

/-- Over a local principal ideal domain, a nontrivial relation can be made primitive: some
coefficient becomes a unit. -/
theorem exists_unit_coeff_relation {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsPrincipalIdealRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
    (hinj : Function.Injective (algebraMap R Ω)) {ι : Type*} [Fintype ι] (v : ι → Ω)
    (c : ι → R) (hc : ∃ i, c i ≠ 0) (hrel : ∑ i, algebraMap R Ω (c i) * v i = 0) :
    ∃ d : ι → R, (∃ i, IsUnit (d i)) ∧ ∑ i, algebraMap R Ω (d i) * v i = 0 := by
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal (Ideal.span (Set.range c))
  have hmem : ∀ i, ∃ d : R, d * g = c i := fun i => by
    have h : c i ∈ Ideal.span (Set.range c) := Ideal.subset_span ⟨i, rfl⟩
    rw [hg, Submodule.mem_span_singleton] at h
    simpa only [smul_eq_mul] using h
  choose d hd using hmem
  have hgmem : g ∈ Ideal.span (Set.range c) := by
    rw [hg]; exact Submodule.mem_span_singleton_self g
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hgmem
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hc
    exact hi (by rw [← hd i, mul_zero])
  have hsum : ∑ i, a i * d i = 1 := by
    have h1 : g * ∑ i, a i * d i = g * 1 := by
      rw [mul_one, Finset.mul_sum]
      conv_rhs => rw [← ha]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hd i]
      ring
    exact mul_left_cancel₀ hg0 h1
  refine ⟨d, ?_, ?_⟩
  · by_contra hno
    have hall : ∀ i, d i ∈ maximalIdeal R := fun i =>
      (mem_maximalIdeal _).mpr fun hu => hno ⟨i, hu⟩
    have h1 : ∑ i, a i * d i ∈ maximalIdeal R :=
      Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hall i)
    rw [hsum] at h1
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · have hg0' : algebraMap R Ω g ≠ 0 := by
      rw [ne_eq, ← map_zero (algebraMap R Ω)]
      exact fun h => hg0 (hinj h)
    have h1 : algebraMap R Ω g * ∑ i, algebraMap R Ω (d i) * v i = 0 := by
      rw [Finset.mul_sum, ← hrel]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hd i, map_mul]
      ring
    exact (mul_eq_zero.mp h1).resolve_left hg0'

/-! ### Pole orders `0, 2, 3, 4, 5, 6, 6` -/

section Poles

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem valuation_mul_le_pow (ν : Valuation K Γ) {δ : Γ} (hδ : 1 ≤ δ) {b M : K} {m n : ℕ}
    (hb : ν b ≤ 1) (hM : ν M = δ ^ m) (hmn : m ≤ n) : ν (b * M) ≤ δ ^ n := by
  rw [map_mul, hM]
  calc ν b * δ ^ m ≤ 1 * δ ^ m := mul_le_mul_of_nonneg_right hb zero_le
    _ = δ ^ m := one_mul _
    _ ≤ δ ^ n := pow_le_pow_right₀ hδ hmn

theorem add_ne_zero_of_valuation_lt (ν : Valuation K Γ) {δ : Γ} (hδ : 1 < δ) {u r : K}
    {n : ℕ} (hu : ν u = δ ^ n) (hr : ν r < δ ^ n) : u + r ≠ 0 := by
  intro h
  have h1 : ν (u + r) = ν u := Valuation.map_add_eq_of_lt_left ν (by rw [hu]; exact hr)
  rw [h, map_zero, hu] at h1
  exact pow_ne_zero n (zero_lt_one.trans hδ).ne' h1.symm

/-- **Pole orders.** If `ν(X) = δ²`, `ν(Y) = δ³` with `δ > 1`, and the coefficients are `0` or
of value `1`, a nontrivial relation among `1, X, Y, X², XY, Y², X³` has nonzero `Y²`- and
`X³`-coefficients. -/
theorem coeff_ne_zero_of_poleOrders (ν : Valuation K Γ) {X Y : K} {δ : Γ} (hδ : 1 < δ)
    (hX : ν X = δ ^ 2) (hY : ν Y = δ ^ 3) (a : Fin 7 → K) (ha : ∀ i, a i = 0 ∨ ν (a i) = 1)
    (hrel : a 0 + a 1 * X + a 2 * Y + a 3 * X ^ 2 + a 4 * (X * Y) + a 5 * Y ^ 2
      + a 6 * X ^ 3 = 0)
    (hne : ∃ i, a i ≠ 0) : a 5 ≠ 0 ∧ a 6 ≠ 0 := by
  have hδ1 : (1 : Γ) ≤ δ := hδ.le
  have hle : ∀ i, ν (a i) ≤ 1 := fun i => by
    rcases ha i with h | h
    · rw [h, map_zero]; exact zero_le
    · exact h.le
  have heq : ∀ i, a i ≠ 0 → ∀ {M : K} {n : ℕ}, ν M = δ ^ n → ν (a i * M) = δ ^ n :=
    fun i hi M n hM => by rw [map_mul, (ha i).resolve_left hi, hM, one_mul]
  have hlt : ∀ {m n : ℕ}, m < n → δ ^ m < δ ^ n := fun h => pow_lt_pow_right₀ hδ h
  have hX2 : ν (X ^ 2) = δ ^ 4 := by rw [map_pow, hX, ← pow_mul]
  have hXY : ν (X * Y) = δ ^ 5 := by rw [map_mul, hX, hY, ← pow_add]
  have hY2 : ν (Y ^ 2) = δ ^ 6 := by rw [map_pow, hY, ← pow_mul]
  have hX3 : ν (X ^ 3) = δ ^ 6 := by rw [map_pow, hX, ← pow_mul]
  have hS0 : ν (a 0) ≤ δ ^ 0 := by rw [pow_zero]; exact hle 0
  have hS2 : ν (a 0 + a 1 * X) ≤ δ ^ 2 :=
    Valuation.map_add_le ν ((hle 0).trans (one_le_pow₀ hδ1))
      (valuation_mul_le_pow ν hδ1 (hle 1) hX le_rfl)
  have hS3 : ν (a 0 + a 1 * X + a 2 * Y) ≤ δ ^ 3 :=
    Valuation.map_add_le ν (hS2.trans (pow_le_pow_right₀ hδ1 (by norm_num)))
      (valuation_mul_le_pow ν hδ1 (hle 2) hY le_rfl)
  have hS4 : ν (a 0 + a 1 * X + a 2 * Y + a 3 * X ^ 2) ≤ δ ^ 4 :=
    Valuation.map_add_le ν (hS3.trans (pow_le_pow_right₀ hδ1 (by norm_num)))
      (valuation_mul_le_pow ν hδ1 (hle 3) hX2 le_rfl)
  have hS5 : ν (a 0 + a 1 * X + a 2 * Y + a 3 * X ^ 2 + a 4 * (X * Y)) ≤ δ ^ 5 :=
    Valuation.map_add_le ν (hS4.trans (pow_le_pow_right₀ hδ1 (by norm_num)))
      (valuation_mul_le_pow ν hδ1 (hle 4) hXY le_rfl)
  by_cases h5 : a 5 = 0
  · by_cases h6 : a 6 = 0
    · exfalso
      have h4 : a 4 = 0 := by
        by_contra h4
        exact add_ne_zero_of_valuation_lt ν hδ (heq 4 h4 hXY) (hS4.trans_lt (hlt (by norm_num)))
          (by linear_combination hrel - Y ^ 2 * h5 - X ^ 3 * h6)
      have h3 : a 3 = 0 := by
        by_contra h3
        exact add_ne_zero_of_valuation_lt ν hδ (heq 3 h3 hX2) (hS3.trans_lt (hlt (by norm_num)))
          (by linear_combination hrel - Y ^ 2 * h5 - X ^ 3 * h6 - X * Y * h4)
      have h2 : a 2 = 0 := by
        by_contra h2
        exact add_ne_zero_of_valuation_lt ν hδ (heq 2 h2 hY) (hS2.trans_lt (hlt (by norm_num)))
          (by linear_combination hrel - Y ^ 2 * h5 - X ^ 3 * h6 - X * Y * h4 - X ^ 2 * h3)
      have h1 : a 1 = 0 := by
        by_contra h1
        exact add_ne_zero_of_valuation_lt ν hδ (heq 1 h1 hX) (hS0.trans_lt (hlt (by norm_num)))
          (by linear_combination hrel - Y ^ 2 * h5 - X ^ 3 * h6 - X * Y * h4 - X ^ 2 * h3
            - Y * h2)
      have h0 : a 0 = 0 := by
        linear_combination hrel - Y ^ 2 * h5 - X ^ 3 * h6 - X * Y * h4 - X ^ 2 * h3 - Y * h2
          - X * h1
      obtain ⟨i, hi⟩ := hne
      apply hi
      fin_cases i <;> assumption
    · exfalso
      exact add_ne_zero_of_valuation_lt ν hδ (heq 6 h6 hX3) (hS5.trans_lt (hlt (by norm_num)))
        (by linear_combination hrel - Y ^ 2 * h5)
  · by_cases h6 : a 6 = 0
    · exfalso
      exact add_ne_zero_of_valuation_lt ν hδ (heq 5 h5 hY2) (hS5.trans_lt (hlt (by norm_num)))
        (by linear_combination hrel - X ^ 3 * h6)
    · exact ⟨h5, h6⟩

end Poles

/-! ### Reduction of the relation -/

/-- An `R`-relation among the seven monomials in `w`-integral `x, y` reduces to a relation in
the residue field of `w`. -/
theorem reduce_seven_relation {R : Type*} [CommRing R] [IsLocalRing R] {Ω : Type*} [Field Ω]
    [Algebra R Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀)
    (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1) {x y : Ω} (hx : w x ≤ 1)
    (hy : w y ≤ 1) (d : Fin 7 → R)
    (hrel : algebraMap R Ω (d 0) + algebraMap R Ω (d 1) * x + algebraMap R Ω (d 2) * y
      + algebraMap R Ω (d 3) * x ^ 2 + algebraMap R Ω (d 4) * (x * y)
      + algebraMap R Ω (d 5) * y ^ 2 + algebraMap R Ω (d 6) * x ^ 3 = 0) :
    residueHom w hR hm (residue R (d 0))
      + residueHom w hR hm (residue R (d 1)) * reduce w x hx
      + residueHom w hR hm (residue R (d 2)) * reduce w y hy
      + residueHom w hR hm (residue R (d 3)) * reduce w x hx ^ 2
      + residueHom w hR hm (residue R (d 4)) * (reduce w x hx * reduce w y hy)
      + residueHom w hR hm (residue R (d 5)) * reduce w y hy ^ 2
      + residueHom w hR hm (residue R (d 6)) * reduce w x hx ^ 3 = 0 := by
  have hφ : ∀ r : R, residueHom w hR hm (residue R r) =
      residue w.valuationSubring (toIntegers w hR r) := by
    intro r
    have := isLocalHom_toIntegers w hR hm
    rw [residueHom, ResidueField.map_residue]
  have h1 : toIntegers w hR (d 0)
      + toIntegers w hR (d 1) * ⟨x, (w.mem_valuationSubring_iff x).2 hx⟩
      + toIntegers w hR (d 2) * ⟨y, (w.mem_valuationSubring_iff y).2 hy⟩
      + toIntegers w hR (d 3) * ⟨x, (w.mem_valuationSubring_iff x).2 hx⟩ ^ 2
      + toIntegers w hR (d 4) * (⟨x, (w.mem_valuationSubring_iff x).2 hx⟩
        * ⟨y, (w.mem_valuationSubring_iff y).2 hy⟩)
      + toIntegers w hR (d 5) * ⟨y, (w.mem_valuationSubring_iff y).2 hy⟩ ^ 2
      + toIntegers w hR (d 6) * ⟨x, (w.mem_valuationSubring_iff x).2 hx⟩ ^ 3 = 0 := by
    apply Subtype.ext
    push_cast
    simpa only [coe_toIntegers] using hrel
  have h2 := congrArg (residue w.valuationSubring) h1
  simp only [map_add, map_mul, map_pow, map_zero] at h2
  simp only [hφ]
  exact h2

/-! ### The integral model -/

/-- **Integral model with unit discriminant (N10).** Let `R` be a DVR with perfect residue field
`k`, `F` its fraction field, `w` a valuation on `Ω ⊇ F` with `w ≤ 1` on `R` and `w < 1` on its
maximal ideal, and `κ_w` its residue field, a `k`-algebra through `residueHom w hR hm`. Let `x, y`
be `w`-integral with `1, x, y, x², xy, y², x³` in an `F`-subspace `V` of dimension at most `6`.
Let `P` be a place of `κ_w/k` with uniformizer `π` at which `x̄` and `ȳ` have exact pole orders
`2` and `3`, `x̄` regular at every other place, and suppose no element of `κ_w` has polar divisor
exactly `1·P`. Then some `W0 : WeierstrassCurve R` with unit discriminant passes through
`(e x, e y)` for a unit `e` of `R`. -/
theorem exists_integralModel {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] {F : Type uF} [Field F] [Algebra R F] [IsFractionRing R F]
    {Ω : Type uΩ} [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower R F Ω]
    {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀)
    (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1)
    [Algebra (ResidueField R) (ResidueField w.valuationSubring)]
    (halg : algebraMap (ResidueField R) (ResidueField w.valuationSubring) = residueHom w hR hm)
    (V : Submodule F Ω) [FiniteDimensional F V] (hV : finrank F V ≤ 6) {x y : Ω}
    (hmono : ∀ i, ![1, x, y, x ^ 2, x * y, y ^ 2, x ^ 3] i ∈ V) (hx : w x ≤ 1) (hy : w y ≤ 1)
    (P : ValuationSubring (ResidueField w.valuationSubring))
    (hP : IsConstPlace (ResidueField R) P) {π : ResidueField w.valuationSubring}
    (hπ : IsUniformizerAt P π) (hxP : P.valuation (reduce w x hx * π ^ 2) = 1)
    (hyP : P.valuation (reduce w y hy * π ^ 3) = 1)
    (hxO : ∀ O : ValuationSubring (ResidueField w.valuationSubring),
      IsConstPlace (ResidueField R) O → O ≠ P → reduce w x hx ∈ O)
    (hnsp : ∀ f : ResidueField w.valuationSubring,
      ¬ HasSimplePoleOnlyAt (ResidueField R) P f) :
    ∃ (W0 : WeierstrassCurve R) (e : Rˣ), IsUnit W0.Δ ∧
      (W0.map (algebraMap R Ω)).toAffine.Equation (algebraMap R Ω e * x)
        (algebraMap R Ω e * y) := by
  -- constants lie in every place
  have hconst : ∀ O : ValuationSubring (ResidueField w.valuationSubring),
      IsConstPlace (ResidueField R) O → ∀ c, residueHom w hR hm c ∈ O := fun O hO c => by
    have := hO c
    rwa [halg] at this
  have hval1 : ∀ c : ResidueField R, c ≠ 0 → P.valuation (residueHom w hR hm c) = 1 :=
    fun c hc => by
      have := GroupCurveNotP1.valuation_algebraMap_eq_one hP hc
      rwa [halg] at this
  -- the pole orders at `P`
  have hπ0 : π ≠ 0 := hπ.1
  have hδ : 1 < P.valuation π⁻¹ := by
    have h := GroupCurveNotP1.inv_not_mem_of_mem_nonunits hπ.2.1 hπ0
    exact not_le.mp (mt (P.valuation_le_one_iff _).mp h)
  have hX : P.valuation (reduce w x hx) = P.valuation π⁻¹ ^ 2 := by
    have : reduce w x hx = reduce w x hx * π ^ 2 * π⁻¹ ^ 2 := by field_simp
    rw [this, map_mul, hxP, one_mul, map_pow]
  have hY : P.valuation (reduce w y hy) = P.valuation π⁻¹ ^ 3 := by
    have : reduce w y hy = reduce w y hy * π ^ 3 * π⁻¹ ^ 3 := by field_simp
    rw [this, map_mul, hyP, one_mul, map_pow]
  -- a primitive relation
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R F Ω, RingHom.coe_comp]
    exact (algebraMap F Ω).injective.comp (IsFractionRing.injective R F)
  obtain ⟨c, hc0, hc⟩ := exists_relation_of_finrank_lt (R := R) V _ hmono
    (by rw [Fintype.card_fin]; omega)
  obtain ⟨d, ⟨i₀, hi₀⟩, hd⟩ := exists_unit_coeff_relation hinj _ c hc0 hc
  have hrel : algebraMap R Ω (d 0) + algebraMap R Ω (d 1) * x + algebraMap R Ω (d 2) * y
      + algebraMap R Ω (d 3) * x ^ 2 + algebraMap R Ω (d 4) * (x * y)
      + algebraMap R Ω (d 5) * y ^ 2 + algebraMap R Ω (d 6) * x ^ 3 = 0 := by
    simpa [Fin.sum_univ_seven] using hd
  have hred := reduce_seven_relation w hR hm hx hy d hrel
  -- the `y²`- and `x³`-coefficients are units
  have hcoef := coeff_ne_zero_of_poleOrders P.valuation hδ hX hY
    (fun i => residueHom w hR hm (residue R (d i)))
    (fun i => by
      by_cases h : residueHom w hR hm (residue R (d i)) = 0
      · exact Or.inl h
      · exact Or.inr (hval1 _ fun h' => h (by rw [h', map_zero])))
    (by simpa using hred)
    ⟨i₀, by
      rw [map_ne_zero]
      exact (residue_ne_zero_iff_isUnit _).mpr hi₀⟩
  have h₅ : IsUnit (d 5) :=
    (residue_ne_zero_iff_isUnit _).mp fun h => hcoef.1 (by simp only [h, map_zero])
  have h₆ : IsUnit (d 6) :=
    (residue_ne_zero_iff_isUnit _).mp fun h => hcoef.2 (by simp only [h, map_zero])
  -- normalization
  obtain ⟨W, e, hE, hsing⟩ :=
    weierstrass_normalization_dvr.{uΩ, uR, uΩ, uΓ} w hR hm hx hy h₅ h₆ hrel
  refine ⟨W, e, ?_, hE⟩
  by_contra hΔ
  have hpole : 1 < P.valuation (reduce w x hx) := by
    rw [hX]; exact one_lt_pow₀ hδ two_ne_zero
  have hnc : ∀ c, residueHom w hR hm c ≠ reduce w x hx := by
    intro c hc
    have h := (P.valuation_le_one_iff _).mpr (hconst P hP c)
    rw [hc] at h
    exact not_le.mpr hpole h
  obtain ⟨x₀, y₀, t, -, -, -, -, -, -, hparam⟩ := hsing hΔ hnc
  have hXe : reduce w (algebraMap R Ω e * x) (valuation_algebraMap_mul_le w hR e hx) =
      residueHom w hR hm (residue R e) * reduce w x hx :=
    reduce_algebraMap_mul w hR hm e hx
  have he0 : residue R (e : R) ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr e.isUnit
  -- `t` has a simple pole at `P`
  obtain ⟨hiff, hsq⟩ := hparam P.ValueGroup P.valuation fun c =>
    (P.valuation_le_one_iff _).mpr (hconst P hP c)
  have hXP : P.valuation (reduce w (algebraMap R Ω e * x)
      (valuation_algebraMap_mul_le w hR e hx)) = P.valuation π⁻¹ ^ 2 := by
    rw [hXe, map_mul, hval1 _ he0, one_mul, hX]
  have ht1 : 1 < P.valuation t := hiff.mpr (by rw [hXP]; exact one_lt_pow₀ hδ two_ne_zero)
  have ht : P.valuation t = P.valuation π⁻¹ := by
    have h := (hsq ht1).symm.trans hXP
    exact le_antisymm ((pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero).mp h.le)
      ((pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero).mp h.ge)
  refine hnsp t ⟨fun h => not_le.mpr ht1 ((P.valuation_le_one_iff t).mpr h), ?_, ?_⟩
  · intro z hz
    have h := (P.valuation_le_one_iff _).mpr (hπ.2.2 z hz)
    rw [← P.valuation_le_one_iff, map_mul, ht]
    rwa [map_mul] at h
  · intro O hO hOP
    by_contra htO
    have h1 : 1 < O.valuation t := not_le.mp (mt (O.valuation_le_one_iff t).mp htO)
    obtain ⟨hiffO, -⟩ := hparam O.ValueGroup O.valuation fun c =>
      (O.valuation_le_one_iff _).mpr (hconst O hO c)
    have h2 := hiffO.mp h1
    have h3 : reduce w (algebraMap R Ω e * x) (valuation_algebraMap_mul_le w hR e hx) ∈ O := by
      rw [hXe]; exact mul_mem (hconst O hO _) (hxO O hO hOP)
    exact not_le.mpr h2 ((O.valuation_le_one_iff _).mpr h3)

/-- **N10 with the group-curve input.** The same conclusion, with the no-simple-pole hypothesis
supplied by `not_hasSimplePoleOnlyAt_of_baseChange`: `κ_w/k` has transcendence degree at most
one, `P` has degree one, and a field `Kb` generated by `κ_w` over an algebraic closure `kb` of
`k` has a `kb`-automorphism fixing no degree-one place. -/
theorem exists_integralModel_of_baseChange {R : Type uR} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] {F : Type uF} [Field F]
    [Algebra R F] [IsFractionRing R F] {Ω : Type uΩ} [Field Ω] [Algebra F Ω] [Algebra R Ω]
    [IsScalarTower R F Ω] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation Ω Γ₀) (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1)
    [Algebra (ResidueField R) (ResidueField w.valuationSubring)]
    (halg : algebraMap (ResidueField R) (ResidueField w.valuationSubring) = residueHom w hR hm)
    (V : Submodule F Ω) [FiniteDimensional F V] (hV : finrank F V ≤ 6) {x y : Ω}
    (hmono : ∀ i, ![1, x, y, x ^ 2, x * y, y ^ 2, x ^ 3] i ∈ V) (hx : w x ≤ 1) (hy : w y ≤ 1)
    (P : ValuationSubring (ResidueField w.valuationSubring))
    (hP : IsDegreeOnePlace (ResidueField R) P) {π : ResidueField w.valuationSubring}
    (hπ : IsUniformizerAt P π) (hxP : P.valuation (reduce w x hx * π ^ 2) = 1)
    (hyP : P.valuation (reduce w y hy * π ^ 3) = 1)
    (hxO : ∀ O : ValuationSubring (ResidueField w.valuationSubring),
      IsConstPlace (ResidueField R) O → O ≠ P → reduce w x hx ∈ O)
    {kb Kb : Type*} [Field kb] [Field Kb] [IsAlgClosed kb] [Algebra (ResidueField R) kb]
    [Algebra.IsAlgebraic (ResidueField R) kb] [Algebra kb Kb]
    [Algebra (ResidueField w.valuationSubring) Kb] [Algebra (ResidueField R) Kb]
    [IsScalarTower (ResidueField R) kb Kb]
    [IsScalarTower (ResidueField R) (ResidueField w.valuationSubring) Kb]
    (hgen : IntermediateField.adjoin kb
      (Set.range (algebraMap (ResidueField w.valuationSubring) Kb)) = ⊤)
    (htr : TrdegLeOne (ResidueField R) (ResidueField w.valuationSubring))
    (σ : Kb ≃ₐ[kb] Kb)
    (hσ : ∀ Q : ValuationSubring Kb, IsDegreeOnePlace kb Q → Q.comap (σ : Kb →+* Kb) ≠ Q) :
    ∃ (W0 : WeierstrassCurve R) (e : Rˣ), IsUnit W0.Δ ∧
      (W0.map (algebraMap R Ω)).toAffine.Equation (algebraMap R Ω e * x)
        (algebraMap R Ω e * y) :=
  exists_integralModel w hR hm halg V hV hmono hx hy P hP.1 hπ hxP hyP hxO
    (not_hasSimplePoleOnlyAt_of_baseChange hgen htr hP σ hσ)

end IntegralModel

end ZInQ.Contrib.CMHeight62Full
