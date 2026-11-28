import Mathlib

/-!
# A group curve has no function with a single simple pole (node N9a)

Function-field formulation. A *place* of `K/k` is a valuation subring `O` of `K` containing the
constants. It has *degree one* if it is proper and its residue field is `k`. A function `f` has
*polar divisor exactly `1·P`* if `f ∉ P`, `𝔪_P · f ⊆ P` (a simple pole) and `f ∈ O` for every
other place `O` (no other pole).

* `adjoin_eq_top_of_hasSimplePoleOnlyAt`: if `K/k` has transcendence degree at most one and `f`
  has polar divisor exactly `1·P` with `P` of degree one, then `K = k(f)`. The pole spaces are
  `L(n·P) = k[f]_{≤ n}` (`exists_poly_of_mem_pow`).
* `false_of_hasSimplePoleOnlyAt`: over an algebraically closed field, if `K = k(f)` with such an
  `f`, then every `k`-automorphism of `K` fixes a degree-one place (it is a Möbius map in `f`).
* `not_hasSimplePoleOnlyAt`: hence, if some `k`-automorphism of `K` fixes no degree-one place
  (a translation by a geometric point other than the identity), no function has polar divisor
  exactly `1·P`.
* `not_hasSimplePoleOnlyAt_of_baseChange`: the same over any field `k`, with the automorphism
  living on a field `K̄` generated over an algebraic closure `k̄` by `K` (the function field of the
  geometric curve).
* `eq_algebraMap_of_mul_uniformizer_mem`, `..._of_baseChange`: equivalently `L(1·P) = k`.

Only Mathlib is used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open Polynomial

section Defs

variable (k : Type*) {K : Type*} [Field k] [Field K] [Algebra k K]

/-- A place of `K/k`: a valuation subring of `K` containing the constants. -/
def IsConstPlace (O : ValuationSubring K) : Prop :=
  ∀ c : k, algebraMap k K c ∈ O

/-- A degree-one place of `K/k`: a proper place with residue field `k`. -/
def IsDegreeOnePlace (O : ValuationSubring K) : Prop :=
  IsConstPlace k O ∧ O ≠ ⊤ ∧ ∀ x ∈ O, ∃ c : k, x - algebraMap k K c ∈ O.nonunits

/-- `f` has polar divisor exactly `1·P`: a simple pole at `P` and no other pole. -/
def HasSimplePoleOnlyAt (P : ValuationSubring K) (f : K) : Prop :=
  f ∉ P ∧ (∀ x ∈ P.nonunits, x * f ∈ P) ∧
    ∀ O : ValuationSubring K, IsConstPlace k O → O ≠ P → f ∈ O

/-- `π` is a uniformizer of `P`. -/
def IsUniformizerAt (P : ValuationSubring K) (π : K) : Prop :=
  π ≠ 0 ∧ π ∈ P.nonunits ∧ ∀ x ∈ P.nonunits, x * π⁻¹ ∈ P

variable (K) in
/-- `K/k` has transcendence degree at most one: `K` is algebraic over `k[x]` for every
transcendental `x`. -/
def TrdegLeOne : Prop :=
  ∀ x : K, Transcendental k x → Algebra.IsAlgebraic (Algebra.adjoin k {x}) K

end Defs

namespace GroupCurveNotP1

section Valuations

variable {K : Type*} [Field K]

theorem valuation_le_of_monic_root {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) {p : K[X]} (hp : p.Monic) {y : K} (hy : p.eval y = 0) {B : Γ₀}
    (hB : 1 ≤ B) (hc : ∀ i, v (p.coeff i) ≤ B) : v y ≤ B := by
  by_contra hlt
  rw [not_le] at hlt
  have hy1 : 1 < v y := lt_of_le_of_lt hB hlt
  have hy0 : v y ≠ 0 := (lt_trans zero_lt_one hy1).ne'
  have hsum := congrArg (Polynomial.eval y) hp.as_sum
  rw [hy] at hsum
  simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C] at hsum
  have hlt' : v (∑ i ∈ Finset.range p.natDegree, p.coeff i * y ^ i) < v y ^ p.natDegree := by
    apply Valuation.map_sum_lt v (pow_ne_zero _ hy0)
    intro i hi
    rw [map_mul, map_pow]
    have hi' : i + 1 ≤ p.natDegree := Finset.mem_range.1 hi
    calc v (p.coeff i) * v y ^ i ≤ B * v y ^ i := mul_le_mul_of_nonneg_right (hc i) zero_le
      _ < v y * v y ^ i := mul_lt_mul_of_pos_right hlt (pow_pos (zero_lt_one.trans hy1) i)
      _ = v y ^ (i + 1) := (pow_succ' _ _).symm
      _ ≤ v y ^ p.natDegree := pow_le_pow_right₀ hy1.le hi'
  have heq : y ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i * y ^ i :=
    eq_neg_of_add_eq_zero_left hsum.symm
  have h2 := congrArg v heq
  rw [Valuation.map_neg, map_pow] at h2
  rw [← h2] at hlt'
  exact lt_irrefl _ hlt'

theorem valuation_le_of_isIntegral {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) {A : Type*} [CommRing A] [Algebra A K] {B : Γ₀} (hB : 1 ≤ B)
    (hA : ∀ a : A, v (algebraMap A K a) ≤ B) {y : K} (hy : IsIntegral A y) : v y ≤ B := by
  obtain ⟨p, hpm, hpe⟩ := hy
  refine valuation_le_of_monic_root v (hpm.map (algebraMap A K)) ?_ hB ?_
  · rw [eval_map]; exact hpe
  · intro i; rw [coeff_map]; exact hA _

theorem mem_of_isIntegral (O : ValuationSubring K) {A : Type*} [CommRing A] [Algebra A K]
    (hA : ∀ a : A, algebraMap A K a ∈ O) {y : K} (hy : IsIntegral A y) : y ∈ O := by
  rw [← O.valuation_le_one_iff]
  exact valuation_le_of_isIntegral O.valuation le_rfl
    (fun a => (O.valuation_le_one_iff _).2 (hA a)) hy

variable {O : ValuationSubring K}

theorem mem_of_mem_nonunits {x : K} (hx : x ∈ O.nonunits) : x ∈ O :=
  (O.valuation_le_one_iff x).1 (O.mem_nonunits_iff.1 hx).le

theorem mul_mem_nonunits {x y : K} (hx : x ∈ O.nonunits) (hy : y ∈ O) :
    x * y ∈ O.nonunits := by
  rw [O.mem_nonunits_iff, map_mul]
  have h1 := O.mem_nonunits_iff.1 hx
  have h2 := (O.valuation_le_one_iff y).2 hy
  calc O.valuation x * O.valuation y ≤ O.valuation x * 1 :=
        mul_le_mul_of_nonneg_left h2 zero_le
    _ = O.valuation x := mul_one _
    _ < 1 := h1

theorem mem_nonunits_of_inv_not_mem {x : K} (_hx : x ∈ O) (hinv : x⁻¹ ∉ O) :
    x ∈ O.nonunits :=
  O.mem_nonunits_iff_or.2 (Or.inr hinv)

theorem inv_not_mem_of_mem_nonunits {x : K} (hx : x ∈ O.nonunits) (hx0 : x ≠ 0) : x⁻¹ ∉ O :=
  (O.mem_nonunits_iff_or.1 hx).resolve_left hx0

theorem mem_nonunits_comap {L : Type*} [Field L] {O : ValuationSubring L} {φ : K →+* L}
    {x : K} : x ∈ (O.comap φ).nonunits ↔ φ x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem eq_of_le_of_nonunits {A B : ValuationSubring K} (hAB : A ≤ B)
    (hn : ∀ x ∈ A.nonunits, x ∈ B.nonunits) : A = B := by
  refine le_antisymm hAB fun x hx => ?_
  by_contra hxA
  have hx0 : x ≠ 0 := fun h => hxA (h ▸ A.zero_mem)
  have hinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA
  have hn' : x⁻¹ ∈ A.nonunits := mem_nonunits_of_inv_not_mem hinv (by rwa [inv_inv])
  exact inv_not_mem_of_mem_nonunits (hn _ hn') (inv_ne_zero hx0) (by rwa [inv_inv])

end Valuations

section Const

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {O : ValuationSubring K}

theorem valuation_algebraMap_eq_one (hO : IsConstPlace k O) {c : k} (hc : c ≠ 0) :
    O.valuation (algebraMap k K c) = 1 := by
  have h1 := (O.valuation_le_one_iff _).2 (hO c)
  have h2 := (O.valuation_le_one_iff _).2 (hO c⁻¹)
  have h3 : O.valuation (algebraMap k K c) * O.valuation (algebraMap k K c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  rw [not_le] at hlt
  have : O.valuation (algebraMap k K c) * O.valuation (algebraMap k K c⁻¹) < 1 :=
    calc _ ≤ O.valuation (algebraMap k K c) * 1 := mul_le_mul_of_nonneg_left h2 zero_le
      _ < 1 := by rw [mul_one]; exact hlt
  exact this.ne h3

theorem eq_zero_of_algebraMap_mem_nonunits (hO : IsConstPlace k O) {c : k}
    (h : algebraMap k K c ∈ O.nonunits) : c = 0 := by
  by_contra hc
  have := O.mem_nonunits_iff.1 h
  rw [valuation_algebraMap_eq_one hO hc] at this
  exact lt_irrefl _ this

/-- The `k`-subalgebra underlying a place. -/
def placeSubalgebra (O : ValuationSubring K) (hO : IsConstPlace k O) : Subalgebra k K :=
  { O.toSubring with algebraMap_mem' := hO }

theorem adjoin_le_place (hO : IsConstPlace k O) {x : K} (hx : x ∈ O) :
    Algebra.adjoin k {x} ≤ placeSubalgebra O hO :=
  Algebra.adjoin_le (Set.singleton_subset_iff.2 hx)

theorem aeval_mem_place (hO : IsConstPlace k O) {x : K} (hx : x ∈ O) (p : k[X]) :
    aeval x p ∈ O :=
  adjoin_le_place hO hx (aeval_mem_adjoin_singleton k x)

theorem valuation_aeval_eq_one (hO : IsConstPlace k O) {z : K} {α : k}
    (hz : z - algebraMap k K α ∈ O.nonunits) {q : k[X]} (hq : q.eval α ≠ 0) :
    O.valuation (aeval z q) = 1 := by
  obtain ⟨r, hr⟩ := (X_sub_C_dvd_sub_C_eval : X - C α ∣ q - C (q.eval α))
  have hzO : z ∈ O := by
    have := add_mem (mem_of_mem_nonunits hz) (hO α)
    simpa using this
  have h1 : aeval z q = algebraMap k K (q.eval α) + (z - algebraMap k K α) * aeval z r := by
    have := congrArg (aeval z) hr
    simp only [map_sub, aeval_C, map_mul, aeval_X] at this
    linear_combination this
  rw [h1, Valuation.map_add_eq_of_lt_left, valuation_algebraMap_eq_one hO hq]
  rw [valuation_algebraMap_eq_one hO hq]
  exact O.mem_nonunits_iff.1 (mul_mem_nonunits hz (aeval_mem_place hO hzO r))

theorem exists_constPlace_not_mem {h : K} (hh : ¬ IsIntegral k h) :
    ∃ O : ValuationSubring K, IsConstPlace k O ∧ h ∉ O := by
  have hR : h ∉ (integralClosure k K).toSubring := hh
  obtain ⟨V, hV, hhV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hR
  exact ⟨V, fun c => hV (isIntegral_algebraMap : IsIntegral k (algebraMap k K c)), hhV⟩

theorem isIntegral_of_forall_mem {h : K}
    (hh : ∀ O : ValuationSubring K, IsConstPlace k O → h ∈ O) : IsIntegral k h := by
  by_contra hn
  obtain ⟨O, hO, hO'⟩ := exists_constPlace_not_mem hn
  exact hO' (hh O hO)

end Const

section Transport

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem mem_comap_algEquiv {O : ValuationSubring K} (σ : K ≃ₐ[k] K) {x : K} :
    x ∈ O.comap (σ : K →+* K) ↔ σ x ∈ O :=
  Iff.rfl

theorem comap_comap_symm (O : ValuationSubring K) (σ : K ≃ₐ[k] K) :
    (O.comap (σ.symm : K →+* K)).comap (σ : K →+* K) = O := by
  ext x
  simp only [mem_comap_algEquiv, AlgEquiv.symm_apply_apply]

theorem comap_symm_comap (O : ValuationSubring K) (σ : K ≃ₐ[k] K) :
    (O.comap (σ : K →+* K)).comap (σ.symm : K →+* K) = O := by
  ext x
  simp only [mem_comap_algEquiv, AlgEquiv.apply_symm_apply]

theorem isConstPlace_comap (σ : K ≃ₐ[k] K) {O : ValuationSubring K} (hO : IsConstPlace k O) :
    IsConstPlace k (O.comap (σ : K →+* K)) := fun c => by
  rw [mem_comap_algEquiv, AlgEquiv.commutes]; exact hO c

theorem isDegreeOnePlace_comap (σ : K ≃ₐ[k] K) {O : ValuationSubring K}
    (hO : IsDegreeOnePlace k O) : IsDegreeOnePlace k (O.comap (σ : K →+* K)) := by
  refine ⟨isConstPlace_comap σ hO.1, ?_, ?_⟩
  · intro htop
    apply hO.2.1
    rw [eq_top_iff]
    intro x _
    have : σ.symm x ∈ O.comap (σ : K →+* K) := by
      rw [htop]; exact ValuationSubring.mem_top _
    rwa [mem_comap_algEquiv, AlgEquiv.apply_symm_apply] at this
  · intro x hx
    rw [mem_comap_algEquiv] at hx
    obtain ⟨c, hc⟩ := hO.2.2 _ hx
    refine ⟨c, ?_⟩
    rw [mem_nonunits_comap]
    have : (σ : K →+* K) (x - algebraMap k K c) = σ x - algebraMap k K c := by
      change σ (x - algebraMap k K c) = _
      rw [map_sub, AlgEquiv.commutes]
    rw [this]; exact hc

theorem hasSimplePoleOnlyAt_comap (σ : K ≃ₐ[k] K) {O : ValuationSubring K} {f : K}
    (hf : HasSimplePoleOnlyAt k O f) :
    HasSimplePoleOnlyAt k (O.comap (σ : K →+* K)) (σ.symm f) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_comap_algEquiv, AlgEquiv.apply_symm_apply]; exact hf.1
  · intro x hx
    rw [mem_nonunits_comap] at hx
    rw [mem_comap_algEquiv, map_mul, AlgEquiv.apply_symm_apply]
    exact hf.2.1 _ hx
  · intro O' hO' hne
    have h1 : IsConstPlace k (O'.comap (σ.symm : K →+* K)) := isConstPlace_comap σ.symm hO'
    have h2 : O'.comap (σ.symm : K →+* K) ≠ O := by
      intro heq; apply hne; rw [← heq, comap_comap_symm]
    have := hf.2.2 _ h1 h2
    exact this

end Transport

section PoleSpaces

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {P : ValuationSubring K} {f : K}

theorem eq_algebraMap_of_forall_mem (hP : IsDegreeOnePlace k P) {h : K}
    (hh : ∀ O : ValuationSubring K, IsConstPlace k O → h ∈ O) :
    ∃ c : k, h = algebraMap k K c := by
  have hint : IsIntegral k h := isIntegral_of_forall_mem hh
  obtain ⟨c, hc⟩ := hP.2.2 h (hh P hP.1)
  refine ⟨c, ?_⟩
  by_contra hne
  have hy0 : h - algebraMap k K c ≠ 0 := sub_ne_zero.2 hne
  have hyint : IsIntegral k (h - algebraMap k K c) := hint.sub isIntegral_algebraMap
  exact inv_not_mem_of_mem_nonunits hc hy0 (mem_of_isIntegral P hP.1 hyint.inv)

theorem ne_zero_of_hasSimplePoleOnlyAt (hf : HasSimplePoleOnlyAt k P f) : f ≠ 0 :=
  fun h0 => hf.1 (h0 ▸ P.zero_mem)

theorem sub_ne_zero_of_hasSimplePoleOnlyAt (hP : IsConstPlace k P)
    (hf : HasSimplePoleOnlyAt k P f) (c : k) : f - algebraMap k K c ≠ 0 :=
  fun h => hf.1 (by rw [sub_eq_zero.1 h]; exact hP c)

theorem transcendental_of_hasSimplePoleOnlyAt (hP : IsConstPlace k P)
    (hf : HasSimplePoleOnlyAt k P f) : Transcendental k f :=
  fun halg => hf.1 (mem_of_isIntegral P hP halg.isIntegral)

/-- Pole spaces: `L(n·P) = k[f]_{≤ n}`. -/
theorem exists_poly_of_mem_pow (hP : IsDegreeOnePlace k P) (hf : HasSimplePoleOnlyAt k P f) :
    ∀ (n : ℕ) (h : K), (∀ O : ValuationSubring K, IsConstPlace k O → O ≠ P → h ∈ O) →
      h * f⁻¹ ^ n ∈ P → ∃ p : k[X], p.natDegree ≤ n ∧ h = aeval f p := by
  have hf0 := ne_zero_of_hasSimplePoleOnlyAt hf
  intro n
  induction n with
  | zero =>
    intro h hO hP0
    rw [pow_zero, mul_one] at hP0
    obtain ⟨c, rfl⟩ := eq_algebraMap_of_forall_mem hP (fun O hO' => by
      by_cases hOP : O = P
      · exact hOP ▸ hP0
      · exact hO O hO' hOP)
    exact ⟨C c, by simp, by simp⟩
  | succ n ih =>
    intro h hO hPn
    obtain ⟨c, hc⟩ := hP.2.2 _ hPn
    have h1 := hf.2.1 _ hc
    have hO' : ∀ O : ValuationSubring K, IsConstPlace k O → O ≠ P →
        h - algebraMap k K c * f ^ (n + 1) ∈ O := fun O hO1 hO2 =>
      sub_mem (hO O hO1 hO2) (mul_mem (hO1 c) (pow_mem (hf.2.2 O hO1 hO2) _))
    have key1 : f⁻¹ ^ (n + 1) * f = f⁻¹ ^ n := by
      rw [pow_succ, mul_assoc, inv_mul_cancel₀ hf0, mul_one]
    have key2 : f ^ (n + 1) * f⁻¹ ^ n = f := by
      rw [pow_succ, mul_comm (f ^ n) f, mul_assoc, ← mul_pow, mul_inv_cancel₀ hf0, one_pow,
        mul_one]
    have hP' : (h - algebraMap k K c * f ^ (n + 1)) * f⁻¹ ^ n ∈ P := by
      have : (h - algebraMap k K c * f ^ (n + 1)) * f⁻¹ ^ n =
          (h * f⁻¹ ^ (n + 1) - algebraMap k K c) * f := by
        linear_combination (-h) * key1 + (-algebraMap k K c) * key2
      rw [this]; exact h1
    obtain ⟨p, hpdeg, hp⟩ := ih _ hO' hP'
    refine ⟨p + C c * X ^ (n + 1), ?_, ?_⟩
    · exact (natDegree_add_le _ _).trans
        (max_le (hpdeg.trans (Nat.le_succ n)) (natDegree_C_mul_X_pow_le c (n + 1)))
    · rw [map_add, ← hp]; simp

theorem valuation_aeval_le {O : ValuationSubring K} (hO : IsConstPlace k O) {x : K}
    (hx : 1 ≤ O.valuation x) (r : k[X]) :
    O.valuation (aeval x r) ≤ O.valuation x ^ r.natDegree := by
  rw [aeval_eq_sum_range]
  apply Valuation.map_sum_le
  intro i hi
  rw [Algebra.smul_def, map_mul, map_pow]
  calc O.valuation (algebraMap k K (r.coeff i)) * O.valuation x ^ i
        ≤ 1 * O.valuation x ^ i :=
          mul_le_mul_of_nonneg_right ((O.valuation_le_one_iff _).2 (hO _)) zero_le
    _ = O.valuation x ^ i := one_mul _
    _ ≤ O.valuation x ^ r.natDegree :=
        pow_le_pow_right₀ hx (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

end PoleSpaces

end GroupCurveNotP1

open GroupCurveNotP1

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {P : ValuationSubring K} {f : K}

/-- A function with polar divisor exactly `1·P` (`P` of degree one) generates `K` over `k`,
when `K/k` has transcendence degree at most one. -/
theorem adjoin_eq_top_of_hasSimplePoleOnlyAt (htr : TrdegLeOne k K)
    (hP : IsDegreeOnePlace k P) (hf : HasSimplePoleOnlyAt k P f) :
    IntermediateField.adjoin k {f} = ⊤ := by
  have halg := htr f (transcendental_of_hasSimplePoleOnlyAt hP.1 hf)
  have hf0 := ne_zero_of_hasSimplePoleOnlyAt hf
  have hV : 1 < P.valuation f := not_le.1 (mt (P.valuation_le_one_iff f).1 hf.1)
  have hV0 : P.valuation f ≠ 0 := (Valuation.ne_zero_iff _).2 hf0
  rw [eq_top_iff]
  intro h _
  obtain ⟨y, hy0, hyint⟩ := (halg.isAlgebraic h).exists_integral_multiple
  rw [Algebra.smul_def] at hyint
  have hAO : ∀ O : ValuationSubring K, IsConstPlace k O → O ≠ P →
      ∀ a : Algebra.adjoin k {f}, algebraMap (Algebra.adjoin k {f}) K a ∈ O :=
    fun O hO hOP a => adjoin_le_place hO (hf.2.2 O hO hOP) a.2
  have hz : ∀ O : ValuationSubring K, IsConstPlace k O → O ≠ P →
      algebraMap (Algebra.adjoin k {f}) K y * h ∈ O :=
    fun O hO hOP => mem_of_isIntegral O (hAO O hO hOP) hyint
  have hbound : ∀ a : Algebra.adjoin k {f}, ∃ d : ℕ,
      P.valuation (algebraMap (Algebra.adjoin k {f}) K a) ≤ P.valuation f ^ d := by
    intro a
    obtain ⟨r, hr⟩ : (a : K) ∈ (aeval (R := k) f).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact a.2
    exact ⟨r.natDegree, by
      change P.valuation (a : K) ≤ _
      rw [← hr]; exact valuation_aeval_le hP.1 hV.le r⟩
  choose d hd using hbound
  obtain ⟨q, hqm, hqe⟩ := hyint
  set D := ∑ i ∈ Finset.range (q.natDegree + 1), d (q.coeff i)
  have hD : P.valuation (algebraMap (Algebra.adjoin k {f}) K y * h) ≤ P.valuation f ^ D := by
    refine valuation_le_of_monic_root P.valuation (hqm.map _) (by rw [eval_map]; exact hqe)
      (one_le_pow₀ hV.le) fun i => ?_
    rw [coeff_map]
    by_cases hi : i ≤ q.natDegree
    · refine (hd _).trans (pow_le_pow_right₀ hV.le ?_)
      exact Finset.single_le_sum (f := fun j => d (q.coeff j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero, map_zero]
      exact zero_le
  have hzP : algebraMap (Algebra.adjoin k {f}) K y * h * f⁻¹ ^ D ∈ P := by
    rw [← P.valuation_le_one_iff, map_mul, map_pow, map_inv₀]
    calc _ ≤ P.valuation f ^ D * (P.valuation f)⁻¹ ^ D := mul_le_mul_of_nonneg_right hD zero_le
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hV0, one_pow]
  obtain ⟨p, -, hp⟩ := exists_poly_of_mem_pow hP hf D _ hz hzP
  have hyK : algebraMap (Algebra.adjoin k {f}) K y ≠ 0 := fun h0 => hy0 (Subtype.ext h0)
  have hyK' : algebraMap (Algebra.adjoin k {f}) K y ∈ IntermediateField.adjoin k {f} :=
    IntermediateField.algebra_adjoin_le_adjoin k {f} y.2
  have hzK : algebraMap (Algebra.adjoin k {f}) K y * h ∈ IntermediateField.adjoin k {f} := by
    rw [hp]; exact IntermediateField.algebra_adjoin_le_adjoin k {f}
      (aeval_mem_adjoin_singleton k f)
  have : h = algebraMap (Algebra.adjoin k {f}) K y * h *
      (algebraMap (Algebra.adjoin k {f}) K y)⁻¹ := by
    rw [mul_comm (algebraMap _ K y) h, mul_assoc, mul_inv_cancel₀ hyK, mul_one]
  rw [this]
  exact mul_mem hzK (inv_mem hyK')

namespace GroupCurveNotP1

/-- Under `σ`, the function `σ⁻¹ f` is a Möbius transform of `f` (if `σ` moves `P`). -/
theorem exists_mobius (hP : IsDegreeOnePlace k P) (hf : HasSimplePoleOnlyAt k P f)
    (σ : K ≃ₐ[k] K) (hσP : P.comap (σ : K →+* K) ≠ P) :
    ∃ a b β : k, σ.symm f * (f - algebraMap k K β) = algebraMap k K a + algebraMap k K b * f := by
  have hQ : IsDegreeOnePlace k (P.comap (σ : K →+* K)) := isDegreeOnePlace_comap σ hP
  have hg : HasSimplePoleOnlyAt k (P.comap (σ : K →+* K)) (σ.symm f) :=
    hasSimplePoleOnlyAt_comap σ hf
  have hfQ : f ∈ P.comap (σ : K →+* K) := hf.2.2 _ hQ.1 hσP
  obtain ⟨β, hβ⟩ := hQ.2.2 f hfQ
  have hgP : σ.symm f ∈ P := hg.2.2 P hP.1 (Ne.symm hσP)
  have hfinv : f⁻¹ ∈ P := (P.mem_or_inv_mem f).resolve_left hf.1
  have hf0 := ne_zero_of_hasSimplePoleOnlyAt hf
  obtain ⟨p, hpdeg, hp⟩ := exists_poly_of_mem_pow hP hf 1 (σ.symm f * (f - algebraMap k K β))
    (fun O hO hOP => by
      by_cases hOQ : O = P.comap (σ : K →+* K)
      · rw [hOQ, mul_comm]; exact hg.2.1 _ hβ
      · exact mul_mem (hg.2.2 O hO hOQ) (sub_mem (hf.2.2 O hO hOP) (hO β)))
    (by
      rw [pow_one, mul_assoc, sub_mul, mul_inv_cancel₀ hf0]
      exact mul_mem hgP (sub_mem (one_mem _) (mul_mem (hP.1 β) hfinv)))
  refine ⟨p.coeff 0, p.coeff 1, β, ?_⟩
  have hp2 := eq_X_add_C_of_natDegree_le_one hpdeg
  rw [hp]
  conv_lhs => rw [hp2]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  ring

section RatPlace

variable (hft : Transcendental k f) (htop : IntermediateField.adjoin k {f} = ⊤)

include hft in
theorem ratPlace_aux (α : k) (r s : k[X]) :
    (∃ p q : k[X], q.eval α ≠ 0 ∧ (aeval f r / aeval f s) * aeval f q = aeval f p) ∨
    (∃ p q : k[X], q.eval α ≠ 0 ∧ (aeval f r / aeval f s)⁻¹ * aeval f q = aeval f p) := by
  have hinj := transcendental_iff_injective.1 hft
  have hne : ∀ t : k[X], t ≠ 0 → aeval f t ≠ 0 :=
    fun t ht h => ht (hinj (by rw [h, map_zero]))
  by_cases hr : r = 0
  · left; exact ⟨0, 1, by simp, by simp [hr]⟩
  by_cases hs : s = 0
  · left; exact ⟨0, 1, by simp, by simp [hs]⟩
  obtain ⟨r', hr', hr'd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr α
  obtain ⟨s', hs', hs'd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd s hs α
  have hr'α : r'.eval α ≠ 0 := fun h => hr'd (dvd_iff_isRoot.2 h)
  have hs'α : s'.eval α ≠ 0 := fun h => hs'd (dvd_iff_isRoot.2 h)
  set m := rootMultiplicity α r
  set n := rootMultiplicity α s
  have hfα : f - algebraMap k K α ≠ 0 := by
    have := hne (X - C α) (X_sub_C_ne_zero α); simpa using this
  have hR : aeval f r = (f - algebraMap k K α) ^ m * aeval f r' := by
    rw [hr']; simp
  have hS : aeval f s = (f - algebraMap k K α) ^ n * aeval f s' := by
    rw [hs']; simp
  have hS'0 : aeval f s' ≠ 0 := hne s' (fun h => hs'α (by simp [h]))
  have hR'0 : aeval f r' ≠ 0 := hne r' (fun h => hr'α (by simp [h]))
  have hFn : (f - algebraMap k K α) ^ n ≠ 0 := pow_ne_zero _ hfα
  have hFm : (f - algebraMap k K α) ^ m ≠ 0 := pow_ne_zero _ hfα
  rcases le_or_gt n m with hnm | hmn
  · left
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hnm
    refine ⟨(X - C α) ^ d * r', s', hs'α, ?_⟩
    rw [hR, hS, hd, pow_add]
    simp only [map_mul, map_pow, map_sub, aeval_X, aeval_C]
    field_simp
  · right
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hmn
    have hd' : n = m + (d + 1) := by omega
    refine ⟨(X - C α) ^ (d + 1) * s', r', hr'α, ?_⟩
    rw [hR, hS, hd', pow_add]
    simp only [map_mul, map_pow, map_sub, aeval_X, aeval_C]
    field_simp

/-- The place of `k(f)` where `f = α`: `k[f]` localized at `f - α`. -/
def ratPlace (α : k) : ValuationSubring K where
  carrier := {x | ∃ p q : k[X], q.eval α ≠ 0 ∧ x * aeval f q = aeval f p}
  zero_mem' := ⟨0, 1, by simp, by simp⟩
  one_mem' := ⟨1, 1, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨p1, q1, hq1, e1⟩ ⟨p2, q2, hq2, e2⟩
    refine ⟨p1 * q2 + p2 * q1, q1 * q2, by simp [hq1, hq2], ?_⟩
    simp only [map_add, map_mul]
    linear_combination aeval f q2 * e1 + aeval f q1 * e2
  mul_mem' := by
    rintro x y ⟨p1, q1, hq1, e1⟩ ⟨p2, q2, hq2, e2⟩
    refine ⟨p1 * p2, q1 * q2, by simp [hq1, hq2], ?_⟩
    simp only [map_mul]
    linear_combination (y * aeval f q2) * e1 + aeval f p1 * e2
  neg_mem' := by
    rintro x ⟨p, q, hq, e⟩
    refine ⟨-p, q, hq, ?_⟩
    simp only [map_neg]
    linear_combination -e
  mem_or_inv_mem' := by
    intro x
    have hx : x ∈ IntermediateField.adjoin k {f} := htop ▸ IntermediateField.mem_top
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k x).1 hx
    exact ratPlace_aux hft α r s

variable {hft htop}

theorem mem_ratPlace {α : k} {x : K} :
    x ∈ ratPlace hft htop α ↔ ∃ p q : k[X], q.eval α ≠ 0 ∧ x * aeval f q = aeval f p :=
  Iff.rfl

theorem isConstPlace_ratPlace (α : k) : IsConstPlace k (ratPlace hft htop α) :=
  fun c => ⟨C c, 1, by simp, by simp⟩

theorem sub_mem_ratPlace (α : k) : f - algebraMap k K α ∈ ratPlace hft htop α :=
  ⟨X - C α, 1, by simp, by simp⟩

theorem inv_sub_not_mem_ratPlace (α : k) : (f - algebraMap k K α)⁻¹ ∉ ratPlace hft htop α := by
  rintro ⟨p, q, hq, e⟩
  have hinj := transcendental_iff_injective.1 hft
  have hfα : f - algebraMap k K α ≠ 0 := by
    intro h
    have : aeval f (X - C α) = aeval f (0 : k[X]) := by simpa using h
    exact X_sub_C_ne_zero α (hinj this)
  have h1 : aeval f q = aeval f ((X - C α) * p) := by
    rw [map_mul, ← e, ← mul_assoc]; simp [mul_inv_cancel₀ hfα]
  have h2 := hinj h1
  apply hq
  rw [h2]; simp

theorem sub_mem_nonunits_ratPlace (α : k) :
    f - algebraMap k K α ∈ (ratPlace hft htop α).nonunits :=
  mem_nonunits_of_inv_not_mem (sub_mem_ratPlace α) (inv_sub_not_mem_ratPlace α)

theorem exists_sub_eq_mul {α : k} {x : K} (hx : x ∈ ratPlace hft htop α) :
    ∃ c : k, ∃ y ∈ ratPlace hft htop α, x - algebraMap k K c = (f - algebraMap k K α) * y := by
  obtain ⟨p, q, hq, e⟩ := hx
  have hinj := transcendental_iff_injective.1 hft
  have hQ0 : aeval f q ≠ 0 := fun h => hq (by
    have : q = 0 := hinj (by rw [h, map_zero])
    simp [this])
  set c := p.eval α / q.eval α
  have hroot : (p - C c * q).IsRoot α := by
    simp only [IsRoot.def, eval_sub, eval_mul, eval_C, c]
    field_simp
    ring
  have hdiv := mul_divByMonic_eq_iff_isRoot.2 hroot
  set r := (p - C c * q) /ₘ (X - C α)
  refine ⟨c, aeval f r / aeval f q, ⟨r, q, hq, div_mul_cancel₀ _ hQ0⟩, ?_⟩
  have h2 : aeval f p - algebraMap k K c * aeval f q =
      (f - algebraMap k K α) * aeval f r := by
    have := congrArg (aeval f) hdiv
    simp only [map_mul, map_sub, aeval_X, aeval_C] at this
    exact this.symm
  have hx' : x = aeval f p / aeval f q := by rw [← e, mul_div_cancel_right₀ _ hQ0]
  rw [hx', mul_div_assoc', ← h2]
  field_simp

theorem eq_mul_of_mem_nonunits {α : k} {x : K} (hx : x ∈ (ratPlace hft htop α).nonunits) :
    ∃ y ∈ ratPlace hft htop α, x = (f - algebraMap k K α) * y := by
  obtain ⟨c, y, hy, e⟩ := exists_sub_eq_mul (mem_of_mem_nonunits hx)
  have hc : algebraMap k K c ∈ (ratPlace hft htop α).nonunits := by
    have : algebraMap k K c = x - (f - algebraMap k K α) * y := by rw [← e]; ring
    rw [this]
    exact sub_mem hx (mul_mem_nonunits (sub_mem_nonunits_ratPlace α) hy)
  have hc0 := eq_zero_of_algebraMap_mem_nonunits (isConstPlace_ratPlace α) hc
  refine ⟨y, hy, ?_⟩
  rw [← e, hc0, map_zero, sub_zero]

theorem isDegreeOnePlace_ratPlace (α : k) : IsDegreeOnePlace k (ratPlace hft htop α) := by
  refine ⟨isConstPlace_ratPlace α, fun htop' => ?_, fun x hx => ?_⟩
  · apply inv_sub_not_mem_ratPlace (hft := hft) (htop := htop) α
    rw [htop']; exact ValuationSubring.mem_top _
  · obtain ⟨c, y, hy, e⟩ := exists_sub_eq_mul hx
    exact ⟨c, e ▸ mul_mem_nonunits (sub_mem_nonunits_ratPlace α) hy⟩

/-- Uniqueness: the only place where `f - α` vanishes is `ratPlace α`. -/
theorem ratPlace_eq {α : k} {O : ValuationSubring K} (hO : IsConstPlace k O)
    (hu : f - algebraMap k K α ∈ O.nonunits) : ratPlace hft htop α = O := by
  have hle : ratPlace hft htop α ≤ O := by
    rintro x ⟨p, q, hq, e⟩
    have hfO : f ∈ O := by
      have := add_mem (mem_of_mem_nonunits hu) (hO α); simpa using this
    have h1 := valuation_aeval_eq_one hO hu hq
    rw [← O.valuation_le_one_iff]
    have h2 := congrArg O.valuation e
    rw [map_mul, h1, mul_one] at h2
    rw [h2, O.valuation_le_one_iff]
    exact aeval_mem_place hO hfO p
  refine eq_of_le_of_nonunits hle fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := eq_mul_of_mem_nonunits hx
  exact mul_mem_nonunits hu (hle hy)

theorem comap_ratPlace_eq (σ : K ≃ₐ[k] K) {α : k}
    (hg : σ.symm f - algebraMap k K α ∈ (ratPlace hft htop α).nonunits) :
    (ratPlace hft htop α).comap (σ : K →+* K) = ratPlace hft htop α := by
  set Q := ratPlace hft htop α
  have hQ := isConstPlace_ratPlace (hft := hft) (htop := htop) α
  have hgQ : σ.symm f ∈ Q := by
    have := add_mem (mem_of_mem_nonunits hg) (hQ α); simpa using this
  have hmap : ∀ x ∈ Q, σ.symm x ∈ Q := by
    rintro x ⟨p, q, hq, e⟩
    have e' : σ.symm x * aeval (σ.symm f) q = aeval (σ.symm f) p := by
      rw [aeval_algHom_apply, aeval_algHom_apply, ← map_mul, e]
    have h1 := valuation_aeval_eq_one hQ hg hq
    rw [← Q.valuation_le_one_iff]
    have h2 := congrArg Q.valuation e'
    rw [map_mul, h1, mul_one] at h2
    rw [h2, Q.valuation_le_one_iff]
    exact aeval_mem_place hQ hgQ p
  have hEq : Q = Q.comap (σ.symm : K →+* K) := by
    refine eq_of_le_of_nonunits (fun x hx => hmap x hx) fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := eq_mul_of_mem_nonunits hx
    rw [mem_nonunits_comap]
    change σ.symm ((f - algebraMap k K α) * y) ∈ Q.nonunits
    rw [map_mul, map_sub, AlgEquiv.commutes]
    exact mul_mem_nonunits hg (hmap y hy)
  have h3 := congrArg (fun O : ValuationSubring K => O.comap (σ : K →+* K)) hEq
  rw [comap_comap_symm] at h3
  exact h3

end RatPlace

end GroupCurveNotP1

/-- Over an algebraically closed field: if `K = k(f)` and `f` has polar divisor exactly `1·P`,
then every `k`-automorphism of `K` fixes some degree-one place. -/
theorem false_of_hasSimplePoleOnlyAt [IsAlgClosed k]
    (htop : IntermediateField.adjoin k {f} = ⊤) (hP : IsDegreeOnePlace k P)
    (hf : HasSimplePoleOnlyAt k P f) (σ : K ≃ₐ[k] K)
    (hσ : ∀ Q : ValuationSubring K, IsDegreeOnePlace k Q → Q.comap (σ : K →+* K) ≠ Q) :
    False := by
  have hft := transcendental_of_hasSimplePoleOnlyAt hP.1 hf
  obtain ⟨a, b, β, hab⟩ := exists_mobius hP hf σ (hσ P hP)
  have hg_nc : ∀ c : k, σ.symm f ≠ algebraMap k K c := by
    intro c hc
    apply hf.1
    have : f = algebraMap k K c := by
      rw [← σ.apply_symm_apply f, hc, AlgEquiv.commutes]
    rw [this]; exact hP.1 c
  have hdeg : (X ^ 2 - C (β + b) * X - C a : k[X]).natDegree = 2 := by compute_degree!
  have hne0 : (X ^ 2 - C (β + b) * X - C a : k[X]) ≠ 0 :=
    ne_zero_of_natDegree_gt (n := 0) (by rw [hdeg]; norm_num)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (X ^ 2 - C (β + b) * X - C a)
    (by rw [degree_eq_natDegree hne0, hdeg]; norm_num)
  have hα' : α ^ 2 - (β + b) * α - a = 0 := by simpa using hα
  have hα'' : algebraMap k K α ^ 2 - (algebraMap k K β + algebraMap k K b) * algebraMap k K α -
      algebraMap k K a = 0 := by
    have := congrArg (algebraMap k K) hα'
    simp only [map_sub, map_mul, map_pow, map_add, map_zero] at this
    exact this
  have hfβ := sub_ne_zero_of_hasSimplePoleOnlyAt hP.1 hf β
  have hfα := sub_ne_zero_of_hasSimplePoleOnlyAt hP.1 hf α
  have hkey : (σ.symm f - algebraMap k K α) * (f - algebraMap k K β) =
      algebraMap k K (b - α) * (f - algebraMap k K α) := by
    rw [map_sub]
    linear_combination hab - hα''
  have hαβ : α ≠ β := by
    intro heq
    apply hg_nc b
    have h1 := hkey
    rw [← heq] at h1
    have h2 := mul_right_cancel₀ hfα h1
    rw [map_sub] at h2
    linear_combination h2
  have hfβinv : (f - algebraMap k K β)⁻¹ ∈ GroupCurveNotP1.ratPlace hft htop α :=
    ⟨1, X - C β, by simp [sub_ne_zero.2 hαβ], by simp [inv_mul_cancel₀ hfβ]⟩
  have hgQ : σ.symm f - algebraMap k K α ∈ (GroupCurveNotP1.ratPlace hft htop α).nonunits := by
    have : σ.symm f - algebraMap k K α = (f - algebraMap k K α) *
        (algebraMap k K (b - α) * (f - algebraMap k K β)⁻¹) := by
      calc σ.symm f - algebraMap k K α
            = (σ.symm f - algebraMap k K α) * (f - algebraMap k K β) *
              (f - algebraMap k K β)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hfβ, mul_one]
        _ = algebraMap k K (b - α) * (f - algebraMap k K α) * (f - algebraMap k K β)⁻¹ := by
              rw [hkey]
        _ = _ := by ring
    rw [this]
    exact mul_mem_nonunits (sub_mem_nonunits_ratPlace α)
      (mul_mem (isConstPlace_ratPlace α _) hfβinv)
  exact hσ _ (isDegreeOnePlace_ratPlace α) (comap_ratPlace_eq σ hgQ)

/-- **N9a, algebraically closed constants.** If some `k`-automorphism of `K` fixes no
degree-one place, no function has polar divisor exactly `1·P`. -/
theorem not_hasSimplePoleOnlyAt [IsAlgClosed k] (htr : TrdegLeOne k K)
    (hP : IsDegreeOnePlace k P) (σ : K ≃ₐ[k] K)
    (hσ : ∀ Q : ValuationSubring K, IsDegreeOnePlace k Q → Q.comap (σ : K →+* K) ≠ Q)
    (f : K) : ¬ HasSimplePoleOnlyAt k P f := fun hf =>
  false_of_hasSimplePoleOnlyAt (adjoin_eq_top_of_hasSimplePoleOnlyAt htr hP hf) hP hf σ hσ

/-- **N9a, any constant field.** `K̄` is generated over an algebraic closure `k̄ ⊇ k` by `K`
(the function field of the geometric curve); a `k̄`-automorphism of `K̄` fixing no degree-one
place (a translation) rules out a function with polar divisor exactly `1·P` on `K`. -/
theorem not_hasSimplePoleOnlyAt_of_baseChange {kb Kb : Type*} [Field kb] [Field Kb]
    [IsAlgClosed kb] [Algebra k kb] [Algebra.IsAlgebraic k kb] [Algebra kb Kb] [Algebra K Kb]
    [Algebra k Kb] [IsScalarTower k kb Kb] [IsScalarTower k K Kb]
    (hgen : IntermediateField.adjoin kb (Set.range (algebraMap K Kb)) = ⊤)
    (htr : TrdegLeOne k K) (hP : IsDegreeOnePlace k P) (σ : Kb ≃ₐ[kb] Kb)
    (hσ : ∀ Q : ValuationSubring Kb, IsDegreeOnePlace kb Q → Q.comap (σ : Kb →+* Kb) ≠ Q)
    (f : K) : ¬ HasSimplePoleOnlyAt k P f := by
  intro hf
  have htop := adjoin_eq_top_of_hasSimplePoleOnlyAt htr hP hf
  have hft := transcendental_of_hasSimplePoleOnlyAt hP.1 hf
  set f' := algebraMap K Kb f
  have hft' : Transcendental kb f' := by
    intro halg
    have h1 : IsAlgebraic k f' := halg.restrictScalars k
    exact hft ((isAlgebraic_algHom_iff (IsScalarTower.toAlgHom k K Kb)
      (algebraMap K Kb).injective).1 h1)
  have htop' : IntermediateField.adjoin kb {f'} = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ IntermediateField.adjoin k {f} := htop ▸ IntermediateField.mem_top
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k x).1 hx
    have hmem : ∀ t : k[X], algebraMap K Kb (aeval f t) ∈ IntermediateField.adjoin kb {f'} := by
      intro t
      rw [← aeval_algebraMap_apply]
      have h1 : Algebra.adjoin k {f'} ≤
          ((IntermediateField.adjoin kb {f'}).restrictScalars k).toSubalgebra :=
        Algebra.adjoin_le (Set.singleton_subset_iff.2
          (IntermediateField.mem_adjoin_simple_self kb f'))
      exact h1 (aeval_mem_adjoin_singleton k f')
    rw [map_div₀]
    exact div_mem (hmem r) (hmem s)
  set u := f'⁻¹
  have hft'' : Transcendental kb u := fun h => hft' (IsAlgebraic.inv_iff.1 h)
  have htopu : IntermediateField.adjoin kb {u} = ⊤ := by
    rw [eq_top_iff, ← htop', IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    have : f' = u⁻¹ := (inv_inv f').symm
    rw [SetLike.mem_coe, this]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self kb u)
  set P' := GroupCurveNotP1.ratPlace hft'' htopu 0
  have hu : u ∈ P'.nonunits := by
    have := sub_mem_nonunits_ratPlace (hft := hft'') (htop := htopu) (0 : kb)
    simpa using this
  have hf'0 : f' ≠ 0 := fun h => hft' (by rw [h]; exact isAlgebraic_zero)
  have hu0 : u ≠ 0 := inv_ne_zero hf'0
  have huf : u * f' = 1 := inv_mul_cancel₀ hf'0
  have hf' : HasSimplePoleOnlyAt kb P' f' := by
    refine ⟨?_, fun x hx => ?_, fun O hO hne => ?_⟩
    · have := inv_not_mem_of_mem_nonunits hu hu0
      rwa [inv_inv] at this
    · obtain ⟨y, hy, rfl⟩ := eq_mul_of_mem_nonunits hx
      have : (u - algebraMap kb Kb 0) * y * f' = y := by
        rw [map_zero, sub_zero, mul_comm u y, mul_assoc, huf, mul_one]
      rw [this]; exact hy
    · by_contra hfO
      have huO : u ∈ O := (O.mem_or_inv_mem f').resolve_left hfO
      have hun : u - algebraMap kb Kb 0 ∈ O.nonunits := by
        rw [map_zero, sub_zero]
        exact mem_nonunits_of_inv_not_mem huO (by rwa [inv_inv])
      exact hne (ratPlace_eq hO hun).symm
  exact false_of_hasSimplePoleOnlyAt htop' (isDegreeOnePlace_ratPlace 0) hf' σ hσ

/-- `L(1·P) = k`: a function regular away from `P` with at most a simple pole there is constant
(algebraically closed constants). -/
theorem eq_algebraMap_of_mul_uniformizer_mem [IsAlgClosed k] (htr : TrdegLeOne k K)
    (hP : IsDegreeOnePlace k P) (σ : K ≃ₐ[k] K)
    (hσ : ∀ Q : ValuationSubring K, IsDegreeOnePlace k Q → Q.comap (σ : K →+* K) ≠ Q)
    {π : K} (hπ : IsUniformizerAt P π) {h : K}
    (hh : ∀ O : ValuationSubring K, IsConstPlace k O → O ≠ P → h ∈ O) (hhP : h * π ∈ P) :
    ∃ c : k, h = algebraMap k K c := by
  by_cases hmem : h ∈ P
  · exact eq_algebraMap_of_forall_mem hP fun O hO => by
      by_cases hOP : O = P
      · exact hOP ▸ hmem
      · exact hh O hO hOP
  · refine (not_hasSimplePoleOnlyAt htr hP σ hσ h ⟨hmem, fun x hx => ?_, hh⟩).elim
    have : x * h = x * π⁻¹ * (h * π) := by field_simp [hπ.1]
    rw [this]; exact mul_mem (hπ.2.2 x hx) hhP

/-- `L(1·P) = k` over any constant field (base-change form). -/
theorem eq_algebraMap_of_mul_uniformizer_mem_of_baseChange {kb Kb : Type*} [Field kb]
    [Field Kb] [IsAlgClosed kb] [Algebra k kb] [Algebra.IsAlgebraic k kb] [Algebra kb Kb]
    [Algebra K Kb] [Algebra k Kb] [IsScalarTower k kb Kb] [IsScalarTower k K Kb]
    (hgen : IntermediateField.adjoin kb (Set.range (algebraMap K Kb)) = ⊤)
    (htr : TrdegLeOne k K) (hP : IsDegreeOnePlace k P) (σ : Kb ≃ₐ[kb] Kb)
    (hσ : ∀ Q : ValuationSubring Kb, IsDegreeOnePlace kb Q → Q.comap (σ : Kb →+* Kb) ≠ Q)
    {π : K} (hπ : IsUniformizerAt P π) {h : K}
    (hh : ∀ O : ValuationSubring K, IsConstPlace k O → O ≠ P → h ∈ O) (hhP : h * π ∈ P) :
    ∃ c : k, h = algebraMap k K c := by
  by_cases hmem : h ∈ P
  · exact eq_algebraMap_of_forall_mem hP fun O hO => by
      by_cases hOP : O = P
      · exact hOP ▸ hmem
      · exact hh O hO hOP
  · refine (not_hasSimplePoleOnlyAt_of_baseChange hgen htr hP σ hσ h
      ⟨hmem, fun x hx => ?_, hh⟩).elim
    have : x * h = x * π⁻¹ * (h * π) := by field_simp [hπ.1]
    rw [this]; exact mul_mem (hπ.2.2 x hx) hhP

end ZInQ.Contrib.CMHeight62Full
