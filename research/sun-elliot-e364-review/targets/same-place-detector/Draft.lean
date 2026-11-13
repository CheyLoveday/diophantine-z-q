import Mathlib

/-!
# Completed `G = 1` proof of `samePlaceDetector`

**Proposed owner:** Local-arithmetic workstream; next agent.

**Status:** complete algebraic proof for the single-group interface. All three
declarations have no `sorryAx` and use only the ordinary foundational axioms.
This module is outside the seven production modules and its fresh audit result.

The earlier draft warnings are retained in dated receipts as historical work;
they are not present in the current file.

This first slice covers one witness group (`G = 1` in Sun's Lemma 3.1). It does
not yet state the full finite-family disjunction with a sum of group inverses.

The design keeps three obligations separate:

1. factor valuations from the odd scalar valuation and unequal parities;
2. the product bound when every place has a failed test;
3. conversion of the global pole/trace obstruction into one common place.

`DetectorKit` is an adapter for a fixed unramified rational prime. Its fields are
not permission to rename or discard actual source objects: a completed adapter
must identify Sun's genuine places, normalized valuations and trace.
-/

namespace SunElliotE364.Targets

open scoped BigOperators

/-- The value group used by the local detector, with `⊤` for zero. -/
abbrev PlaceValue := WithTop ℤ


lemma place_two_nsmul (a : PlaceValue) : (2 : ℕ) • a = ((2 : ℤ) : PlaceValue) * a := by
  induction a using WithTop.recTopCoe with
  | top =>
      rw [two_nsmul, WithTop.mul_top (show ((2 : ℤ) : PlaceValue) ≠ 0 by norm_num),
        WithTop.add_top]
  | coe a =>
      rw [← WithTop.coe_nsmul, ← WithTop.coe_mul]
      exact WithTop.coe_inj.mpr (nsmul_eq_mul 2 a)

lemma place_nat_smul_coe (k : ℕ) (a : ℤ) :
    k • (a : PlaceValue) = ((k : ℤ) : PlaceValue) * a := by
  rw [← WithTop.coe_nsmul, ← WithTop.coe_mul]
  exact WithTop.coe_inj.mpr (nsmul_eq_mul k a)

/-- Source-side data at one unramified rational prime. -/
structure DetectorKit (F : Type*) [Field F] [Algebra ℚ F] where
  p : ℕ
  p_prime : p.Prime
  Place : Type*
  val : Place → AddValuation F PlaceValue
  trace : F →ₗ[ℚ] ℚ
  /-- Normalized valuations agree with the rational `p`-adic valuation.
  The split at zero is essential: `AddValuation 0 = ⊤`, while
  `padicValRat p 0 = 0`. -/
  val_algebraMap : ∀ (P : Place) (q : ℚ),
    val P (algebraMap ℚ F q) = if q = 0 then ⊤ else (padicValRat p q : PlaceValue)
  /-- The unramified compatibility used to take integrality through trace. -/
  trace_lower_bound : ∀ (x : F) (a : ℤ),
    (∀ P : Place, (a : PlaceValue) ≤ val P x) →
      (a : PlaceValue) ≤ (padicValRat p (trace x) : PlaceValue)

variable {F I : Type*} [Field F] [Algebra ℚ F] [Fintype I]

/-- The rational scalar in the detector field. -/
def scalar (R : ℚ) : F := algebraMap ℚ F R

/-- One nonconstant detector quotient. -/
def detectorQuotient (R : ℚ) (D : I → F) (k : I → ℕ) (i : I) : F :=
  D i / (scalar R : F) ^ k i

/-- One detector factor. -/
def detectorFactor (R : ℚ) (D : I → F) (k : I → ℕ) (i : I) : F :=
  1 + scalar R * (detectorQuotient R D k i) ^ 2

/-- Product before inversion and trace; this ordering must not be changed. -/
def detectorW (R : ℚ) (D : I → F) (k : I → ℕ) : F :=
  ∏ i, detectorFactor R D k i

/-- Mapping a finite product to a sum of additive valuations, by induction on
the finite carrier. -/
lemma addValuation_prod {v : AddValuation F PlaceValue} (s : Finset I) (f : I → F) :
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, v.map_mul, ih, Finset.sum_insert ha]

/-- The rational trace of the inverse product. -/
def detectorTheta (kit : DetectorKit F) (R : ℚ) (D : I → F) (k : I → ℕ) : ℚ :=
  kit.trace (detectorW R D k)⁻¹

/-- The input to the inherited one-sided pole predicate. -/
def detectorB (kit : DetectorKit F) (R : ℚ) (D : I → F) (k : I → ℕ) : ℚ :=
  R / detectorTheta kit R D k ^ 2

/-- The nonconstant factor valuation before taking its minimum with zero. -/
def localTermValue (kit : DetectorKit F) (R : ℚ) (D : I → F) (k : I → ℕ)
    (P : kit.Place) (i : I) : PlaceValue :=
  (padicValRat kit.p R : PlaceValue) +
    2 • (kit.val P (D i) - (k i) • (padicValRat kit.p R : PlaceValue))

/-- First concrete helper target, proved below. The odd scalar premise is
essential: without it `R = -1`, `k = 0`, `D = 1` produces a zero factor and
`⊤` on the left but `0` on the right. -/
theorem detectorFactor_valuation (kit : DetectorKit F) [Nonempty kit.Place]
    (R : ℚ) (D : I → F) (k : I → ℕ) (hα : Odd (padicValRat kit.p R))
    (P : kit.Place) (i : I) :
    kit.val P (detectorFactor R D k i) = min 0 (localTermValue kit R D k P i) := by
  have hR : R ≠ 0 := by
    intro hzero
    simp [hzero] at hα
  by_cases hD : D i = 0
  · have hb2 : (2 : ℕ) • (⊤ : PlaceValue) = ⊤ := by
      rw [two_nsmul]
      simp
    have hb : localTermValue kit R D k P i = ⊤ := by
      simp [localTermValue, hD, hb2]
    rw [hb]
    simp [detectorFactor, detectorQuotient, hD]
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp ((kit.val P).ne_top_iff.mpr hD)
    have hq : kit.val P (detectorQuotient R D k i) =
        kit.val P (D i) - (k i) • (padicValRat kit.p R : PlaceValue) := by
      unfold detectorQuotient
      rw [(kit.val P).map_div, (kit.val P).map_pow, scalar, kit.val_algebraMap, if_neg hR]
    have ht : kit.val P (scalar R * (detectorQuotient R D k i) ^ 2) =
        localTermValue kit R D k P i := by
      rw [(kit.val P).map_mul, (kit.val P).map_pow, hq, scalar, kit.val_algebraMap, if_neg hR]
      dsimp [localTermValue]
    have hbcast : localTermValue kit R D k P i =
        ((padicValRat kit.p R + 2 * (d - (k i : ℤ) * padicValRat kit.p R) : ℤ) : PlaceValue) := by
      unfold localTermValue
      rw [← hd, place_nat_smul_coe, place_two_nsmul]
      norm_cast
    have hbodd : Odd (padicValRat kit.p R + 2 * (d - (k i : ℤ) * padicValRat kit.p R)) := by
      obtain ⟨a, ha⟩ := hα
      exact ⟨a + (d - (k i : ℤ) * padicValRat kit.p R), by omega⟩
    have hbne : localTermValue kit R D k P i ≠ 0 := by
      rw [hbcast]
      have hbzero : padicValRat kit.p R + 2 * (d - (k i : ℤ) * padicValRat kit.p R) ≠ 0 := by
        obtain ⟨a, ha⟩ := hbodd
        omega
      exact WithTop.coe_ne_zero.mpr hbzero
    unfold detectorFactor
    rw [(kit.val P).map_add_of_distinct_val]
    · rw [(kit.val P).map_one, ht]
    · rw [(kit.val P).map_one, ht]
      exact Ne.symm hbne

/-- Product bound when every place contains some failed test. Other factors
cannot repair it: every factor has nonpositive valuation. -/
theorem failedEverywhere_product_bound (kit : DetectorKit F) [Nonempty kit.Place]
    (R : ℚ) (D : I → F) (k : I → ℕ) (hk : ∀ i, 1 ≤ k i)
    (hfactor : ∀ (P : kit.Place) (i : I),
      kit.val P (detectorFactor R D k i) = min 0 (localTermValue kit R D k P i))
    (hα : Odd (padicValRat kit.p R))
    (hfail : ∀ P : kit.Place, ∃ i, kit.val P (D i) < (k i : PlaceValue)) :
    ∀ P : kit.Place, kit.val P (detectorW R D k) ≤ -(padicValRat kit.p R : PlaceValue) := by
  classical
  have hnonpos : ∀ P : kit.Place, ∀ i, kit.val P (detectorFactor R D k i) ≤ 0 := by
    intro P i
    rw [hfactor P i]
    exact min_le_left _ _
  have hWnonpos : ∀ P : kit.Place, kit.val P (detectorW R D k) ≤ 0 := by
    intro P
    rw [detectorW, addValuation_prod]
    exact Finset.sum_nonpos (fun i _ => hnonpos P i)
  intro P
  by_cases hαpos : 0 < padicValRat kit.p R
  · obtain ⟨i, hi⟩ := hfail P
    have hDltTop : kit.val P (D i) < ⊤ :=
      hi.trans_le (by exact le_top)
    obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hDltTop)
    have hdlt : d < (k i : ℤ) := by
      rw [← hd] at hi
      exact_mod_cast hi
    have hbcast : localTermValue kit R D k P i =
        ((padicValRat kit.p R + 2 * (d - (k i : ℤ) * padicValRat kit.p R) : ℤ) : PlaceValue) := by
      unfold localTermValue
      rw [← hd, place_nat_smul_coe, place_two_nsmul]
      norm_cast
    have hbZ : padicValRat kit.p R + 2 * (d - (k i : ℤ) * padicValRat kit.p R) ≤
        -padicValRat kit.p R := by
      have hk_i : 1 ≤ (k i : ℤ) := by exact_mod_cast hk i
      have hprod_nonneg : 0 ≤ ((k i : ℤ) - 1) * ((padicValRat kit.p R) - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
    have hbi : kit.val P (detectorFactor R D k i) ≤ -(padicValRat kit.p R : PlaceValue) := by
      rw [hfactor P i]
      apply (min_le_right _ _).trans
      rw [hbcast]
      exact_mod_cast hbZ
    rw [detectorW, addValuation_prod, ← Finset.add_sum_erase _ _ (by simp : i ∈ Finset.univ)]
    have hothers : ∑ j ∈ Finset.univ.erase i, kit.val P (detectorFactor R D k j) ≤ 0 :=
      Finset.sum_nonpos (fun j _ => hnonpos P j)
    simpa only [add_zero] using add_le_add hbi hothers
  · by_cases hαzero : padicValRat kit.p R = 0
    · simp [hαzero] at hα
    · have hαneg : padicValRat kit.p R < 0 := by omega
      have hpos0 : (0 : PlaceValue) < -(padicValRat kit.p R : PlaceValue) := by
        norm_cast
        exact neg_pos.mpr hαneg
      apply (hWnonpos P).trans
      exact le_of_lt hpos0

/-- The one-sided pole consequence needed from the inherited predicate. It is
not a new definition of `Φ₀`; it is the exact outside-`S₀` inference used here. -/
def NoNegativeOddPoleValuation (kit : DetectorKit F) (B : ℚ) : Prop :=
  Odd (padicValRat kit.p B) → 0 ≤ padicValRat kit.p B

/-- **Target interface (`G = 1`).** The guards are deliberately retained. A
subsequent adapter must derive the pole rule from Sun's actual `Φ₀`, and the
factor/trace compatibility from the genuine number-field construction.

The final proof must produce both positivity of the odd scalar valuation and a
single place satisfying every precision condition. It must not return separate
places for separate tests. -/
theorem samePlaceDetector (kit : DetectorKit F) [Fintype kit.Place] [Nonempty kit.Place]
    (R : ℚ) (D : I → F) (k : I → ℕ)
    (hR : R ≠ 0) (hk : ∀ i, 1 ≤ k i)
    (hW : detectorW R D k ≠ 0) (hTheta : detectorTheta kit R D k ≠ 0)
    (hpole : NoNegativeOddPoleValuation kit (detectorB kit R D k))
    (hα : Odd (padicValRat kit.p R)) :
    0 < padicValRat kit.p R ∧
      ∃ P : kit.Place, ∀ i, (k i : PlaceValue) ≤ kit.val P (D i) := by
  classical
  letI : Fact kit.p.Prime := ⟨kit.p_prime⟩
  have hfactor : ∀ (Q : kit.Place) (i : I),
      kit.val Q (detectorFactor R D k i) = min 0 (localTermValue kit R D k Q i) := by
    intro Q i
    exact detectorFactor_valuation kit R D k hα Q i
  have hBval : padicValRat kit.p (detectorB kit R D k) =
      padicValRat kit.p R - 2 * padicValRat kit.p (detectorTheta kit R D k) := by
    unfold detectorB
    rw [padicValRat.div hR (pow_ne_zero 2 hTheta), padicValRat.pow]
    norm_num
  have hBodd : Odd (padicValRat kit.p (detectorB kit R D k)) := by
    obtain ⟨a, ha⟩ := hα
    exact ⟨a - padicValRat kit.p (detectorTheta kit R D k), by rw [hBval]; omega⟩
  have hαpos : 0 < padicValRat kit.p R := by
    by_contra hnpos
    have hαne : padicValRat kit.p R ≠ 0 := by
      intro hzero
      simp [hzero] at hα
    have hαneg : padicValRat kit.p R < 0 := by omega
    have hτnon : 0 ≤ padicValRat kit.p (detectorTheta kit R D k) := by
      have hnonpos : (0 : PlaceValue) ≤
          (padicValRat kit.p (detectorTheta kit R D k) : PlaceValue) := by
        unfold detectorTheta
        apply kit.trace_lower_bound (detectorW R D k)⁻¹ 0
        intro Q
        rw [(kit.val Q).map_inv]
        have hq : kit.val Q (detectorW R D k) ≤ 0 := by
          rw [detectorW, addValuation_prod]
          apply Finset.sum_nonpos
          intro i hi
          rw [hfactor Q i]
          exact min_le_left _ _
        obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp
          ((kit.val Q).ne_top_iff.mpr hW)
        rw [← hw] at hq ⊢
        have hwZ : w ≤ 0 := by exact_mod_cast hq
        have hnegative : 0 ≤ -w := by omega
        exact_mod_cast hnegative
      exact_mod_cast hnonpos
    have hvBneg : padicValRat kit.p (detectorB kit R D k) < 0 := by
      rw [hBval]
      omega
    exact (not_lt_of_ge (hpole hBodd)) hvBneg
  have hgood : ¬ ∀ P : kit.Place, ∃ i, kit.val P (D i) < (k i : PlaceValue) := by
    intro hfail
    have hτge : padicValRat kit.p R ≤ padicValRat kit.p (detectorTheta kit R D k) := by
      have hnonneg :
          (padicValRat kit.p R : PlaceValue) ≤
            (padicValRat kit.p (detectorTheta kit R D k) : PlaceValue) := by
        unfold detectorTheta
        apply kit.trace_lower_bound (detectorW R D k)⁻¹ (padicValRat kit.p R)
        intro Q
        rw [(kit.val Q).map_inv]
        have hq : kit.val Q (detectorW R D k) ≤ -(padicValRat kit.p R : PlaceValue) := by
          exact failedEverywhere_product_bound kit R D k hk hfactor hα hfail Q
        obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp
          ((kit.val Q).ne_top_iff.mpr hW)
        rw [← hw] at hq ⊢
        have hwZ : padicValRat kit.p R ≤ -w := by
          have hqZ : w ≤ -padicValRat kit.p R := by exact_mod_cast hq
          omega
        exact_mod_cast hwZ
      exact_mod_cast hnonneg
    have hvBneg : padicValRat kit.p (detectorB kit R D k) < 0 := by
      rw [hBval]
      omega
    exact (not_lt_of_ge (hpole hBodd)) hvBneg
  exact ⟨hαpos, by push_neg at hgood; exact hgood⟩

-- Completed-interface check: all three reports must exclude `sorryAx`.
#print axioms detectorFactor_valuation
#print axioms failedEverywhere_product_bound
#print axioms samePlaceDetector

end SunElliotE364.Targets
