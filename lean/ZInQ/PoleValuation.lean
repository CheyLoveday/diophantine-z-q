module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Int.Parity

/-!
# Valuation obstruction for the rational pole witness system

For the explicit rational pole witness system `poleSystem B v` (six Boolean coordinates,
the multiplier `m = (1-2b₀)(1+b₁)(1+2b₂)(1+4b₃)(1+6b₄)(1+12b₅)`, `A = m B`,
`H = A (A - B²)`, the inverse equation `e H z w = 1`, and the two curve equations
`r₁² = A (A - e) (A + 3e)` and `r₂² = A (A z² - e H) (A z² + 3 e H)`), we show that for every
prime `p ∤ 2730 = 2·3·5·7·13` the input `B ≠ 0` cannot have a negative odd `p`-adic valuation.

Everything is phrased with Mathlib's actual `padicValRat`, whose value at `0` is `0` (not `∞`).
Every use of the product or ultrametric sum rule is guarded by an explicitly derived
nonvanishing fact; the nonvanishing of `e`, `z` and `H` comes from the inverse equation and
from the valuation computation itself. Zero ordinates `r₁`, `r₂` are allowed.

## Main results

* `poleMultiplier_nonzero_and_valuation_zero`: the Boolean multiplier is a nonzero `p`-adic
  unit for `p ∤ 2730`.
* `negative_input_pole_h_valuation`: for a unit `m` and `v_p(B) < 0`,
  `v_p(mB (mB - B²)) = 3 v_p(B)` (with the factors nonzero).
* `curve_rhs_nonzero_and_valuation`: the unnormalized square-scaling fact: if
  `v_p(x) ≠ v_p(l)` and `p ≠ 3`, then `x (x - l) (x + 3l) ≠ 0` and its valuation is
  `v_p(x) + 2 min (v_p(x), v_p(l))`.
* `elliptic_x_valuation_even_of_parameter_even`: on `y² = x (x - l) (x + 3l)` with `x, l ≠ 0`
  and `v_p(l)` even, `v_p(x)` is even.
* `poleSystem_no_negative_odd_valuation`: the main obstruction.
-/

public section

namespace ZInQ.ValuationObstruction

structure PoleWitness where
  bit : Fin 6 → Rat
  e : Rat
  z : Rat
  r1 : Rat
  r2 : Rat
  w : Rat

@[expose] def poleMultiplier (b : Fin 6 → Rat) : Rat :=
  (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) *
    (1 + 4 * b 3) * (1 + 6 * b 4) * (1 + 12 * b 5)

@[expose] def poleA (B : Rat) (v : PoleWitness) : Rat :=
  poleMultiplier v.bit * B

@[expose] def poleH (B : Rat) (v : PoleWitness) : Rat :=
  poleA B v * (poleA B v - B ^ 2)

@[expose] def poleSystem (B : Rat) (v : PoleWitness) : Prop :=
  (∀ i : Fin 6, (v.bit i) ^ 2 - v.bit i = 0) ∧
  v.e * poleH B v * v.z * v.w = 1 ∧
  v.r1 ^ 2 = poleA B v * (poleA B v - v.e) * (poleA B v + 3 * v.e) ∧
  v.r2 ^ 2 = poleA B v *
    (poleA B v * v.z ^ 2 - v.e * poleH B v) *
    (poleA B v * v.z ^ 2 + 3 * v.e * poleH B v)

/-! ### Boolean coordinates and the multiplier -/

/-- A rational solution of `x ^ 2 - x = 0` is `0` or `1`. -/
theorem bit_eq_zero_or_one (x : ℚ) (h : x ^ 2 - x = 0) : x = 0 ∨ x = 1 := by
  have hfac : x * (x - 1) = 0 := by
    have e : x * (x - 1) = x ^ 2 - x := by ring
    exact e.trans h
  rcases mul_eq_zero.mp hfac with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- A rational equal to a nonzero natural divisor of `2730` is a nonzero `p`-adic unit
whenever `p ∤ 2730`. -/
theorem unit_of_eq_natCast_dvd (p : ℕ) (hpout : ¬ p ∣ 2730)
    (q : ℚ) (N : ℕ) (hN : N ∣ 2730) (hN0 : N ≠ 0) (hq : q = (N : ℚ)) :
    q ≠ 0 ∧ padicValRat p q = 0 := by
  subst hq
  refine ⟨by exact_mod_cast hN0, ?_⟩
  have hnd : ¬ p ∣ N := fun h => hpout (dvd_trans h hN)
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd, Nat.cast_zero]

/-- The factor `1 - 2 x` of the multiplier is a nonzero `p`-adic unit for Boolean `x`
(it equals `1` or `-1`). -/
theorem factor0_unit (p : ℕ) (x : ℚ) (hx : x = 0 ∨ x = 1) :
    (1 - 2 * x) ≠ 0 ∧ padicValRat p (1 - 2 * x) = 0 := by
  rcases hx with rfl | rfl
  · norm_num
  · norm_num

/-- A factor `q` of the multiplier which equals `1` when the Boolean `x` is `0`, and equals a
nonzero natural divisor `N` of `2730` when `x` is `1`, is a nonzero `p`-adic unit for
`p ∤ 2730`. -/
theorem factor_unit (p : ℕ) (hpout : ¬ p ∣ 2730) (q x : ℚ)
    (hx : x = 0 ∨ x = 1) (N : ℕ) (hN : N ∣ 2730) (hN0 : N ≠ 0)
    (h0 : x = 0 → q = 1) (h1 : x = 1 → q = (N : ℚ)) :
    q ≠ 0 ∧ padicValRat p q = 0 := by
  rcases hx with hx | hx
  · rw [h0 hx]
    exact ⟨one_ne_zero, padicValRat.one⟩
  · exact unit_of_eq_natCast_dvd p hpout q N hN hN0 (h1 hx)

/-- The product of two nonzero `p`-adic units is a nonzero `p`-adic unit. -/
theorem unit_mul (p : ℕ) [Fact p.Prime] {q r : ℚ} (hq : q ≠ 0 ∧ padicValRat p q = 0)
    (hr : r ≠ 0 ∧ padicValRat p r = 0) : q * r ≠ 0 ∧ padicValRat p (q * r) = 0 :=
  ⟨mul_ne_zero hq.1 hr.1, by rw [padicValRat.mul hq.1 hr.1, hq.2, hr.2, add_zero]⟩

theorem poleMultiplier_nonzero_and_valuation_zero
    (p : Nat) (hp : p.Prime) (hpout : ¬ p ∣ 2730)
    (b : Fin 6 → Rat)
    (hbits : ∀ i : Fin 6, (b i) ^ 2 - b i = 0) :
    poleMultiplier b ≠ 0 ∧ padicValRat p (poleMultiplier b) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have f0 : (1 - 2 * b 0) ≠ 0 ∧ padicValRat p (1 - 2 * b 0) = 0 :=
    factor0_unit p (b 0) (bit_eq_zero_or_one _ (hbits 0))
  have f1 : (1 + b 1) ≠ 0 ∧ padicValRat p (1 + b 1) = 0 :=
    factor_unit p hpout (1 + b 1) (b 1) (bit_eq_zero_or_one _ (hbits 1)) 2 (by decide)
      (by decide) (fun h => by norm_num [h]) (fun h => by norm_num [h])
  have f2 : (1 + 2 * b 2) ≠ 0 ∧ padicValRat p (1 + 2 * b 2) = 0 :=
    factor_unit p hpout (1 + 2 * b 2) (b 2) (bit_eq_zero_or_one _ (hbits 2)) 3 (by decide)
      (by decide) (fun h => by norm_num [h]) (fun h => by norm_num [h])
  have f3 : (1 + 4 * b 3) ≠ 0 ∧ padicValRat p (1 + 4 * b 3) = 0 :=
    factor_unit p hpout (1 + 4 * b 3) (b 3) (bit_eq_zero_or_one _ (hbits 3)) 5 (by decide)
      (by decide) (fun h => by norm_num [h]) (fun h => by norm_num [h])
  have f4 : (1 + 6 * b 4) ≠ 0 ∧ padicValRat p (1 + 6 * b 4) = 0 :=
    factor_unit p hpout (1 + 6 * b 4) (b 4) (bit_eq_zero_or_one _ (hbits 4)) 7 (by decide)
      (by decide) (fun h => by norm_num [h]) (fun h => by norm_num [h])
  have f5 : (1 + 12 * b 5) ≠ 0 ∧ padicValRat p (1 + 12 * b 5) = 0 :=
    factor_unit p hpout (1 + 12 * b 5) (b 5) (bit_eq_zero_or_one _ (hbits 5)) 13 (by decide)
      (by decide) (fun h => by norm_num [h]) (fun h => by norm_num [h])
  have hprod := unit_mul p (unit_mul p (unit_mul p (unit_mul p (unit_mul p f0 f1) f2) f3) f4) f5
  unfold poleMultiplier
  exact hprod

/-! ### The valuation of `H` -/

theorem negative_input_pole_h_valuation
    (p : Nat) (hp : p.Prime) (m B : Rat)
    (hm : m ≠ 0) (hB : B ≠ 0)
    (hm_unit : padicValRat p m = 0) (hneg : padicValRat p B < 0) :
    m * B ≠ 0 ∧
    (m * B) * (m * B - B ^ 2) ≠ 0 ∧
    padicValRat p ((m * B) * (m * B - B ^ 2)) =
      3 * padicValRat p B := by
  have : Fact p.Prime := ⟨hp⟩
  have hmB : m * B ≠ 0 := mul_ne_zero hm hB
  have hmB_val : padicValRat p (m * B) = padicValRat p B := by
    rw [padicValRat.mul hm hB, hm_unit, zero_add]
  have hnegB : -B ≠ 0 := neg_ne_zero.mpr hB
  have hlt : padicValRat p (-B) < padicValRat p m := by
    rw [padicValRat.neg, hm_unit]
    exact hneg
  -- `m ≠ B` because their valuations differ, so `m - B ≠ 0`.
  have hmsub : m - B ≠ 0 := by
    intro h
    have hmB' : m = B := sub_eq_zero.mp h
    rw [hmB'] at hm_unit
    omega
  have hmsub_val : padicValRat p (m - B) = padicValRat p B := by
    have hre : m - B = -B + m := by ring
    have hsum : -B + m ≠ 0 := by
      rw [← hre]
      exact hmsub
    rw [hre, padicValRat.add_eq_of_lt (p := p) hsum hnegB hm hlt, padicValRat.neg]
  have hfac : m * B - B ^ 2 = B * (m - B) := by ring
  have hsec : m * B - B ^ 2 ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero hB hmsub
  have hsec_val : padicValRat p (m * B - B ^ 2) = 2 * padicValRat p B := by
    rw [hfac, padicValRat.mul hB hmsub, hmsub_val]
    ring
  refine ⟨hmB, mul_ne_zero hmB hsec, ?_⟩
  rw [padicValRat.mul hmB hsec, hmB_val, hsec_val]
  ring

/-! ### The square-scaling argument on `y² = x (x - l) (x + 3l)` -/

/-- `v_p(3) = 0` for a prime `p ≠ 3`. -/
theorem padicValRat_three_eq_zero (p : ℕ) [hp : Fact p.Prime] (hp3 : p ≠ 3) :
    padicValRat p (3 : ℚ) = 0 := by
  have hnd : ¬ p ∣ 3 := by
    intro hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp hd)
  have h := padicValRat.of_nat (p := p) (n := 3)
  rw [padicValNat.eq_zero_of_not_dvd hnd] at h
  exact_mod_cast h

/-- The unnormalized square-scaling fact: if `x, l ≠ 0` have different `p`-adic valuations and
`p ≠ 3`, then `x (x - l) (x + 3l) ≠ 0` and its valuation is `v(x) + 2 min (v(x), v(l))`. -/
theorem curve_rhs_nonzero_and_valuation (p : ℕ) [hp : Fact p.Prime] (hp3 : p ≠ 3)
    (x l : ℚ) (hx : x ≠ 0) (hl : l ≠ 0)
    (hne : padicValRat p x ≠ padicValRat p l) :
    x * (x - l) * (x + 3 * l) ≠ 0 ∧
      padicValRat p (x * (x - l) * (x + 3 * l)) =
        padicValRat p x + 2 * min (padicValRat p x) (padicValRat p l) := by
  -- the factor `x - l`
  have hnl : -l ≠ 0 := neg_ne_zero.mpr hl
  have hvnl : padicValRat p (-l) = padicValRat p l := padicValRat.neg l
  have hsub0 : x - l ≠ 0 := by
    intro h
    exact hne (by rw [sub_eq_zero.mp h])
  have hsum0 : x + -l ≠ 0 := by
    rw [← sub_eq_add_neg]
    exact hsub0
  have hne' : padicValRat p x ≠ padicValRat p (-l) := by
    rw [hvnl]
    exact hne
  have hsub : padicValRat p (x - l) = min (padicValRat p x) (padicValRat p l) := by
    rw [sub_eq_add_neg, padicValRat.add_eq_min (p := p) hsum0 hx hnl hne', hvnl]
  -- the factor `x + 3 * l`
  have h30 : (3 : ℚ) ≠ 0 := by norm_num
  have h3l0 : 3 * l ≠ 0 := mul_ne_zero h30 hl
  have hv3l : padicValRat p (3 * l) = padicValRat p l := by
    rw [padicValRat.mul h30 hl, padicValRat_three_eq_zero p hp3, zero_add]
  have hadd0 : x + 3 * l ≠ 0 := by
    intro h
    have hx' : x = -(3 * l) := eq_neg_iff_add_eq_zero.mpr h
    apply hne
    rw [hx', padicValRat.neg, hv3l]
  have hne3 : padicValRat p x ≠ padicValRat p (3 * l) := by
    rw [hv3l]
    exact hne
  have hadd : padicValRat p (x + 3 * l) = min (padicValRat p x) (padicValRat p l) := by
    rw [padicValRat.add_eq_min (p := p) hadd0 hx h3l0 hne3, hv3l]
  have hxs0 : x * (x - l) ≠ 0 := mul_ne_zero hx hsub0
  refine ⟨mul_ne_zero hxs0 hadd0, ?_⟩
  rw [padicValRat.mul hxs0 hadd0, padicValRat.mul hx hsub0, hsub, hadd]
  ring

theorem elliptic_x_valuation_even_of_parameter_even
    (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (x l y : Rat) (hx : x ≠ 0) (hl : l ≠ 0)
    (hl_even : Even (padicValRat p l))
    (hcurve : y ^ 2 = x * (x - l) * (x + 3 * l)) :
    Even (padicValRat p x) := by
  -- The hypothesis `p ≠ 2` belongs to the fixed target signature, but the argument below
  -- only needs `p ≠ 3` (so that `v_p(3 l) = v_p(l)`); it is discarded explicitly.
  clear hp2
  have : Fact p.Prime := ⟨hp⟩
  by_cases heq : padicValRat p x = padicValRat p l
  · -- equal valuations: parity is immediate
    rw [heq]
    exact hl_even
  · -- different valuations: `v(y²) = v(x) + 2 min (v(x), v(l))`
    obtain ⟨hne0, hval⟩ := curve_rhs_nonzero_and_valuation p hp3 x l hx hl heq
    have hy : y ≠ 0 := by
      intro h
      have h2 : y ^ 2 = 0 := by simp [h]
      exact hne0 (hcurve.symm.trans h2)
    have hy2 : padicValRat p (y ^ 2) = 2 * padicValRat p y := by
      have h := padicValRat.pow (p := p) y (k := 2)
      exact_mod_cast h
    rw [← hcurve, hy2] at hval
    generalize min (padicValRat p x) (padicValRat p l) = c at hval
    exact ⟨padicValRat p y - c, by omega⟩

/-! ### The main obstruction -/

theorem poleSystem_no_negative_odd_valuation
    (B : Rat) (v : PoleWitness) (hB : B ≠ 0)
    (hsystem : poleSystem B v)
    (p : Nat) (hp : p.Prime) (hpout : ¬ p ∣ 2730) :
    ¬ (padicValRat p B < 0 ∧ Odd (padicValRat p B)) := by
  rintro ⟨hneg, hodd⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hbits, hinv, hc1, hc2⟩ := hsystem
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpout
    exact hpout (by decide)
  have hp3 : p ≠ 3 := by
    intro h
    rw [h] at hpout
    exact hpout (by decide)
  -- the multiplier is a nonzero unit
  obtain ⟨hm0, hmv⟩ :=
    poleMultiplier_nonzero_and_valuation_zero p hp hpout v.bit hbits
  -- `A ≠ 0`, `H ≠ 0` and `v(H) = 3 v(B)`
  obtain ⟨hA0, hH0, hHv⟩ :=
    negative_input_pole_h_valuation p hp (poleMultiplier v.bit) B hm0 hB hmv hneg
  have hA0' : poleA B v ≠ 0 := hA0
  have hH0' : poleH B v ≠ 0 := hH0
  have hHv' : padicValRat p (poleH B v) = 3 * padicValRat p B := hHv
  have hAv : padicValRat p (poleA B v) = padicValRat p B := by
    show padicValRat p (poleMultiplier v.bit * B) = padicValRat p B
    rw [padicValRat.mul hm0 hB, hmv, zero_add]
  -- nonvanishing of `e` and `z` from the inverse equation `e H z w = 1`
  have he0 : v.e ≠ 0 := by
    intro h
    rw [h] at hinv
    simp at hinv
  have hz0 : v.z ≠ 0 := by
    intro h
    rw [h] at hinv
    simp at hinv
  obtain ⟨kb, hkb⟩ := hodd
  rcases Int.even_or_odd (padicValRat p v.e) with he | he
  · -- `v(e)` even: the first point `(A, r1)` forces `v(A) = v(B)` even
    have hAeven := elliptic_x_valuation_even_of_parameter_even p hp hp2 hp3
      (poleA B v) v.e v.r1 hA0' he0 he hc1
    rw [hAv] at hAeven
    obtain ⟨r, hr⟩ := hAeven
    omega
  · -- `v(e)` odd: then `v(e H) = v(e) + 3 v(B)` is even, and the second point
    -- `(A z², z r2)` forces `v(A z²) = v(B) + 2 v(z)` even
    have hl0 : v.e * poleH B v ≠ 0 := mul_ne_zero he0 hH0'
    have hleven : Even (padicValRat p (v.e * poleH B v)) := by
      rw [padicValRat.mul he0 hH0', hHv']
      obtain ⟨ke, hke⟩ := he
      exact ⟨ke + 3 * kb + 2, by omega⟩
    have hz2ne : v.z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
    have hx0 : poleA B v * v.z ^ 2 ≠ 0 := mul_ne_zero hA0' hz2ne
    have hcurve2 : (v.z * v.r2) ^ 2 = (poleA B v * v.z ^ 2) *
        ((poleA B v * v.z ^ 2) - v.e * poleH B v) *
        ((poleA B v * v.z ^ 2) + 3 * (v.e * poleH B v)) := by
      rw [mul_pow, hc2]
      ring
    have hxeven := elliptic_x_valuation_even_of_parameter_even p hp hp2 hp3
      (poleA B v * v.z ^ 2) (v.e * poleH B v) (v.z * v.r2) hx0 hl0 hleven hcurve2
    have hz2 : padicValRat p (v.z ^ 2) = 2 * padicValRat p v.z := by
      have h := padicValRat.pow (p := p) v.z (k := 2)
      exact_mod_cast h
    rw [padicValRat.mul hA0' hz2ne, hAv, hz2] at hxeven
    obtain ⟨r, hr⟩ := hxeven
    omega

end ZInQ.ValuationObstruction
