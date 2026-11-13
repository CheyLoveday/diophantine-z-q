import Mathlib

/-!
The marked congruent-curve point attached to an even midpoint. Integer
parameters retain the source arithmetic; rational functions are introduced
only where ordinates, denominators, or valuations require them.
-/

namespace SunElliotE364

open scoped BigOperators

/-- The first doubled ordinate in the attached E364 construction. -/
def doubleX (N s : ℤ) : ℚ :=
  ((N ^ 2 + 1) ^ 2 : ℤ) / (4 * s ^ 2 : ℤ)

/-- The second doubled ordinate in the attached E364 construction. -/
def doubleY (N s : ℤ) : ℚ :=
  ((N ^ 2 + 1) * (N ^ 2 - 2 * N - 1) * (N ^ 2 + 2 * N - 1) : ℤ) /
    (8 * s ^ 3 : ℤ)

/-- The marked point on `y² = x³ - D²x`. -/
def markedX (N : ℤ) (D : ℕ) : ℚ := (D : ℚ) * N

def markedY (D : ℕ) (s : ℤ) : ℚ := (D : ℚ) ^ 2 * s

/-- The tangent slope, with the nonzero parameter `D` already cancelled. -/
def tangentSlope (N s : ℤ) : ℚ := (3 * N ^ 2 - 1 : ℤ) / (2 * s : ℤ)

/-- Duplication using the tangent slope at the marked point. -/
def tangentDoubleX (N : ℤ) (D : ℕ) (s : ℤ) : ℚ :=
  tangentSlope N s ^ 2 - 2 * markedX N D

def tangentDoubleY (N : ℤ) (D : ℕ) (s : ℤ) : ℚ :=
  tangentSlope N s * (markedX N D - tangentDoubleX N D s) - markedY D s

/-- The formal parameter `z = -x/y` of the doubled point. -/
def formalZ (N s : ℤ) : ℚ := -doubleX N s / doubleY N s

/-- The tangent slope before cancellation of `D`. -/
def rawSlope (N : ℤ) (D : ℕ) (s : ℤ) : ℚ :=
  (3 * markedX N D ^ 2 - (D : ℚ) ^ 2) / (2 * markedY D s)

lemma odd_sq_add_one {N : ℤ} (hN : Even N) : Odd (N ^ 2 + 1) := by
  rcases hN with ⟨n, rfl⟩
  exact ⟨2 * n ^ 2, by ring⟩

lemma odd_sq_sub_two_mul_sub_one {N : ℤ} (hN : Even N) :
    Odd (N ^ 2 - 2 * N - 1) := by
  rcases hN with ⟨n, rfl⟩
  exact ⟨2 * n ^ 2 - 2 * n - 1, by ring⟩

lemma odd_sq_add_two_mul_sub_one {N : ℤ} (hN : Even N) :
    Odd (N ^ 2 + 2 * N - 1) := by
  rcases hN with ⟨n, rfl⟩
  exact ⟨2 * n ^ 2 + 2 * n - 1, by ring⟩

lemma odd_ne_zero {A : ℤ} (hA : Odd A) : A ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := hA
  omega

lemma odd_yNumerator {N : ℤ} (hN : Even N) :
    Odd ((N ^ 2 - 2 * N - 1) * (N ^ 2 + 2 * N - 1)) :=
  (odd_sq_sub_two_mul_sub_one hN).mul (odd_sq_add_two_mul_sub_one hN)

/-- A common divisor of an odd integer `A` and `s` is one when a linear
combination of `A` and a multiple `M` of `s` produces four. -/
lemma gcd_eq_one_of_odd_of_four {A M s : ℤ} (hA : Odd A) (hs : s ∣ M)
    (h4 : ∃ x y : ℤ, 4 = A * x + M * y) : Int.gcd A s = 1 := by
  have hgm : A.gcd s ∣ A.gcd M := by
    rw [Int.gcd_eq_natAbs, Int.gcd_eq_natAbs]
    apply Nat.dvd_gcd
    · have h := Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_left A s)
      simpa only [Int.natAbs_natCast, Int.gcd_eq_natAbs] using h
    · have h := Int.natAbs_dvd_natAbs.mpr ((Int.gcd_dvd_right A s).trans hs)
      simpa only [Int.natAbs_natCast, Int.gcd_eq_natAbs] using h
  have hg4 : A.gcd s ∣ 4 := hgm.trans (Int.gcd_dvd_iff.mpr h4)
  have hgA : A.gcd s ∣ A.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_left A s)
    simpa only [Int.natAbs_natCast, Int.gcd_eq_natAbs] using h
  have hgodd : Odd (A.gcd s) := Odd.of_dvd_nat (Int.natAbs_odd.mpr hA) hgA
  have hgle : A.gcd s ≤ 4 := Nat.le_of_dvd (by norm_num) hg4
  interval_cases g : A.gcd s <;> simp_all [Nat.odd_iff]

lemma dvd_consecutive_of_decomposition {N : ℤ} {D : ℕ} {s : ℤ}
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    s ∣ N * (N ^ 2 - 1) := by
  refine ⟨(D : ℤ) * s, ?_⟩
  rw [hdecomp]
  ring

lemma gcd_sq_add_one {N : ℤ} {D : ℕ} {s : ℤ} (hN : Even N)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    Int.gcd (N ^ 2 + 1) s = 1 := by
  apply gcd_eq_one_of_odd_of_four (odd_sq_add_one hN)
    (dvd_consecutive_of_decomposition hdecomp)
  exact ⟨4 - 2 * N ^ 2, 2 * N, by ring⟩

lemma gcd_sq_sub_two_mul_sub_one {N : ℤ} {D : ℕ} {s : ℤ} (hN : Even N)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    Int.gcd (N ^ 2 - 2 * N - 1) s = 1 := by
  apply gcd_eq_one_of_odd_of_four (odd_sq_sub_two_mul_sub_one hN)
    (dvd_consecutive_of_decomposition hdecomp)
  exact ⟨4 * N ^ 2 - 2 * N - 4, -4 * N + 10, by ring⟩

lemma gcd_sq_add_two_mul_sub_one {N : ℤ} {D : ℕ} {s : ℤ} (hN : Even N)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    Int.gcd (N ^ 2 + 2 * N - 1) s = 1 := by
  apply gcd_eq_one_of_odd_of_four (odd_sq_add_two_mul_sub_one hN)
    (dvd_consecutive_of_decomposition hdecomp)
  exact ⟨4 * N ^ 2 + 2 * N - 4, -4 * N - 10, by ring⟩

lemma gcd_yNumerator {N : ℤ} {D : ℕ} {s : ℤ} (hN : Even N)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    Int.gcd ((N ^ 2 - 2 * N - 1) * (N ^ 2 + 2 * N - 1)) s = 1 := by
  rw [Int.gcd_eq_natAbs, Int.natAbs_mul]
  exact Nat.Coprime.mul_left
    (by
      change (N ^ 2 - 2 * N - 1).natAbs.gcd s.natAbs = 1
      rw [← Int.gcd_eq_natAbs]
      exact gcd_sq_sub_two_mul_sub_one hN hdecomp)
    (by
      change (N ^ 2 + 2 * N - 1).natAbs.gcd s.natAbs = 1
      rw [← Int.gcd_eq_natAbs]
      exact gcd_sq_add_two_mul_sub_one hN hdecomp)


lemma odd_full_yNumerator {N : ℤ} (hN : Even N) :
    Odd ((N ^ 2 + 1) * (N ^ 2 - 2 * N - 1) * (N ^ 2 + 2 * N - 1)) :=
  ((odd_sq_add_one hN).mul (odd_sq_sub_two_mul_sub_one hN)).mul
    (odd_sq_add_two_mul_sub_one hN)

lemma gcd_full_yNumerator {N : ℤ} {D : ℕ} {s : ℤ} (hN : Even N)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    Int.gcd ((N ^ 2 + 1) * (N ^ 2 - 2 * N - 1) * (N ^ 2 + 2 * N - 1)) s = 1 := by
  rw [Int.gcd_eq_natAbs, Int.natAbs_mul, Int.natAbs_mul]
  apply Nat.Coprime.mul_left
  · apply Nat.Coprime.mul_left
    · change (N ^ 2 + 1).natAbs.gcd s.natAbs = 1
      rw [← Int.gcd_eq_natAbs]
      exact gcd_sq_add_one hN hdecomp
    · change (N ^ 2 - 2 * N - 1).natAbs.gcd s.natAbs = 1
      rw [← Int.gcd_eq_natAbs]
      exact gcd_sq_sub_two_mul_sub_one hN hdecomp
  · change (N ^ 2 + 2 * N - 1).natAbs.gcd s.natAbs = 1
    rw [← Int.gcd_eq_natAbs]
    exact gcd_sq_add_two_mul_sub_one hN hdecomp

/-- Coprimality of powers in the numerator and denominator of a reduced
fraction, retaining the power of two in the denominator. -/
lemma fractionCoprime {A s : ℤ} (hA : Odd A) (hgcd : Int.gcd A s = 1)
    (m r n : ℕ) : (A ^ m).natAbs.Coprime ((2 ^ r * s ^ n).natAbs) := by
  have hc : A.natAbs.Coprime s.natAbs := by
    change A.natAbs.gcd s.natAbs = 1
    rw [← Int.gcd_eq_natAbs]
    exact hgcd
  have h2 : A.natAbs.Coprime 2 := Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hA)
  have hnat2 : (2 : ℤ).natAbs = 2 := by norm_num
  simpa only [Int.natAbs_mul, Int.natAbs_pow, hnat2] using
    Nat.Coprime.mul_right (h2.pow (m := m) (n := r)) (hc.pow (m := m) (n := n))

/-- The first doubled ordinate is reduced, including its full dyadic factor. -/
theorem doubleX_den {N : ℤ} {D : ℕ} {s : ℤ} (hN : Even N) (hs : 0 < s)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    (doubleX N s).den = (4 * s ^ 2).natAbs := by
  unfold doubleX
  have hpos : 0 < (4 * s ^ 2 : ℤ) := mul_pos (by norm_num) (pow_pos hs 2)
  have h := Rat.den_div_eq_of_coprime hpos
    (fractionCoprime (odd_sq_add_one hN) (gcd_sq_add_one hN hdecomp) 2 2 2)
  exact congrArg Int.natAbs h

/-- The second doubled ordinate is reduced, including its full dyadic factor. -/
theorem doubleY_den {N : ℤ} {D : ℕ} {s : ℤ} (hN : Even N) (hs : 0 < s)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    (doubleY N s).den = (8 * s ^ 3).natAbs := by
  unfold doubleY
  have hpos : 0 < (8 * s ^ 3 : ℤ) := mul_pos (by norm_num) (pow_pos hs 3)
  have hc : (((N ^ 2 + 1) * (N ^ 2 - 2 * N - 1) * (N ^ 2 + 2 * N - 1) : ℤ).natAbs).Coprime
      ((8 * s ^ 3 : ℤ).natAbs) := by
    have h23 : (2 : ℤ) ^ 3 = 8 := by norm_num
    simpa only [pow_one, h23] using
      (fractionCoprime (odd_full_yNumerator hN) (gcd_full_yNumerator hN hdecomp) 1 3 3)
  have h := Rat.den_div_eq_of_coprime hpos hc
  simpa only [Int.natAbs_natCast] using congrArg Int.natAbs h

/-- The common square/cube denominator base is exactly `2s`. -/
theorem denominator_base {N : ℤ} {D : ℕ} {s : ℤ} (hN : Even N) (hs : 0 < s)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    (doubleX N s).den = (2 * s).natAbs ^ 2 ∧
      (doubleY N s).den = (2 * s).natAbs ^ 3 := by
  rw [doubleX_den hN hs hdecomp, doubleY_den hN hs hdecomp]
  have hx : (4 * s ^ 2 : ℤ) = (2 * s) ^ 2 := by ring
  have hy : (8 * s ^ 3 : ℤ) = (2 * s) ^ 3 := by ring
  simp [hx, hy, Int.natAbs_pow]

/-- The marked point lies on the congruent curve, from exactly the source
squareclass decomposition. -/
theorem marked_on_curve {N : ℤ} {D : ℕ} {s : ℤ}
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    markedY D s ^ 2 = markedX N D ^ 3 - (D : ℚ) ^ 2 * markedX N D := by
  have h : (N : ℚ) * ((N : ℚ) ^ 2 - 1) = (D : ℚ) * (s : ℚ) ^ 2 := by
    exact_mod_cast hdecomp
  unfold markedX markedY
  calc
    ((D : ℚ) ^ 2 * (s : ℚ)) ^ 2 = (D : ℚ) ^ 3 * ((D : ℚ) * (s : ℚ) ^ 2) := by ring
    _ = (D : ℚ) ^ 3 * ((N : ℚ) * ((N : ℚ) ^ 2 - 1)) := by rw [← h]
    _ = ((D : ℚ) * (N : ℚ)) ^ 3 - (D : ℚ) ^ 2 * ((D : ℚ) * (N : ℚ)) := by ring

/-- The cancelled and raw tangent slopes agree for positive source
parameters. -/
theorem tangentSlope_eq_rawSlope {N : ℤ} {D : ℕ} {s : ℤ}
    (hD : 0 < D) (hs : 0 < s) : tangentSlope N s = rawSlope N D s := by
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast (Int.ne_of_gt hs)
  unfold tangentSlope rawSlope markedX markedY
  push_cast
  field_simp [hDQ, hsQ]
  <;> ring

/-- Exact doubling formula for the marked point, with no finite-size bound. -/
theorem doubling_formulae {N : ℤ} {D : ℕ} {s : ℤ} (hD : 0 < D) (hs : 0 < s)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    tangentDoubleX N D s = doubleX N s ∧ tangentDoubleY N D s = doubleY N s := by
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast (Int.ne_of_gt hs)
  have h : (D : ℚ) * (s : ℚ) ^ 2 = (N : ℚ) * ((N : ℚ) ^ 2 - 1) := by
    have h' : (N : ℚ) * ((N : ℚ) ^ 2 - 1) = (D : ℚ) * (s : ℚ) ^ 2 := by
      exact_mod_cast hdecomp
    exact h'.symm
  constructor
  · unfold tangentDoubleX doubleX tangentSlope markedX
    push_cast
    field_simp
    linear_combination (-32 * (N : ℚ)) * h
  · unfold tangentDoubleY doubleY tangentDoubleX tangentSlope markedX markedY
    push_cast
    field_simp
    linear_combination
      (32 * (N : ℚ) * (7 * (N : ℚ) ^ 2 - 1) - 64 * (D : ℚ) * (s : ℚ) ^ 2) * h

/-- The square-middle leaf is literally the quartic-Pell-to-congruent-point
bridge. -/
theorem square_middle_bridge {X Y : ℤ} {D : ℕ}
    (h : X ^ 4 - 1 = (D : ℤ) * Y ^ 2) :
    let N := X ^ 2
    let s := X * Y
    N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2 := by
  dsimp
  calc
    X ^ 2 * ((X ^ 2) ^ 2 - 1) = X ^ 2 * ((D : ℤ) * Y ^ 2) := by rw [← h]; ring
    _ = (D : ℤ) * (X * Y) ^ 2 := by ring

/-- Quotient form of `z = -x/y`, retaining both ordinate formulas. -/
theorem formalZ_eq {N : ℤ} {D : ℕ} {s : ℤ} (hN : Even N) (hs : 0 < s)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    formalZ N s = -(2 * s * (N ^ 2 + 1) : ℤ) /
      ((N ^ 2 - 2 * N - 1) * (N ^ 2 + 2 * N - 1) : ℤ) := by
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast (Int.ne_of_gt hs)
  have hA : (N : ℚ) ^ 2 + 1 ≠ 0 := by positivity
  have hB1 : ((N : ℚ) ^ 2 - 2 * N - 1) ≠ 0 := by
    exact_mod_cast odd_ne_zero (odd_sq_sub_two_mul_sub_one hN)
  have hB2 : ((N : ℚ) ^ 2 + 2 * N - 1) ≠ 0 := by
    exact_mod_cast odd_ne_zero (odd_sq_add_two_mul_sub_one hN)
  have hB : ((N : ℚ) ^ 2 - 2 * N - 1) * ((N : ℚ) ^ 2 + 2 * N - 1) ≠ 0 :=
    mul_ne_zero hB1 hB2
  have hY : doubleY N s ≠ 0 := by
    unfold doubleY
    push_cast
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hA hB1) hB2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hsQ))
  unfold formalZ
  push_cast
  rw [div_eq_div_iff hY hB]
  unfold doubleX doubleY
  push_cast
  field_simp [hsQ]
  <;> ring


lemma odd_not_two_dvd {A : ℤ} (hA : Odd A) : ¬(2 : ℤ) ∣ A := by
  intro hd
  exact (Int.not_even_iff_odd.mpr hA) (even_iff_two_dvd.mpr hd)

lemma prime_not_dvd_one {p : ℕ} (hp : p.Prime) : ¬(p : ℤ) ∣ 1 := by
  intro hd
  exact (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_dvd_one hd)

lemma prime_ne_two_not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬(p : ℤ) ∣ 2 := by
  intro hd
  have hdn : p ∣ 2 := by exact_mod_cast hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdn with h | h
  · exact hp.ne_one h
  · exact hp2 h

lemma prime_dvd_consecutive_cases {p : ℕ} (hp : p.Prime) {N : ℤ} {D : ℕ} {s : ℤ}
    (hpD : p ∣ D) (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    (p : ℤ) ∣ N ∨ (p : ℤ) ∣ N - 1 ∨ (p : ℤ) ∣ N + 1 := by
  have hpDZ : (p : ℤ) ∣ (D : ℤ) := by exact_mod_cast hpD
  have hpM : (p : ℤ) ∣ N * (N ^ 2 - 1) := by
    rw [hdecomp]
    exact dvd_mul_of_dvd_left hpDZ _
  have hpM' : (p : ℤ) ∣ N * (N - 1) * (N + 1) := by
    convert hpM using 1 <;> ring
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  rcases hpZ.dvd_mul.mp hpM' with h | h
  · rcases hpZ.dvd_mul.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- At an odd prime dividing the squareclass parameter, the three factors
occurring in the formal-parameter expression are local units. -/
lemma numerator_units_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {N : ℤ} {D : ℕ} {s : ℤ} (hpD : p ∣ D)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    ¬(p : ℤ) ∣ N ^ 2 + 1 ∧
      ¬(p : ℤ) ∣ (N ^ 2 - 2 * N - 1) * (N ^ 2 + 2 * N - 1) := by
  have hcases := prime_dvd_consecutive_cases hp hpD hdecomp
  have hp1 := prime_not_dvd_one hp
  have hp2not := prime_ne_two_not_dvd_two hp hp2
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hA : ¬(p : ℤ) ∣ N ^ 2 + 1 := by
    intro hpA
    rcases hcases with hN | hminus | hplus
    · have hd := dvd_sub hpA (dvd_mul_of_dvd_left hN N)
      apply hp1
      convert hd using 1 <;> ring
    · have hd := dvd_sub hpA (dvd_mul_of_dvd_left hminus (N + 1))
      apply hp2not
      convert hd using 1 <;> ring
    · have hd := dvd_sub hpA (dvd_mul_of_dvd_left hplus (N - 1))
      apply hp2not
      convert hd using 1 <;> ring
  refine ⟨hA, fun hpB => hpZ.not_unit (isUnit_of_dvd_one ?_)⟩
  have hB1 : (p : ℤ) ∣ N ^ 2 - 2 * N - 1 ∨
      (p : ℤ) ∣ N ^ 2 + 2 * N - 1 := by
    exact hpZ.dvd_mul.mp hpB
  have hp1or2 : (p : ℤ) ∣ 1 ∨ (p : ℤ) ∣ 2 := by
    rcases hcases with hN | hminus | hplus
    · rcases hB1 with h | h
      · have hd := dvd_sub h (dvd_mul_of_dvd_left hN (N - 2))
        left
        have hd' : (p : ℤ) ∣ -1 := by convert hd using 1 <;> ring
        simpa using hd'
      · have hd := dvd_sub h (dvd_mul_of_dvd_left hN (N + 2))
        left
        have hd' : (p : ℤ) ∣ -1 := by convert hd using 1 <;> ring
        simpa using hd'
    · rcases hB1 with h | h
      · have hd := dvd_sub h (dvd_mul_of_dvd_left hminus (N - 1))
        right
        have hd' : (p : ℤ) ∣ -2 := by convert hd using 1 <;> ring
        simpa using hd'
      · have hd := dvd_sub h (dvd_mul_of_dvd_left hminus (N + 3))
        right
        convert hd using 1 <;> ring
    · rcases hB1 with h | h
      · have hd := dvd_sub h (dvd_mul_of_dvd_left hplus (N - 3))
        right
        convert hd using 1 <;> ring
      · have hd := dvd_sub h (dvd_mul_of_dvd_left hplus (N + 1))
        right
        have hd' : (p : ℤ) ∣ -2 := by convert hd using 1 <;> ring
        simpa using hd'
  rcases hp1or2 with h | h
  · exact h
  · exact (hp2not h).elim

lemma valuation_zero_of_not_dvd {p : ℕ} (A : ℤ) (h : ¬(p : ℤ) ∣ A) :
    padicValRat p (A : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd h]
  norm_num

/-- Valuation of the exact formal-parameter quotient when the two retained
polynomial factors are local units. -/
theorem formalZ_valuation_of_units {p : ℕ} [Fact p.Prime] {N : ℤ} {D : ℕ} {s : ℤ}
    (hN : Even N) (hs : 0 < s)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2)
    (hA : ¬(p : ℤ) ∣ N ^ 2 + 1)
    (hB : ¬(p : ℤ) ∣ (N ^ 2 - 2 * N - 1) * (N ^ 2 + 2 * N - 1)) :
    padicValRat p (formalZ N s) =
      padicValRat p (2 : ℚ) + padicValRat p (s : ℚ) := by
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast (Int.ne_of_gt hs)
  have hAQ : (N : ℚ) ^ 2 + 1 ≠ 0 := by positivity
  have hBQ : ((N : ℚ) ^ 2 - 2 * N - 1) * ((N : ℚ) ^ 2 + 2 * N - 1) ≠ 0 := by
    have hB1 : ((N : ℚ) ^ 2 - 2 * N - 1) ≠ 0 := by
      exact_mod_cast odd_ne_zero (odd_sq_sub_two_mul_sub_one hN)
    have hB2 : ((N : ℚ) ^ 2 + 2 * N - 1) ≠ 0 := by
      exact_mod_cast odd_ne_zero (odd_sq_add_two_mul_sub_one hN)
    exact mul_ne_zero hB1 hB2
  have hnum : -(2 * (s : ℚ) * ((N : ℚ) ^ 2 + 1)) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hsQ) hAQ)
  have hAv := valuation_zero_of_not_dvd (p := p) (N ^ 2 + 1) hA
  have hBv := valuation_zero_of_not_dvd (p := p)
    ((N ^ 2 - 2 * N - 1) * (N ^ 2 + 2 * N - 1)) hB
  push_cast at hAv hBv
  rw [formalZ_eq hN hs hdecomp]
  push_cast
  rw [padicValRat.div hnum hBQ, padicValRat.neg,
    padicValRat.mul (mul_ne_zero (by norm_num) hsQ) hAQ,
    padicValRat.mul (by norm_num) hsQ, hAv, hBv]
  ring

/-- The dyadic formal-depth formula is separate from the odd-prime formula. -/
theorem dyadic_formal_depth {N : ℤ} {D : ℕ} {s : ℤ} (hN : Even N) (hs : 0 < s)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    padicValRat 2 (formalZ N s) = 1 + padicValRat 2 (s : ℚ) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [formalZ_valuation_of_units hN hs hdecomp
    (odd_not_two_dvd (odd_sq_add_one hN)) (odd_not_two_dvd (odd_yNumerator hN))]
  have hv2 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using (padicValRat.self (p := 2) Nat.prime_two.one_lt)
  rw [hv2]

/-- At an odd support prime of the squareclass parameter, the formal depth is
exactly `(k - 1) / 2`. The first equality is the division-free form. -/
theorem odd_prime_formal_depth {p : ℕ} [Fact p.Prime] {N : ℤ} {D : ℕ} {s : ℤ}
    (hp2 : p ≠ 2) (hN : Even N) (hD : 0 < D) (hs : 0 < s)
    (hDsf : Squarefree D) (hpD : p ∣ D)
    (hdecomp : N * (N ^ 2 - 1) = (D : ℤ) * s ^ 2) :
    let k := padicValRat p ((N * (N ^ 2 - 1) : ℤ) : ℚ)
    2 * padicValRat p (formalZ N s) + 1 = k ∧
      padicValRat p (formalZ N s) = (k - 1) / 2 := by
  have hp : p.Prime := Fact.out
  have hunits := numerator_units_of_odd_prime hp hp2 hpD hdecomp
  have hz := formalZ_valuation_of_units (p := p) hN hs hdecomp hunits.1 hunits.2
  have hpnot2 : ¬p ∣ 2 := by
    intro hd
    exact hp2 (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hp.ne_one)
  have hv2 : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hpnot2]
    norm_num
  have hzs : padicValRat p (formalZ N s) = padicValRat p (s : ℚ) := by
    rw [hz, hv2, zero_add]
  have hDval : padicValRat p (D : ℚ) = 1 := by
    have hfac : D.factorization p = 1 :=
      Nat.factorization_eq_one_of_squarefree hDsf hp hpD
    rw [padicValRat.of_nat, ← Nat.factorization_def D hp, hfac]
    norm_num
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast (Int.ne_of_gt hs)
  have hprod : padicValRat p ((N * (N ^ 2 - 1) : ℤ) : ℚ) =
      1 + 2 * padicValRat p (s : ℚ) := by
    rw [hdecomp]
    push_cast
    rw [padicValRat.mul hDQ (pow_ne_zero 2 hsQ), padicValRat.pow, hDval]
    ring
  dsimp
  rw [hprod, ← hzs]
  constructor
  · ring
  · omega

end SunElliotE364
