module

public import ZInQ.HeightConstantAlgorithm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Comparison of the literal six-contact height constants

The definitions follow `six-contact-height-proof.txt` and
`z-in-q-height-constant-comparison.txt`. The parameterized bodies keep
proofs symbolic; the final definitions use the literal value 324!.
-/

public section

namespace ZInQ.HeightConstantComparison

open scoped BigOperators

/-- The literal factorial in the source. -/
@[expose] def d0 : ℕ := Nat.factorial 324

/-- The degree expression with its factorial argument left symbolic. -/
@[expose] def degreeFromBase (D0 : ℕ) : ℕ := D0 * 3 ^ (256 * D0 ^ 4)

/-- The literal degree bound. -/
@[expose] def d : ℕ := degreeFromBase d0

/-- The fixed finite-group factor. -/
@[expose] def g0 : ℕ := 116064000000

/-- The conductor-exponent expression for a given degree. -/
@[expose] def e0ForDegree (D : ℕ) : ℕ := 10 * (D * g0) ^ 2

/-- The intermediate CM expression for a given degree. -/
@[expose] def bCmForDegree (D : ℕ) : ℕ := D ^ 2 * 3 ^ (21000 * D ^ 2) + 1

/-- The CM constant for a given degree. -/
@[expose] def cCmForDegree (D : ℕ) : ℕ :=
  2 * bCmForDegree D + 4096 * (1028 + 5 * D + 84000 * D ^ 2)

/-- R with a symbolic degree and set maximum. -/
@[expose] def rForDegree (D maxS : ℕ) : ℕ := max (max D maxS) (10 ^ 12)

/-- Q0 with symbolic parameters. -/
@[expose] def q0ForDegree (D maxS : ℕ) : ℕ :=
  rForDegree D maxS ^ (rForDegree D maxS * e0ForDegree D)

/-- The entire H6 expression with a symbolic degree. -/
@[expose] def h6ForDegree (D maxS : ℕ) : ℕ :=
  2 * 10 ^ 13 * max (max 1 (cCmForDegree D)) (q0ForDegree D maxS ^ 17)

/-- The product of the distinct elements of S. -/
@[expose] def primeProduct (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

/-- The independent constant C with a symbolic degree. -/
@[expose] def cForDegree (D : ℕ) (S : Finset ℕ) : ℕ :=
  10 ^ 13 * max ((8 * D) ^ (288 * D)) (6 ^ 100) * primeProduct S ^ 24

/-- The literal E0 from the source. -/
@[expose] def e0 : ℕ := e0ForDegree d

/-- The literal B(d) from the source. -/
@[expose] def bCm : ℕ := bCmForDegree d

/-- The literal C_CM(d) from the source. -/
@[expose] def cCm : ℕ := cCmForDegree d

/-- The literal R with a specified maximum parameter. -/
@[expose] def r (maxS : ℕ) : ℕ := rForDegree d maxS

/-- The literal Q0 with a specified maximum parameter. -/
@[expose] def q0 (maxS : ℕ) : ℕ := q0ForDegree d maxS

/-- The literal H6 with a specified maximum parameter. -/
@[expose] def h6ForMax (maxS : ℕ) : ℕ := h6ForDegree d maxS

/-- The literal H6(S); the empty set has maximum zero. -/
@[expose] def h6 (S : Finset ℕ) : ℕ := h6ForMax (S.sup id)

/-- The literal independently derived C(S). -/
@[expose] def c (S : Finset ℕ) : ℕ := cForDegree d S

theorem one_le_degree_from_base (D0 : ℕ) (hD0 : 1 ≤ D0) :
    1 ≤ degreeFromBase D0 := by
  dsimp only [degreeFromBase]
  exact Nat.mul_pos hD0 (pow_pos (by decide) _)

theorem one_le_d : 1 ≤ d :=
  one_le_degree_from_base d0 (Nat.factorial_pos _)

theorem two_le_g0 : 2 ≤ g0 := by decide

theorem degree_le_r_for_degree (D maxS : ℕ) : D ≤ rForDegree D maxS :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem max_le_r_for_degree (D maxS : ℕ) : maxS ≤ rForDegree D maxS :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem eight_le_r_for_degree (D maxS : ℕ) : 8 ≤ rForDegree D maxS :=
  (by decide : 8 ≤ (10 : ℕ) ^ 12).trans (le_max_right _ _)

/-- Bounding the finite product needs positivity, but no distribution of primes. -/
theorem prime_product_le_self_power (S : Finset ℕ) (R : ℕ)
    (hpos : ∀ p ∈ S, 0 < p) (hbound : ∀ p ∈ S, p ≤ R) (hR : 1 ≤ R) :
    primeProduct S ≤ R ^ R := by
  have hsub : S ⊆ Finset.Icc 1 R := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨hpos p hp, hbound p hp⟩
  have hcard : S.card ≤ R := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel_right] using Finset.card_le_card hsub
  calc
    primeProduct S ≤ R ^ S.card := Finset.prod_le_pow_card S id R hbound
    _ ≤ R ^ R := pow_le_pow_right₀ hR hcard

/-- The scalar comparison before substituting any enormous literal constant. -/
theorem max_factor_mul_product_le_main_power
    (d G R P : ℕ) (hd : 1 ≤ d) (hG : 2 ≤ G) (hR : 8 ≤ R)
    (hdR : d ≤ R) (hP : P ≤ R ^ R) :
    max ((8 * d) ^ (288 * d)) (6 ^ 100) * P ^ 24 ≤
      (R ^ (R * (10 * (d * G) ^ 2))) ^ 17 := by
  have hRone : 1 ≤ R := by omega
  have hbase : 8 * d ≤ R ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hR hdR
  have hfirst : (8 * d) ^ (288 * d) ≤ R ^ (576 * d) := by
    calc
      (8 * d) ^ (288 * d) ≤ (R ^ 2) ^ (288 * d) :=
        pow_le_pow_left' hbase _
      _ = R ^ (576 * d) := by
        rw [← pow_mul]
        congr 1
        omega
  have hsecond : 6 ^ 100 ≤ R ^ (576 * d) := by
    calc
      6 ^ 100 ≤ R ^ 100 := pow_le_pow_left' (by omega : 6 ≤ R) _
      _ ≤ R ^ (576 * d) := pow_le_pow_right₀ hRone (by omega)
  have hmax : max ((8 * d) ^ (288 * d)) (6 ^ 100) ≤ R ^ (576 * d) :=
    max_le hfirst hsecond
  have hprod : P ^ 24 ≤ R ^ (24 * R) := by
    calc
      P ^ 24 ≤ (R ^ R) ^ 24 := pow_le_pow_left' hP _
      _ = R ^ (24 * R) := by rw [← pow_mul, Nat.mul_comm R 24]
  have hsmall :
      max ((8 * d) ^ (288 * d)) (6 ^ 100) * P ^ 24 ≤ R ^ (600 * R) := by
    calc
      max ((8 * d) ^ (288 * d)) (6 ^ 100) * P ^ 24 ≤
          R ^ (576 * d) * R ^ (24 * R) := Nat.mul_le_mul hmax hprod
      _ = R ^ (576 * d + 24 * R) := (pow_add _ _ _).symm
      _ ≤ R ^ (600 * R) := pow_le_pow_right₀ hRone (by omega)
  have htwo : 2 ≤ d * G := by
    calc
      2 ≤ G := hG
      _ = 1 * G := (one_mul G).symm
      _ ≤ d * G := Nat.mul_le_mul_right G hd
  have hsquare : 4 ≤ (d * G) ^ 2 := by
    calc
      4 = (2 : ℕ) ^ 2 := by decide
      _ ≤ (d * G) ^ 2 := pow_le_pow_left' htwo _
  have hE : 600 ≤ 17 * (10 * (d * G) ^ 2) := by omega
  have hexp : 600 * R ≤ (R * (10 * (d * G) ^ 2)) * 17 := by
    calc
      600 * R = R * 600 := Nat.mul_comm _ _
      _ ≤ R * (17 * (10 * (d * G) ^ 2)) := Nat.mul_le_mul_left R hE
      _ = (R * (10 * (d * G) ^ 2)) * 17 := by ac_rfl
  exact hsmall.trans (by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hRone hexp)

/-- The independent constant is bounded by the non-CM term, with a symbolic degree. -/
theorem c_for_degree_le_main_power (D : ℕ) (S : Finset ℕ) (maxS : ℕ)
    (hD : 1 ≤ D) (hpos : ∀ p ∈ S, 0 < p) (hmax : S.sup id ≤ maxS) :
    cForDegree D S ≤ 10 ^ 13 * q0ForDegree D maxS ^ 17 := by
  have hRone : 1 ≤ rForDegree D maxS :=
    (by decide : 1 ≤ (8 : ℕ)).trans (eight_le_r_for_degree D maxS)
  have hp : primeProduct S ≤ rForDegree D maxS ^ rForDegree D maxS :=
    prime_product_le_self_power S (rForDegree D maxS) hpos
      (fun p hp => (Finset.le_sup (f := id) hp).trans
        (hmax.trans (max_le_r_for_degree D maxS))) hRone
  have hmain := max_factor_mul_product_le_main_power
    D g0 (rForDegree D maxS) (primeProduct S) hD two_le_g0
    (eight_le_r_for_degree D maxS) (degree_le_r_for_degree D maxS) hp
  dsimp only [cForDegree, q0ForDegree, e0ForDegree]
  rw [mul_assoc]
  exact Nat.mul_le_mul_left (10 ^ 13) hmain

theorem two_mul_c_for_degree_le_h6_for_degree (D : ℕ) (S : Finset ℕ) (maxS : ℕ)
    (hD : 1 ≤ D) (hpos : ∀ p ∈ S, 0 < p) (hmax : S.sup id ≤ maxS) :
    2 * cForDegree D S ≤ h6ForDegree D maxS := by
  calc
    2 * cForDegree D S ≤ 2 * (10 ^ 13 * q0ForDegree D maxS ^ 17) :=
      Nat.mul_le_mul_left 2 (c_for_degree_le_main_power D S maxS hD hpos hmax)
    _ = (2 * 10 ^ 13) * q0ForDegree D maxS ^ 17 := (mul_assoc _ _ _).symm
    _ ≤ (2 * 10 ^ 13) * max (max 1 (cCmForDegree D)) (q0ForDegree D maxS ^ 17) :=
      Nat.mul_le_mul_left _ (le_max_right _ _)
    _ = h6ForDegree D maxS := rfl

/-- The literal comparison, with the factorial and every constant substituted. -/
theorem c_le_main_power (S : Finset ℕ) (maxS : ℕ)
    (hpos : ∀ p ∈ S, 0 < p) (hmax : S.sup id ≤ maxS) :
    c S ≤ 10 ^ 13 * q0 maxS ^ 17 :=
  c_for_degree_le_main_power d S maxS one_le_d hpos hmax

theorem two_mul_c_le_h6_for_max (S : Finset ℕ) (maxS : ℕ)
    (hpos : ∀ p ∈ S, 0 < p) (hmax : S.sup id ≤ maxS) :
    2 * c S ≤ h6ForMax maxS :=
  two_mul_c_for_degree_le_h6_for_degree d S maxS one_le_d hpos hmax

/-- The factor-two comparison for every finite set of positive integers. -/
theorem two_mul_c_le_h6 (S : Finset ℕ) (hpos : ∀ p ∈ S, 0 < p) :
    2 * c S ≤ h6 S :=
  two_mul_c_le_h6_for_max S (S.sup id) hpos le_rfl

theorem c_le_h6 (S : Finset ℕ) (hpos : ∀ p ∈ S, 0 < p) :
    c S ≤ h6 S := by
  have hc : c S ≤ 2 * c S := by
    simpa only [one_mul] using Nat.mul_le_mul_right (c S) (by decide : 1 ≤ (2 : ℕ))
  exact hc.trans (two_mul_c_le_h6 S hpos)

/-- In particular the stronger comparison applies to the source's prime sets. -/
theorem two_mul_c_le_h6_of_primes (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    2 * c S ≤ h6 S :=
  two_mul_c_le_h6 S (fun p hp => (hprime p hp).pos)

theorem c_le_h6_of_primes (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    c S ≤ h6 S :=
  c_le_h6 S (fun p hp => (hprime p hp).pos)

/-- The fixed-maximum specialization has exactly the algorithm module's body. -/
theorem h6_for_degree_from_base_317_eq_height_body (D0 : ℕ) :
    h6ForDegree (degreeFromBase D0) 317 = HeightConstantAlgorithm.heightBody D0 := by
  rfl

/-- The two modules use the identical literal H6(primes <= 324) integer. -/
theorem h6_for_max_317_eq_height_constant :
    h6ForMax 317 = HeightConstantAlgorithm.heightConstant :=
  h6_for_degree_from_base_317_eq_height_body d0

end ZInQ.HeightConstantComparison

