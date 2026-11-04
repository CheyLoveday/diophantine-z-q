module

public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

/-!
# Finite Gauss polynomial certificates

Explicit integer polynomials for fourteen conductors. Both quotient identities
are checked by Lean's kernel using `ring`. The names `phi` and `tau` label
explicit coefficient lists. This file does not prove their identification with
`Polynomial.cyclotomic` or a general character sum, or a universal Gauss theorem.
-/

public section

namespace ZInQ.PolynomialCertificates
open Polynomial
noncomputable section
set_option maxRecDepth 4096

/-- A quotient identity gives divisibility. -/
theorem dvd_of_certificate (a phi q : Polynomial ℤ)
    (h : a = phi * q) : phi ∣ a := ⟨q, h⟩

/-- A polynomial identity can be evaluated in any commutative ring. -/
theorem eval_sub_of_certificate {R : Type*} [CommRing R]
    (a b phi q : Polynomial ℤ) (x : R)
    (h : a - b = phi * q) (hx : phi.eval₂ (Int.castRingHom R) x = 0) :
    a.eval₂ (Int.castRingHom R) x = b.eval₂ (Int.castRingHom R) x := by
  have he := congrArg (Polynomial.eval₂RingHom (Int.castRingHom R) x) h
  change (a - b).eval₂ (Int.castRingHom R) x =
    (phi * q).eval₂ (Int.castRingHom R) x at he
  rw [eval₂_sub, eval₂_mul, hx, zero_mul] at he
  exact sub_eq_zero.mp he

/-- The squared certificate gives its value at any root of its modulus. -/
theorem eval_square_of_certificate {R : Type*} [CommRing R]
    (tau phi q : Polynomial ℤ) (s : ℤ) (x : R)
    (h : tau ^ 2 - C s = phi * q) (hx : phi.eval₂ (Int.castRingHom R) x = 0) :
    (tau.eval₂ (Int.castRingHom R) x) ^ 2 = (s : R) := by
  have he := congrArg (Polynomial.eval₂RingHom (Int.castRingHom R) x) h
  change (tau ^ 2 - C s).eval₂ (Int.castRingHom R) x =
    (phi * q).eval₂ (Int.castRingHom R) x at he
  rw [eval₂_sub, eval₂_pow, eval₂_C, eval₂_mul, hx, zero_mul] at he
  exact sub_eq_zero.mp he

/-- Explicit coefficient polynomial for conductor 1. -/
@[expose] def raw1 : Polynomial ℤ := C (1 : ℤ)

/-- Explicit coefficient polynomial for conductor 1. -/
@[expose] def tau1 : Polynomial ℤ := C (1 : ℤ)

/-- Explicit coefficient polynomial for conductor 1. -/
@[expose] def phi1 : Polynomial ℤ := C (-1 : ℤ) + C (1 : ℤ) * X ^ 1

/-- Explicit coefficient polynomial for conductor 1. -/
@[expose] def rawQuotient1 : Polynomial ℤ := 0

/-- Explicit coefficient polynomial for conductor 1. -/
@[expose] def quotient1 : Polynomial ℤ := 0

theorem raw_certificate_1 : raw1 - tau1 = phi1 * rawQuotient1 := by
  unfold raw1 tau1 phi1 rawQuotient1
  simp only [map_neg, map_one]
  ring

theorem certificate_1 : tau1 ^ 2 - C (1 : ℤ) = phi1 * quotient1 := by
  unfold tau1 phi1 quotient1
  simp only [map_neg, map_one]
  ring

theorem raw_divisibility_1 : phi1 ∣ raw1 - tau1 :=
  dvd_of_certificate _ _ _ raw_certificate_1

theorem divisibility_1 : phi1 ∣ tau1 ^ 2 - C (1 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_1

/-- Explicit coefficient polynomial for conductor 3. -/
@[expose] def raw3 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (-1 : ℤ) * X ^ 2

/-- Explicit coefficient polynomial for conductor 3. -/
@[expose] def tau3 : Polynomial ℤ := C (1 : ℤ) + C (2 : ℤ) * X ^ 1

/-- Explicit coefficient polynomial for conductor 3. -/
@[expose] def phi3 : Polynomial ℤ := C (1 : ℤ) + C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2

/-- Explicit coefficient polynomial for conductor 3. -/
@[expose] def rawQuotient3 : Polynomial ℤ := C (-1 : ℤ)

/-- Explicit coefficient polynomial for conductor 3. -/
@[expose] def quotient3 : Polynomial ℤ := C (4 : ℤ)

theorem raw_certificate_3 : raw3 - tau3 = phi3 * rawQuotient3 := by
  unfold raw3 tau3 phi3 rawQuotient3
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_3 : tau3 ^ 2 - C (-3 : ℤ) = phi3 * quotient3 := by
  unfold tau3 phi3 quotient3
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_3 : phi3 ∣ raw3 - tau3 :=
  dvd_of_certificate _ _ _ raw_certificate_3

theorem divisibility_3 : phi3 ∣ tau3 ^ 2 - C (-3 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_3

/-- Explicit coefficient polynomial for conductor 5. -/
@[expose] def raw5 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (-1 : ℤ) * X ^ 2 + C (-1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4

/-- Explicit coefficient polynomial for conductor 5. -/
@[expose] def tau5 : Polynomial ℤ := C (-1 : ℤ) + C (-2 : ℤ) * X ^ 2 + C (-2 : ℤ) * X ^ 3

/-- Explicit coefficient polynomial for conductor 5. -/
@[expose] def phi5 : Polynomial ℤ := C (1 : ℤ) + C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4

/-- Explicit coefficient polynomial for conductor 5. -/
@[expose] def rawQuotient5 : Polynomial ℤ := C (1 : ℤ)

/-- Explicit coefficient polynomial for conductor 5. -/
@[expose] def quotient5 : Polynomial ℤ := C (-4 : ℤ) + C (4 : ℤ) * X ^ 1 + C (4 : ℤ) * X ^ 2

theorem raw_certificate_5 : raw5 - tau5 = phi5 * rawQuotient5 := by
  unfold raw5 tau5 phi5 rawQuotient5
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_5 : tau5 ^ 2 - C (5 : ℤ) = phi5 * quotient5 := by
  unfold tau5 phi5 quotient5
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_5 : phi5 ∣ raw5 - tau5 :=
  dvd_of_certificate _ _ _ raw_certificate_5

theorem divisibility_5 : phi5 ∣ tau5 ^ 2 - C (5 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_5

/-- Explicit coefficient polynomial for conductor 7. -/
@[expose] def raw7 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (-1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (-1 : ℤ) * X ^ 5 + C (-1 : ℤ) * X ^ 6

/-- Explicit coefficient polynomial for conductor 7. -/
@[expose] def tau7 : Polynomial ℤ := C (1 : ℤ) + C (2 : ℤ) * X ^ 1 + C (2 : ℤ) * X ^ 2 + C (2 : ℤ) * X ^ 4

/-- Explicit coefficient polynomial for conductor 7. -/
@[expose] def phi7 : Polynomial ℤ := C (1 : ℤ) + C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 5 + C (1 : ℤ) * X ^ 6

/-- Explicit coefficient polynomial for conductor 7. -/
@[expose] def rawQuotient7 : Polynomial ℤ := C (-1 : ℤ)

/-- Explicit coefficient polynomial for conductor 7. -/
@[expose] def quotient7 : Polynomial ℤ := C (8 : ℤ) + C (-4 : ℤ) * X ^ 1 + C (4 : ℤ) * X ^ 2

theorem raw_certificate_7 : raw7 - tau7 = phi7 * rawQuotient7 := by
  unfold raw7 tau7 phi7 rawQuotient7
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_7 : tau7 ^ 2 - C (-7 : ℤ) = phi7 * quotient7 := by
  unfold tau7 phi7 quotient7
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_7 : phi7 ∣ raw7 - tau7 :=
  dvd_of_certificate _ _ _ raw_certificate_7

theorem divisibility_7 : phi7 ∣ tau7 ^ 2 - C (-7 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_7

/-- Explicit coefficient polynomial for conductor 11. -/
@[expose] def raw11 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (-1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 5 + C (-1 : ℤ) * X ^ 6 + C (-1 : ℤ) * X ^ 7 + C (-1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 9 + C (-1 : ℤ) * X ^ 10

/-- Explicit coefficient polynomial for conductor 11. -/
@[expose] def tau11 : Polynomial ℤ := C (1 : ℤ) + C (2 : ℤ) * X ^ 1 + C (2 : ℤ) * X ^ 3 + C (2 : ℤ) * X ^ 4 + C (2 : ℤ) * X ^ 5 + C (2 : ℤ) * X ^ 9

/-- Explicit coefficient polynomial for conductor 11. -/
@[expose] def phi11 : Polynomial ℤ := C (1 : ℤ) + C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 5 + C (1 : ℤ) * X ^ 6 + C (1 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 9 + C (1 : ℤ) * X ^ 10

/-- Explicit coefficient polynomial for conductor 11. -/
@[expose] def rawQuotient11 : Polynomial ℤ := C (-1 : ℤ)

/-- Explicit coefficient polynomial for conductor 11. -/
@[expose] def quotient11 : Polynomial ℤ := C (12 : ℤ) + C (-8 : ℤ) * X ^ 1 + C (8 : ℤ) * X ^ 4 + C (-4 : ℤ) * X ^ 7 + C (4 : ℤ) * X ^ 8

theorem raw_certificate_11 : raw11 - tau11 = phi11 * rawQuotient11 := by
  unfold raw11 tau11 phi11 rawQuotient11
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_11 : tau11 ^ 2 - C (-11 : ℤ) = phi11 * quotient11 := by
  unfold tau11 phi11 quotient11
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_11 : phi11 ∣ raw11 - tau11 :=
  dvd_of_certificate _ _ _ raw_certificate_11

theorem divisibility_11 : phi11 ∣ tau11 ^ 2 - C (-11 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_11

/-- Explicit coefficient polynomial for conductor 13. -/
@[expose] def raw13 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (-1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (-1 : ℤ) * X ^ 5 + C (-1 : ℤ) * X ^ 6 + C (-1 : ℤ) * X ^ 7 + C (-1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 9 + C (1 : ℤ) * X ^ 10 + C (-1 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 12

/-- Explicit coefficient polynomial for conductor 13. -/
@[expose] def tau13 : Polynomial ℤ := C (-1 : ℤ) + C (-2 : ℤ) * X ^ 2 + C (-2 : ℤ) * X ^ 5 + C (-2 : ℤ) * X ^ 6 + C (-2 : ℤ) * X ^ 7 + C (-2 : ℤ) * X ^ 8 + C (-2 : ℤ) * X ^ 11

/-- Explicit coefficient polynomial for conductor 13. -/
@[expose] def phi13 : Polynomial ℤ := C (1 : ℤ) + C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 5 + C (1 : ℤ) * X ^ 6 + C (1 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 9 + C (1 : ℤ) * X ^ 10 + C (1 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 12

/-- Explicit coefficient polynomial for conductor 13. -/
@[expose] def rawQuotient13 : Polynomial ℤ := C (1 : ℤ)

/-- Explicit coefficient polynomial for conductor 13. -/
@[expose] def quotient13 : Polynomial ℤ := C (-12 : ℤ) + C (12 : ℤ) * X ^ 1 + C (4 : ℤ) * X ^ 2 + C (-4 : ℤ) * X ^ 3 + C (4 : ℤ) * X ^ 4 + C (8 : ℤ) * X ^ 7 + C (-4 : ℤ) * X ^ 9 + C (4 : ℤ) * X ^ 10

theorem raw_certificate_13 : raw13 - tau13 = phi13 * rawQuotient13 := by
  unfold raw13 tau13 phi13 rawQuotient13
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_13 : tau13 ^ 2 - C (13 : ℤ) = phi13 * quotient13 := by
  unfold tau13 phi13 quotient13
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_13 : phi13 ∣ raw13 - tau13 :=
  dvd_of_certificate _ _ _ raw_certificate_13

theorem divisibility_13 : phi13 ∣ tau13 ^ 2 - C (13 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_13

/-- Explicit coefficient polynomial for conductor 15. -/
@[expose] def raw15 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 4 + C (-1 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8 + C (-1 : ℤ) * X ^ 11 + C (-1 : ℤ) * X ^ 13 + C (-1 : ℤ) * X ^ 14

/-- Explicit coefficient polynomial for conductor 15. -/
@[expose] def tau15 : Polynomial ℤ := C (-3 : ℤ) + C (4 : ℤ) * X ^ 1 + C (2 : ℤ) * X ^ 2 + C (-2 : ℤ) * X ^ 3 + C (4 : ℤ) * X ^ 4 + C (-2 : ℤ) * X ^ 5 + C (2 : ℤ) * X ^ 7

/-- Explicit coefficient polynomial for conductor 15. -/
@[expose] def phi15 : Polynomial ℤ := C (1 : ℤ) + C (-1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 3 + C (-1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 5 + C (-1 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8

/-- Explicit coefficient polynomial for conductor 15. -/
@[expose] def rawQuotient15 : Polynomial ℤ := C (3 : ℤ) + C (-1 : ℤ) * X ^ 2 + C (-2 : ℤ) * X ^ 3 + C (-2 : ℤ) * X ^ 4 + C (-2 : ℤ) * X ^ 5 + C (-1 : ℤ) * X ^ 6

/-- Explicit coefficient polynomial for conductor 15. -/
@[expose] def quotient15 : Polynomial ℤ := C (24 : ℤ) + C (4 : ℤ) * X ^ 2 + C (8 : ℤ) * X ^ 3 + C (-4 : ℤ) * X ^ 4 + C (4 : ℤ) * X ^ 5 + C (4 : ℤ) * X ^ 6

theorem raw_certificate_15 : raw15 - tau15 = phi15 * rawQuotient15 := by
  unfold raw15 tau15 phi15 rawQuotient15
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_15 : tau15 ^ 2 - C (-15 : ℤ) = phi15 * quotient15 := by
  unfold tau15 phi15 quotient15
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_15 : phi15 ∣ raw15 - tau15 :=
  dvd_of_certificate _ _ _ raw_certificate_15

theorem divisibility_15 : phi15 ∣ tau15 ^ 2 - C (-15 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_15

/-- Explicit coefficient polynomial for conductor 17. -/
@[expose] def raw17 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (-1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (-1 : ℤ) * X ^ 5 + C (-1 : ℤ) * X ^ 6 + C (-1 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 9 + C (-1 : ℤ) * X ^ 10 + C (-1 : ℤ) * X ^ 11 + C (-1 : ℤ) * X ^ 12 + C (1 : ℤ) * X ^ 13 + C (-1 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 16

/-- Explicit coefficient polynomial for conductor 17. -/
@[expose] def tau17 : Polynomial ℤ := C (-1 : ℤ) + C (-2 : ℤ) * X ^ 3 + C (-2 : ℤ) * X ^ 5 + C (-2 : ℤ) * X ^ 6 + C (-2 : ℤ) * X ^ 7 + C (-2 : ℤ) * X ^ 10 + C (-2 : ℤ) * X ^ 11 + C (-2 : ℤ) * X ^ 12 + C (-2 : ℤ) * X ^ 14

/-- Explicit coefficient polynomial for conductor 17. -/
@[expose] def phi17 : Polynomial ℤ := C (1 : ℤ) + C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 5 + C (1 : ℤ) * X ^ 6 + C (1 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 9 + C (1 : ℤ) * X ^ 10 + C (1 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 12 + C (1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 16

/-- Explicit coefficient polynomial for conductor 17. -/
@[expose] def rawQuotient17 : Polynomial ℤ := C (1 : ℤ)

/-- Explicit coefficient polynomial for conductor 17. -/
@[expose] def quotient17 : Polynomial ℤ := C (-16 : ℤ) + C (16 : ℤ) * X ^ 1 + C (4 : ℤ) * X ^ 3 + C (-4 : ℤ) * X ^ 4 + C (4 : ℤ) * X ^ 5 + C (4 : ℤ) * X ^ 6 + C (-4 : ℤ) * X ^ 7 + C (4 : ℤ) * X ^ 8 + C (8 : ℤ) * X ^ 10 + C (-4 : ℤ) * X ^ 11 + C (4 : ℤ) * X ^ 12

theorem raw_certificate_17 : raw17 - tau17 = phi17 * rawQuotient17 := by
  unfold raw17 tau17 phi17 rawQuotient17
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_17 : tau17 ^ 2 - C (17 : ℤ) = phi17 * quotient17 := by
  unfold tau17 phi17 quotient17
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_17 : phi17 ∣ raw17 - tau17 :=
  dvd_of_certificate _ _ _ raw_certificate_17

theorem divisibility_17 : phi17 ∣ tau17 ^ 2 - C (17 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_17

/-- Explicit coefficient polynomial for conductor 21. -/
@[expose] def raw21 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (-1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 5 + C (-1 : ℤ) * X ^ 8 + C (-1 : ℤ) * X ^ 10 + C (-1 : ℤ) * X ^ 11 + C (-1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 17 + C (-1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 20

/-- Explicit coefficient polynomial for conductor 21. -/
@[expose] def tau21 : Polynomial ℤ := C (1 : ℤ) + C (2 : ℤ) * X ^ 1 + C (-4 : ℤ) * X ^ 2 + C (2 : ℤ) * X ^ 4 + C (2 : ℤ) * X ^ 7 + C (-2 : ℤ) * X ^ 8 + C (-2 : ℤ) * X ^ 9 + C (-2 : ℤ) * X ^ 11

/-- Explicit coefficient polynomial for conductor 21. -/
@[expose] def phi21 : Polynomial ℤ := C (1 : ℤ) + C (-1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 3 + C (-1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 6 + C (-1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 9 + C (-1 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 12

/-- Explicit coefficient polynomial for conductor 21. -/
@[expose] def rawQuotient21 : Polynomial ℤ := C (-1 : ℤ) + C (-2 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (2 : ℤ) * X ^ 3 + C (2 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 8

/-- Explicit coefficient polynomial for conductor 21. -/
@[expose] def quotient21 : Polynomial ℤ := C (-20 : ℤ) + C (-16 : ℤ) * X ^ 1 + C (-20 : ℤ) * X ^ 2 + C (-16 : ℤ) * X ^ 3 + C (12 : ℤ) * X ^ 5 + C (12 : ℤ) * X ^ 6 + C (16 : ℤ) * X ^ 7 + C (12 : ℤ) * X ^ 8 + C (4 : ℤ) * X ^ 9 + C (4 : ℤ) * X ^ 10

theorem raw_certificate_21 : raw21 - tau21 = phi21 * rawQuotient21 := by
  unfold raw21 tau21 phi21 rawQuotient21
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_21 : tau21 ^ 2 - C (21 : ℤ) = phi21 * quotient21 := by
  unfold tau21 phi21 quotient21
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_21 : phi21 ∣ raw21 - tau21 :=
  dvd_of_certificate _ _ _ raw_certificate_21

theorem divisibility_21 : phi21 ∣ tau21 ^ 2 - C (21 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_21

/-- Explicit coefficient polynomial for conductor 33. -/
@[expose] def raw33 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 4 + C (-1 : ℤ) * X ^ 5 + C (-1 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8 + C (-1 : ℤ) * X ^ 10 + C (-1 : ℤ) * X ^ 13 + C (-1 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 17 + C (-1 : ℤ) * X ^ 19 + C (-1 : ℤ) * X ^ 20 + C (-1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 25 + C (-1 : ℤ) * X ^ 26 + C (-1 : ℤ) * X ^ 28 + C (1 : ℤ) * X ^ 29 + C (1 : ℤ) * X ^ 31 + C (1 : ℤ) * X ^ 32

/-- Explicit coefficient polynomial for conductor 33. -/
@[expose] def tau33 : Polynomial ℤ := C (3 : ℤ) + C (2 : ℤ) * X ^ 3 + C (-2 : ℤ) * X ^ 5 + C (4 : ℤ) * X ^ 6 + C (-4 : ℤ) * X ^ 7 + C (2 : ℤ) * X ^ 9 + C (-4 : ℤ) * X ^ 10 + C (2 : ℤ) * X ^ 11 + C (2 : ℤ) * X ^ 12 + C (-4 : ℤ) * X ^ 13 + C (2 : ℤ) * X ^ 15 + C (-2 : ℤ) * X ^ 16 + C (4 : ℤ) * X ^ 17 + C (-4 : ℤ) * X ^ 19

/-- Explicit coefficient polynomial for conductor 33. -/
@[expose] def phi33 : Polynomial ℤ := C (1 : ℤ) + C (-1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 3 + C (-1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 6 + C (-1 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 9 + C (-1 : ℤ) * X ^ 10 + C (1 : ℤ) * X ^ 11 + C (-1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 14 + C (-1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 17 + C (-1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 20

/-- Explicit coefficient polynomial for conductor 33. -/
@[expose] def rawQuotient33 : Polynomial ℤ := C (-3 : ℤ) + C (-2 : ℤ) * X ^ 1 + C (-1 : ℤ) * X ^ 2 + C (-2 : ℤ) * X ^ 6 + C (2 : ℤ) * X ^ 9 + C (2 : ℤ) * X ^ 10 + C (2 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 12

/-- Explicit coefficient polynomial for conductor 33. -/
@[expose] def quotient33 : Polynomial ℤ := C (-24 : ℤ) + C (-24 : ℤ) * X ^ 1 + C (-24 : ℤ) * X ^ 2 + C (12 : ℤ) * X ^ 3 + C (12 : ℤ) * X ^ 4 + C (16 : ℤ) * X ^ 6 + C (-8 : ℤ) * X ^ 7 + C (-4 : ℤ) * X ^ 8 + C (-4 : ℤ) * X ^ 9 + C (-16 : ℤ) * X ^ 10 + C (12 : ℤ) * X ^ 11 + C (36 : ℤ) * X ^ 12 + C (-16 : ℤ) * X ^ 14 + C (-16 : ℤ) * X ^ 15 + C (-16 : ℤ) * X ^ 16 + C (16 : ℤ) * X ^ 17 + C (16 : ℤ) * X ^ 18

theorem raw_certificate_33 : raw33 - tau33 = phi33 * rawQuotient33 := by
  unfold raw33 tau33 phi33 rawQuotient33
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_33 : tau33 ^ 2 - C (33 : ℤ) = phi33 * quotient33 := by
  unfold tau33 phi33 quotient33
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_33 : phi33 ∣ raw33 - tau33 :=
  dvd_of_certificate _ _ _ raw_certificate_33

theorem divisibility_33 : phi33 ∣ tau33 ^ 2 - C (33 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_33

/-- Explicit coefficient polynomial for conductor 35. -/
@[expose] def raw35 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (-1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (-1 : ℤ) * X ^ 6 + C (-1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 9 + C (1 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 12 + C (1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 17 + C (-1 : ℤ) * X ^ 18 + C (-1 : ℤ) * X ^ 19 + C (-1 : ℤ) * X ^ 22 + C (-1 : ℤ) * X ^ 23 + C (-1 : ℤ) * X ^ 24 + C (-1 : ℤ) * X ^ 26 + C (1 : ℤ) * X ^ 27 + C (1 : ℤ) * X ^ 29 + C (-1 : ℤ) * X ^ 31 + C (-1 : ℤ) * X ^ 32 + C (1 : ℤ) * X ^ 33 + C (-1 : ℤ) * X ^ 34

/-- Explicit coefficient polynomial for conductor 35. -/
@[expose] def tau35 : Polynomial ℤ := C (-1 : ℤ) + C (4 : ℤ) * X ^ 4 + C (-2 : ℤ) * X ^ 5 + C (-4 : ℤ) * X ^ 8 + C (4 : ℤ) * X ^ 9 + C (-2 : ℤ) * X ^ 10 + C (4 : ℤ) * X ^ 11 + C (2 : ℤ) * X ^ 14 + C (-4 : ℤ) * X ^ 15 + C (4 : ℤ) * X ^ 16 + C (-2 : ℤ) * X ^ 20 + C (2 : ℤ) * X ^ 21 + C (-4 : ℤ) * X ^ 22

/-- Explicit coefficient polynomial for conductor 35. -/
@[expose] def phi35 : Polynomial ℤ := C (1 : ℤ) + C (-1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 5 + C (-1 : ℤ) * X ^ 6 + C (1 : ℤ) * X ^ 7 + C (-1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 10 + C (-1 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 12 + C (-1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 14 + C (-1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 17 + C (-1 : ℤ) * X ^ 18 + C (1 : ℤ) * X ^ 19 + C (-1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 24

/-- Explicit coefficient polynomial for conductor 35. -/
@[expose] def rawQuotient35 : Polynomial ℤ := C (1 : ℤ) + C (2 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (2 : ℤ) * X ^ 3 + C (-1 : ℤ) * X ^ 4 + C (-2 : ℤ) * X ^ 6 + C (-2 : ℤ) * X ^ 7 + C (-1 : ℤ) * X ^ 8 + C (-1 : ℤ) * X ^ 10

/-- Explicit coefficient polynomial for conductor 35. -/
@[expose] def quotient35 : Polynomial ℤ := C (36 : ℤ) + C (36 : ℤ) * X ^ 1 + C (36 : ℤ) * X ^ 2 + C (36 : ℤ) * X ^ 3 + C (28 : ℤ) * X ^ 4 + C (-4 : ℤ) * X ^ 5 + C (-4 : ℤ) * X ^ 6 + C (-40 : ℤ) * X ^ 7 + C (-16 : ℤ) * X ^ 8 + C (-32 : ℤ) * X ^ 9 + C (-28 : ℤ) * X ^ 10 + C (-28 : ℤ) * X ^ 11 + C (-28 : ℤ) * X ^ 12 + C (-4 : ℤ) * X ^ 13 + C (-16 : ℤ) * X ^ 14 + C (16 : ℤ) * X ^ 16 + C (12 : ℤ) * X ^ 17 + C (20 : ℤ) * X ^ 18 + C (16 : ℤ) * X ^ 20

theorem raw_certificate_35 : raw35 - tau35 = phi35 * rawQuotient35 := by
  unfold raw35 tau35 phi35 rawQuotient35
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_35 : tau35 ^ 2 - C (-35 : ℤ) = phi35 * quotient35 := by
  unfold tau35 phi35 quotient35
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_35 : phi35 ∣ raw35 - tau35 :=
  dvd_of_certificate _ _ _ raw_certificate_35

theorem divisibility_35 : phi35 ∣ tau35 ^ 2 - C (-35 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_35

/-- Explicit coefficient polynomial for conductor 65. -/
@[expose] def raw65 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (-1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (-1 : ℤ) * X ^ 6 + C (1 : ℤ) * X ^ 7 + C (1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 9 + C (-1 : ℤ) * X ^ 11 + C (-1 : ℤ) * X ^ 12 + C (1 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 16 + C (-1 : ℤ) * X ^ 17 + C (1 : ℤ) * X ^ 18 + C (-1 : ℤ) * X ^ 19 + C (-1 : ℤ) * X ^ 21 + C (-1 : ℤ) * X ^ 22 + C (-1 : ℤ) * X ^ 23 + C (-1 : ℤ) * X ^ 24 + C (-1 : ℤ) * X ^ 27 + C (1 : ℤ) * X ^ 28 + C (1 : ℤ) * X ^ 29 + C (-1 : ℤ) * X ^ 31 + C (1 : ℤ) * X ^ 32 + C (1 : ℤ) * X ^ 33 + C (-1 : ℤ) * X ^ 34 + C (1 : ℤ) * X ^ 36 + C (1 : ℤ) * X ^ 37 + C (-1 : ℤ) * X ^ 38 + C (-1 : ℤ) * X ^ 41 + C (-1 : ℤ) * X ^ 42 + C (-1 : ℤ) * X ^ 43 + C (-1 : ℤ) * X ^ 44 + C (-1 : ℤ) * X ^ 46 + C (1 : ℤ) * X ^ 47 + C (-1 : ℤ) * X ^ 48 + C (1 : ℤ) * X ^ 49 + C (1 : ℤ) * X ^ 51 + C (-1 : ℤ) * X ^ 53 + C (-1 : ℤ) * X ^ 54 + C (1 : ℤ) * X ^ 56 + C (1 : ℤ) * X ^ 57 + C (1 : ℤ) * X ^ 58 + C (-1 : ℤ) * X ^ 59 + C (1 : ℤ) * X ^ 61 + C (-1 : ℤ) * X ^ 62 + C (1 : ℤ) * X ^ 63 + C (1 : ℤ) * X ^ 64

/-- Explicit coefficient polynomial for conductor 65. -/
@[expose] def tau65 : Polynomial ℤ := C (1 : ℤ) + C (4 : ℤ) * X ^ 2 + C (-2 : ℤ) * X ^ 3 + C (-4 : ℤ) * X ^ 6 + C (4 : ℤ) * X ^ 7 + C (2 : ℤ) * X ^ 10 + C (-4 : ℤ) * X ^ 11 + C (4 : ℤ) * X ^ 15 + C (-2 : ℤ) * X ^ 16 + C (-4 : ℤ) * X ^ 19 + C (4 : ℤ) * X ^ 20 + C (-4 : ℤ) * X ^ 21 + C (-4 : ℤ) * X ^ 24 + C (2 : ℤ) * X ^ 25 + C (-2 : ℤ) * X ^ 26 + C (4 : ℤ) * X ^ 28 + C (-2 : ℤ) * X ^ 29 + C (2 : ℤ) * X ^ 30 + C (-4 : ℤ) * X ^ 31 + C (4 : ℤ) * X ^ 33 + C (-4 : ℤ) * X ^ 34 + C (2 : ℤ) * X ^ 35 + C (-2 : ℤ) * X ^ 39 + C (2 : ℤ) * X ^ 40 + C (-2 : ℤ) * X ^ 42 + C (-4 : ℤ) * X ^ 44

/-- Explicit coefficient polynomial for conductor 65. -/
@[expose] def phi65 : Polynomial ℤ := C (1 : ℤ) + C (-1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 5 + C (-1 : ℤ) * X ^ 6 + C (1 : ℤ) * X ^ 10 + C (-1 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 13 + C (-1 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 15 + C (-1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 18 + C (-1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 20 + C (-1 : ℤ) * X ^ 21 + C (1 : ℤ) * X ^ 23 + C (-1 : ℤ) * X ^ 24 + C (1 : ℤ) * X ^ 25 + C (-1 : ℤ) * X ^ 27 + C (1 : ℤ) * X ^ 28 + C (-1 : ℤ) * X ^ 29 + C (1 : ℤ) * X ^ 30 + C (-1 : ℤ) * X ^ 32 + C (1 : ℤ) * X ^ 33 + C (-1 : ℤ) * X ^ 34 + C (1 : ℤ) * X ^ 35 + C (-1 : ℤ) * X ^ 37 + C (1 : ℤ) * X ^ 38 + C (-1 : ℤ) * X ^ 42 + C (1 : ℤ) * X ^ 43 + C (-1 : ℤ) * X ^ 47 + C (1 : ℤ) * X ^ 48

/-- Explicit coefficient polynomial for conductor 65. -/
@[expose] def rawQuotient65 : Polynomial ℤ := C (-1 : ℤ) + C (-3 : ℤ) * X ^ 2 + C (-2 : ℤ) * X ^ 3 + C (-1 : ℤ) * X ^ 4 + C (2 : ℤ) * X ^ 6 + C (2 : ℤ) * X ^ 7 + C (2 : ℤ) * X ^ 8 + C (2 : ℤ) * X ^ 9 + C (2 : ℤ) * X ^ 12 + C (2 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 14 + C (2 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 16

/-- Explicit coefficient polynomial for conductor 65. -/
@[expose] def quotient65 : Polynomial ℤ := C (-64 : ℤ) + C (-64 : ℤ) * X ^ 1 + C (-56 : ℤ) * X ^ 2 + C (-60 : ℤ) * X ^ 3 + C (-44 : ℤ) * X ^ 4 + C (4 : ℤ) * X ^ 5 + C (-28 : ℤ) * X ^ 8 + C (4 : ℤ) * X ^ 9 + C (8 : ℤ) * X ^ 10 + C (4 : ℤ) * X ^ 11 + C (28 : ℤ) * X ^ 12 + C (52 : ℤ) * X ^ 13 + C (36 : ℤ) * X ^ 14 + C (48 : ℤ) * X ^ 15 + C (40 : ℤ) * X ^ 16 + C (72 : ℤ) * X ^ 17 + C (32 : ℤ) * X ^ 18 + C (4 : ℤ) * X ^ 19 + C (8 : ℤ) * X ^ 20 + C (-32 : ℤ) * X ^ 21 + C (-32 : ℤ) * X ^ 22 + C (-36 : ℤ) * X ^ 23 + C (-24 : ℤ) * X ^ 24 + C (-8 : ℤ) * X ^ 25 + C (-20 : ℤ) * X ^ 26 + C (-4 : ℤ) * X ^ 27 + C (-8 : ℤ) * X ^ 28 + C (-16 : ℤ) * X ^ 29 + C (16 : ℤ) * X ^ 30 + C (-4 : ℤ) * X ^ 31 + C (8 : ℤ) * X ^ 32 + C (4 : ℤ) * X ^ 33 + C (12 : ℤ) * X ^ 34 + C (20 : ℤ) * X ^ 35 + C (20 : ℤ) * X ^ 36 + C (32 : ℤ) * X ^ 37 + C (32 : ℤ) * X ^ 38 + C (16 : ℤ) * X ^ 39 + C (16 : ℤ) * X ^ 40

theorem raw_certificate_65 : raw65 - tau65 = phi65 * rawQuotient65 := by
  unfold raw65 tau65 phi65 rawQuotient65
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_65 : tau65 ^ 2 - C (65 : ℤ) = phi65 * quotient65 := by
  unfold tau65 phi65 quotient65
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_65 : phi65 ∣ raw65 - tau65 :=
  dvd_of_certificate _ _ _ raw_certificate_65

theorem divisibility_65 : phi65 ∣ tau65 ^ 2 - C (65 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_65

/-- Explicit coefficient polynomial for conductor 77. -/
@[expose] def raw77 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (-1 : ℤ) * X ^ 2 + C (-1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (-1 : ℤ) * X ^ 5 + C (1 : ℤ) * X ^ 6 + C (-1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 9 + C (1 : ℤ) * X ^ 10 + C (-1 : ℤ) * X ^ 12 + C (1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 17 + C (-1 : ℤ) * X ^ 18 + C (1 : ℤ) * X ^ 19 + C (-1 : ℤ) * X ^ 20 + C (1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 24 + C (1 : ℤ) * X ^ 25 + C (-1 : ℤ) * X ^ 26 + C (-1 : ℤ) * X ^ 27 + C (-1 : ℤ) * X ^ 29 + C (-1 : ℤ) * X ^ 30 + C (-1 : ℤ) * X ^ 31 + C (-1 : ℤ) * X ^ 32 + C (-1 : ℤ) * X ^ 34 + C (1 : ℤ) * X ^ 36 + C (1 : ℤ) * X ^ 37 + C (-1 : ℤ) * X ^ 38 + C (-1 : ℤ) * X ^ 39 + C (1 : ℤ) * X ^ 40 + C (1 : ℤ) * X ^ 41 + C (-1 : ℤ) * X ^ 43 + C (-1 : ℤ) * X ^ 45 + C (-1 : ℤ) * X ^ 46 + C (-1 : ℤ) * X ^ 47 + C (-1 : ℤ) * X ^ 48 + C (-1 : ℤ) * X ^ 50 + C (-1 : ℤ) * X ^ 51 + C (1 : ℤ) * X ^ 52 + C (1 : ℤ) * X ^ 53 + C (1 : ℤ) * X ^ 54 + C (-1 : ℤ) * X ^ 57 + C (1 : ℤ) * X ^ 58 + C (-1 : ℤ) * X ^ 59 + C (1 : ℤ) * X ^ 60 + C (1 : ℤ) * X ^ 61 + C (1 : ℤ) * X ^ 62 + C (1 : ℤ) * X ^ 64 + C (-1 : ℤ) * X ^ 65 + C (1 : ℤ) * X ^ 67 + C (1 : ℤ) * X ^ 68 + C (-1 : ℤ) * X ^ 69 + C (1 : ℤ) * X ^ 71 + C (-1 : ℤ) * X ^ 72 + C (1 : ℤ) * X ^ 73 + C (-1 : ℤ) * X ^ 74 + C (-1 : ℤ) * X ^ 75 + C (1 : ℤ) * X ^ 76

/-- Explicit coefficient polynomial for conductor 77. -/
@[expose] def tau77 : Polynomial ℤ := C (-3 : ℤ) + C (2 : ℤ) * X ^ 4 + C (-4 : ℤ) * X ^ 7 + C (4 : ℤ) * X ^ 9 + C (-2 : ℤ) * X ^ 11 + C (-2 : ℤ) * X ^ 14 + C (2 : ℤ) * X ^ 15 + C (4 : ℤ) * X ^ 16 + C (-4 : ℤ) * X ^ 18 + C (4 : ℤ) * X ^ 19 + C (-4 : ℤ) * X ^ 21 + C (-2 : ℤ) * X ^ 22 + C (4 : ℤ) * X ^ 23 + C (2 : ℤ) * X ^ 26 + C (-4 : ℤ) * X ^ 28 + C (-4 : ℤ) * X ^ 29 + C (4 : ℤ) * X ^ 30 + C (-4 : ℤ) * X ^ 32 + C (-4 : ℤ) * X ^ 35 + C (6 : ℤ) * X ^ 37 + C (-4 : ℤ) * X ^ 39 + C (4 : ℤ) * X ^ 41 + C (-2 : ℤ) * X ^ 42 + C (-4 : ℤ) * X ^ 43 + C (2 : ℤ) * X ^ 44 + C (-4 : ℤ) * X ^ 46 + C (2 : ℤ) * X ^ 48 + C (-2 : ℤ) * X ^ 49 + C (-4 : ℤ) * X ^ 50 + C (4 : ℤ) * X ^ 52 + C (-2 : ℤ) * X ^ 56 + C (-4 : ℤ) * X ^ 57 + C (4 : ℤ) * X ^ 58 + C (2 : ℤ) * X ^ 59

/-- Explicit coefficient polynomial for conductor 77. -/
@[expose] def phi77 : Polynomial ℤ := C (1 : ℤ) + C (-1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 7 + C (-1 : ℤ) * X ^ 8 + C (1 : ℤ) * X ^ 11 + C (-1 : ℤ) * X ^ 12 + C (1 : ℤ) * X ^ 14 + C (-1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 18 + C (-1 : ℤ) * X ^ 19 + C (1 : ℤ) * X ^ 21 + C (-1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 25 + C (-1 : ℤ) * X ^ 26 + C (1 : ℤ) * X ^ 28 + C (-1 : ℤ) * X ^ 30 + C (1 : ℤ) * X ^ 32 + C (-1 : ℤ) * X ^ 34 + C (1 : ℤ) * X ^ 35 + C (-1 : ℤ) * X ^ 37 + C (1 : ℤ) * X ^ 39 + C (-1 : ℤ) * X ^ 41 + C (1 : ℤ) * X ^ 42 + C (-1 : ℤ) * X ^ 45 + C (1 : ℤ) * X ^ 46 + C (-1 : ℤ) * X ^ 48 + C (1 : ℤ) * X ^ 49 + C (-1 : ℤ) * X ^ 52 + C (1 : ℤ) * X ^ 53 + C (-1 : ℤ) * X ^ 59 + C (1 : ℤ) * X ^ 60

/-- Explicit coefficient polynomial for conductor 77. -/
@[expose] def rawQuotient77 : Polynomial ℤ := C (3 : ℤ) + C (4 : ℤ) * X ^ 1 + C (3 : ℤ) * X ^ 2 + C (2 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 6 + C (2 : ℤ) * X ^ 7 + C (-2 : ℤ) * X ^ 9 + C (-1 : ℤ) * X ^ 12 + C (-1 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 16

/-- Explicit coefficient polynomial for conductor 77. -/
@[expose] def quotient77 : Polynomial ℤ := C (-68 : ℤ) + C (-68 : ℤ) * X ^ 1 + C (-68 : ℤ) * X ^ 2 + C (-68 : ℤ) * X ^ 3 + C (-80 : ℤ) * X ^ 4 + C (-80 : ℤ) * X ^ 5 + C (-80 : ℤ) * X ^ 6 + C (12 : ℤ) * X ^ 7 + C (16 : ℤ) * X ^ 8 + C (-8 : ℤ) * X ^ 9 + C (-8 : ℤ) * X ^ 10 + C (68 : ℤ) * X ^ 11 + C (68 : ℤ) * X ^ 12 + C (84 : ℤ) * X ^ 13 + C (88 : ℤ) * X ^ 14 + C (76 : ℤ) * X ^ 15 + C (44 : ℤ) * X ^ 16 + C (44 : ℤ) * X ^ 17 + C (4 : ℤ) * X ^ 18 + C (-16 : ℤ) * X ^ 19 + C (-8 : ℤ) * X ^ 20 + C (4 : ℤ) * X ^ 21 + C (4 : ℤ) * X ^ 25 + C (-16 : ℤ) * X ^ 26 + C (-16 : ℤ) * X ^ 27 + C (36 : ℤ) * X ^ 28 + C (48 : ℤ) * X ^ 29 + C (12 : ℤ) * X ^ 30 + C (12 : ℤ) * X ^ 31 + C (32 : ℤ) * X ^ 32 + C (32 : ℤ) * X ^ 33 + C (48 : ℤ) * X ^ 34 + C (60 : ℤ) * X ^ 35 + C (28 : ℤ) * X ^ 36 + C (-16 : ℤ) * X ^ 37 + C (12 : ℤ) * X ^ 39 + C (-4 : ℤ) * X ^ 40 + C (-24 : ℤ) * X ^ 41 + C (-4 : ℤ) * X ^ 42 + C (-20 : ℤ) * X ^ 43 + C (-28 : ℤ) * X ^ 44 + C (-28 : ℤ) * X ^ 45 + C (-16 : ℤ) * X ^ 47 + C (-36 : ℤ) * X ^ 48 + C (-20 : ℤ) * X ^ 49 + C (28 : ℤ) * X ^ 50 + C (12 : ℤ) * X ^ 51 + C (-4 : ℤ) * X ^ 53 + C (-20 : ℤ) * X ^ 54 + C (-20 : ℤ) * X ^ 55 + C (20 : ℤ) * X ^ 56 + C (20 : ℤ) * X ^ 57 + C (4 : ℤ) * X ^ 58

theorem raw_certificate_77 : raw77 - tau77 = phi77 * rawQuotient77 := by
  unfold raw77 tau77 phi77 rawQuotient77
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_77 : tau77 ^ 2 - C (77 : ℤ) = phi77 * quotient77 := by
  unfold tau77 phi77 quotient77
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_77 : phi77 ∣ raw77 - tau77 :=
  dvd_of_certificate _ _ _ raw_certificate_77

theorem divisibility_77 : phi77 ∣ tau77 ^ 2 - C (77 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_77

/-- Explicit coefficient polynomial for conductor 105. -/
@[expose] def raw105 : Polynomial ℤ := C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 4 + C (1 : ℤ) * X ^ 8 + C (-1 : ℤ) * X ^ 11 + C (1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 16 + C (-1 : ℤ) * X ^ 17 + C (-1 : ℤ) * X ^ 19 + C (-1 : ℤ) * X ^ 22 + C (1 : ℤ) * X ^ 23 + C (1 : ℤ) * X ^ 26 + C (-1 : ℤ) * X ^ 29 + C (-1 : ℤ) * X ^ 31 + C (1 : ℤ) * X ^ 32 + C (-1 : ℤ) * X ^ 34 + C (-1 : ℤ) * X ^ 37 + C (-1 : ℤ) * X ^ 38 + C (1 : ℤ) * X ^ 41 + C (-1 : ℤ) * X ^ 43 + C (-1 : ℤ) * X ^ 44 + C (1 : ℤ) * X ^ 46 + C (-1 : ℤ) * X ^ 47 + C (1 : ℤ) * X ^ 52 + C (1 : ℤ) * X ^ 53 + C (-1 : ℤ) * X ^ 58 + C (1 : ℤ) * X ^ 59 + C (-1 : ℤ) * X ^ 61 + C (-1 : ℤ) * X ^ 62 + C (1 : ℤ) * X ^ 64 + C (-1 : ℤ) * X ^ 67 + C (-1 : ℤ) * X ^ 68 + C (-1 : ℤ) * X ^ 71 + C (1 : ℤ) * X ^ 73 + C (-1 : ℤ) * X ^ 74 + C (-1 : ℤ) * X ^ 76 + C (1 : ℤ) * X ^ 79 + C (1 : ℤ) * X ^ 82 + C (-1 : ℤ) * X ^ 83 + C (-1 : ℤ) * X ^ 86 + C (-1 : ℤ) * X ^ 88 + C (1 : ℤ) * X ^ 89 + C (1 : ℤ) * X ^ 92 + C (-1 : ℤ) * X ^ 94 + C (1 : ℤ) * X ^ 97 + C (1 : ℤ) * X ^ 101 + C (1 : ℤ) * X ^ 103 + C (1 : ℤ) * X ^ 104

/-- Explicit coefficient polynomial for conductor 105. -/
@[expose] def tau105 : Polynomial ℤ := C (-1 : ℤ) + C (4 : ℤ) * X ^ 1 + C (2 : ℤ) * X ^ 2 + C (2 : ℤ) * X ^ 3 + C (6 : ℤ) * X ^ 4 + C (4 : ℤ) * X ^ 5 + C (-2 : ℤ) * X ^ 8 + C (-2 : ℤ) * X ^ 9 + C (-2 : ℤ) * X ^ 10 + C (-2 : ℤ) * X ^ 11 + C (-2 : ℤ) * X ^ 12 + C (-2 : ℤ) * X ^ 14 + C (4 : ℤ) * X ^ 16 + C (-2 : ℤ) * X ^ 17 + C (2 : ℤ) * X ^ 18 + C (-2 : ℤ) * X ^ 19 + C (4 : ℤ) * X ^ 20 + C (-2 : ℤ) * X ^ 21 + C (4 : ℤ) * X ^ 24 + C (4 : ℤ) * X ^ 26 + C (-2 : ℤ) * X ^ 27 + C (-6 : ℤ) * X ^ 29 + C (-2 : ℤ) * X ^ 30 + C (-2 : ℤ) * X ^ 31 + C (-2 : ℤ) * X ^ 34 + C (2 : ℤ) * X ^ 35 + C (2 : ℤ) * X ^ 36 + C (2 : ℤ) * X ^ 37 + C (-2 : ℤ) * X ^ 38 + C (6 : ℤ) * X ^ 39 + C (4 : ℤ) * X ^ 41 + C (-2 : ℤ) * X ^ 42 + C (-2 : ℤ) * X ^ 43 + C (-6 : ℤ) * X ^ 44 + C (2 : ℤ) * X ^ 46

/-- Explicit coefficient polynomial for conductor 105. -/
@[expose] def phi105 : Polynomial ℤ := C (1 : ℤ) + C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (-1 : ℤ) * X ^ 5 + C (-1 : ℤ) * X ^ 6 + C (-2 : ℤ) * X ^ 7 + C (-1 : ℤ) * X ^ 8 + C (-1 : ℤ) * X ^ 9 + C (1 : ℤ) * X ^ 12 + C (1 : ℤ) * X ^ 13 + C (1 : ℤ) * X ^ 14 + C (1 : ℤ) * X ^ 15 + C (1 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 17 + C (-1 : ℤ) * X ^ 20 + C (-1 : ℤ) * X ^ 22 + C (-1 : ℤ) * X ^ 24 + C (-1 : ℤ) * X ^ 26 + C (-1 : ℤ) * X ^ 28 + C (1 : ℤ) * X ^ 31 + C (1 : ℤ) * X ^ 32 + C (1 : ℤ) * X ^ 33 + C (1 : ℤ) * X ^ 34 + C (1 : ℤ) * X ^ 35 + C (1 : ℤ) * X ^ 36 + C (-1 : ℤ) * X ^ 39 + C (-1 : ℤ) * X ^ 40 + C (-2 : ℤ) * X ^ 41 + C (-1 : ℤ) * X ^ 42 + C (-1 : ℤ) * X ^ 43 + C (1 : ℤ) * X ^ 46 + C (1 : ℤ) * X ^ 47 + C (1 : ℤ) * X ^ 48

/-- Explicit coefficient polynomial for conductor 105. -/
@[expose] def rawQuotient105 : Polynomial ℤ := C (1 : ℤ) + C (-4 : ℤ) * X ^ 1 + C (2 : ℤ) * X ^ 2 + C (-7 : ℤ) * X ^ 4 + C (4 : ℤ) * X ^ 5 + C (-4 : ℤ) * X ^ 7 + C (2 : ℤ) * X ^ 8 + C (-2 : ℤ) * X ^ 9 + C (-3 : ℤ) * X ^ 10 + C (-2 : ℤ) * X ^ 11 + C (3 : ℤ) * X ^ 12 + C (-2 : ℤ) * X ^ 13 + C (-2 : ℤ) * X ^ 14 + C (-4 : ℤ) * X ^ 16 + C (4 : ℤ) * X ^ 17 + C (-5 : ℤ) * X ^ 18 + C (4 : ℤ) * X ^ 19 + C (-2 : ℤ) * X ^ 20 + C (-4 : ℤ) * X ^ 21 + C (7 : ℤ) * X ^ 22 + C (-8 : ℤ) * X ^ 23 + C (2 : ℤ) * X ^ 24 + C (2 : ℤ) * X ^ 25 + C (-2 : ℤ) * X ^ 26 + C (2 : ℤ) * X ^ 27 + C (-2 : ℤ) * X ^ 28 + C (2 : ℤ) * X ^ 29 + C (-4 : ℤ) * X ^ 30 + C (4 : ℤ) * X ^ 31 + C (-2 : ℤ) * X ^ 33 + C (4 : ℤ) * X ^ 34 + C (-4 : ℤ) * X ^ 35 + C (3 : ℤ) * X ^ 36 + C (-1 : ℤ) * X ^ 38 + C (4 : ℤ) * X ^ 39 + C (-3 : ℤ) * X ^ 40 + C (2 : ℤ) * X ^ 41 + C (2 : ℤ) * X ^ 44 + C (1 : ℤ) * X ^ 46 + C (2 : ℤ) * X ^ 50 + C (-1 : ℤ) * X ^ 52 + C (2 : ℤ) * X ^ 53 + C (-1 : ℤ) * X ^ 54 + C (1 : ℤ) * X ^ 56

/-- Explicit coefficient polynomial for conductor 105. -/
@[expose] def quotient105 : Polynomial ℤ := C (-104 : ℤ) + C (96 : ℤ) * X ^ 1 + C (20 : ℤ) * X ^ 2 + C (-104 : ℤ) * X ^ 3 + C (92 : ℤ) * X ^ 4 + C (-44 : ℤ) * X ^ 5 + C (4 : ℤ) * X ^ 6 + C (-12 : ℤ) * X ^ 7 + C (68 : ℤ) * X ^ 8 + C (-116 : ℤ) * X ^ 10 + C (148 : ℤ) * X ^ 11 + C (-88 : ℤ) * X ^ 12 + C (-12 : ℤ) * X ^ 13 + C (40 : ℤ) * X ^ 14 + C (12 : ℤ) * X ^ 15 + C (-16 : ℤ) * X ^ 16 + C (-36 : ℤ) * X ^ 17 + C (52 : ℤ) * X ^ 18 + C (-60 : ℤ) * X ^ 19 + C (32 : ℤ) * X ^ 20 + C (52 : ℤ) * X ^ 21 + C (-48 : ℤ) * X ^ 22 + C (-52 : ℤ) * X ^ 23 + C (36 : ℤ) * X ^ 24 + C (28 : ℤ) * X ^ 25 + C (-60 : ℤ) * X ^ 26 + C (88 : ℤ) * X ^ 27 + C (-28 : ℤ) * X ^ 28 + C (-8 : ℤ) * X ^ 30 + C (28 : ℤ) * X ^ 31 + C (-48 : ℤ) * X ^ 32 + C (-36 : ℤ) * X ^ 33 + C (104 : ℤ) * X ^ 34 + C (-44 : ℤ) * X ^ 35 + C (-32 : ℤ) * X ^ 37 + C (4 : ℤ) * X ^ 38 + C (-8 : ℤ) * X ^ 39 + C (32 : ℤ) * X ^ 40 + C (20 : ℤ) * X ^ 41 + C (-24 : ℤ) * X ^ 42 + C (-4 : ℤ) * X ^ 43 + C (4 : ℤ) * X ^ 44

theorem raw_certificate_105 : raw105 - tau105 = phi105 * rawQuotient105 := by
  unfold raw105 tau105 phi105 rawQuotient105
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem certificate_105 : tau105 ^ 2 - C (105 : ℤ) = phi105 * quotient105 := by
  unfold tau105 phi105 quotient105
  simp only [map_ofNat, map_neg, map_one]
  ring

theorem raw_divisibility_105 : phi105 ∣ raw105 - tau105 :=
  dvd_of_certificate _ _ _ raw_certificate_105

theorem divisibility_105 : phi105 ∣ tau105 ^ 2 - C (105 : ℤ) :=
  dvd_of_certificate _ _ _ certificate_105

end

end ZInQ.PolynomialCertificates
