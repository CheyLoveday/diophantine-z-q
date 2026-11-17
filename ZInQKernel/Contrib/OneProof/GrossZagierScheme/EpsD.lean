import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Factorization.Induction

/-!
# hgz-steps: `ε_D(n) = (n / |D|)` for an odd negative discriminant `D`

`ε_D` is the Kronecker symbol `(D / ·)` (the quadratic character of `ℚ(√D)`): completely
multiplicative, `(D / p)` the Legendre symbol for odd primes `p`, `(D / 2) = χ₈(D)`
(`0` if `D` even, `1` if `D ≡ ±1 (mod 8)`, `−1` if `D ≡ ±3 (mod 8)`), and `(D / 0) = [|D| = 1]`.
-/

open ZMod

namespace ZInQ.HGZSteps

/-- The Kronecker symbol `(D / p)` at a prime `p`: `χ₈(D)` at `p = 2`, the Legendre symbol
`(D / p) = J(D | p)` at odd `p`. -/
def kronPrime (D : ℤ) (p : ℕ) : ℤ := if p = 2 then χ₈ (D : ZMod 8) else jacobiSym D p

/-- **`ε_D`, the Kronecker symbol `(D / n)`**, completely multiplicative in `n ≥ 1`
(H. Cohen, *A course in computational algebraic number theory*, Def. 1.4.8; for a fundamental
discriminant `D` it is the quadratic Dirichlet character of `ℚ(√D)` of conductor `|D|`, Zagier,
*Zetafunktionen und quadratische Körper*, §8; UNVERIFIED locators). -/
def epsD (D : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then (if D.natAbs = 1 then 1 else 0) else n.factorization.prod fun p e => kronPrime D p ^ e

theorem epsD_one (D : ℤ) : epsD D 1 = 1 := by simp [epsD]

theorem epsD_mul (D : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    epsD D (m * n) = epsD D m * epsD D n := by
  simp only [epsD, mul_ne_zero hm hn, hm, hn, ite_false]
  rw [Nat.factorization_mul hm hn, Finsupp.prod_add_index']
  · intro a; simp
  · intro a b₁ b₂; rw [pow_add]

theorem epsD_prime (D : ℤ) {p : ℕ} (hp : p.Prime) : epsD D p = kronPrime D p := by
  simp only [epsD, hp.ne_zero, ite_false, hp.factorization, Finsupp.prod_single_index, pow_one,
    pow_zero]

/-- **`ε_D(n) = J(n | |D|)`** for `D < 0`, `D ≡ 1 (mod 4)` (in particular for odd negative
fundamental discriminants): quadratic reciprocity. -/
theorem epsD_eq_jacobiSym {D : ℤ} (hD : D < 0) (h4 : D % 4 = 1) (n : ℕ) :
    epsD D n = jacobiSym n D.natAbs := by
  have hb3 : D.natAbs % 4 = 3 := by omega
  have hbodd : Odd D.natAbs := Nat.odd_iff.mpr (by omega)
  have hb1 : 1 < D.natAbs := by omega
  induction n using Nat.recOnMul with
  | zero =>
    simp only [epsD, ite_true, show D.natAbs ≠ 1 by omega, ite_false, Nat.cast_zero]
    exact (jacobiSym.zero_left hb1).symm
  | one => rw [epsD_one, Nat.cast_one, jacobiSym.one_left]
  | prime p hp =>
    rw [epsD_prime D hp, kronPrime]
    split_ifs with h2
    · subst h2
      rw [Nat.cast_ofNat, jacobiSym.at_two hbodd]
      have hc : ((D.natAbs : ℕ) : ZMod 8) = ((-D : ℤ) : ZMod 8) := by
        rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hD.le]
      rw [hc, χ₈_int_eq_if_mod_eight, χ₈_int_eq_if_mod_eight]
      split_ifs <;> omega
    · have hpodd : Odd p := hp.odd_of_ne_two h2
      have hJ : jacobiSym D p = jacobiSym (-1) p * jacobiSym (D.natAbs : ℤ) p := by
        rw [← jacobiSym.mul_left]; congr 1; omega
      rw [hJ, jacobiSym.at_neg_one hpodd, χ₄_nat_eq_if_mod_four]
      have hp2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
      split_ifs with h0 h1
      · omega
      · rw [one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hbodd]
      · have h3 : p % 4 = 3 := by omega
        rw [jacobiSym.quadratic_reciprocity_three_mod_four hb3 h3]
        ring
  | mul a b ha hb =>
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · simpa using ha
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · simpa using hb
    rw [epsD_mul D ha0.ne' hb0.ne', ha, hb, Nat.cast_mul, jacobiSym.mul_left]

/-- At primes: `ε_D(p) = 1` iff `J(p | |D|) = 1` (the Heegner hypothesis in either form). -/
theorem epsD_prime_eq_one_iff {D : ℤ} (hD : D < 0) (h4 : D % 4 = 1) (p : ℕ) :
    epsD D p = 1 ↔ jacobiSym p D.natAbs = 1 := by
  rw [epsD_eq_jacobiSym hD h4]

/-- For an odd prime `p ∤ D`, `ε_D(p) = 1` iff `D` is a square mod `p` (the splitting criterion's
arithmetic side; Mathlib's `legendreSym.eq_one_iff`). -/
theorem epsD_eq_one_iff_isSquare {D : ℤ} {p : ℕ} [hp : Fact p.Prime] (h2 : p ≠ 2)
    (hD : (D : ZMod p) ≠ 0) : epsD D p = 1 ↔ IsSquare (D : ZMod p) := by
  rw [epsD_prime D hp.out, kronPrime, if_neg h2, ← jacobiSym.legendreSym.to_jacobiSym]
  exact legendreSym.eq_one_iff p hD

/-- `ε_D(2) = 1` iff `D ≡ 1 (mod 8)`, for `D ≡ 1 (mod 4)`. -/
theorem epsD_two_eq_one_iff {D : ℤ} (h4 : D % 4 = 1) : epsD D 2 = 1 ↔ D % 8 = 1 := by
  rw [epsD_prime D Nat.prime_two, kronPrime, if_pos rfl, χ₈_int_eq_if_mod_eight]
  split_ifs <;> simp_all <;> omega

end ZInQ.HGZSteps

