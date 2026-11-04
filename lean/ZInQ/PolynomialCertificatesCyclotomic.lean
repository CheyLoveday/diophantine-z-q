module

public import ZInQ.PolynomialCertificates
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# The pinned `phi` coefficient lists are cyclotomic polynomials

For the pinned (unchanged) definitions `phi1, phi3, phi5, phi7, phi11, phi13, phi17` of
`ZInQ.PolynomialCertificates`, this file proves `phiN = Polynomial.cyclotomic N ℤ`
over `Polynomial ℤ`, using Mathlib's genuine `Polynomial.cyclotomic`.

* `N = 1`: Mathlib's `Polynomial.cyclotomic_one`.
* `N ∈ {3, 5, 7, 11, 13, 17}`: Mathlib's `Polynomial.cyclotomic_prime`; the primality of
  each concrete numeral is proved locally inside the proof by `norm_num` (a kernel-checked
  proof term), and the geometric sum is expanded by `Finset.sum_range_succ` and closed by `ring`.

Scope: finite polynomial equalities only. Nothing here identifies the `raw`/`tau`
polynomials with character sums, nor proves any general Gauss theorem.
-/

public section

namespace ZInQ.PolynomialCertificates
open Polynomial

theorem phi1_eq_cyclotomic : phi1 = Polynomial.cyclotomic 1 ℤ := by
  rw [Polynomial.cyclotomic_one]
  unfold phi1
  simp only [map_neg, map_one]
  ring

theorem phi3_eq_cyclotomic : phi3 = Polynomial.cyclotomic 3 ℤ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Polynomial.cyclotomic_prime ℤ 3]
  unfold phi3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_one]
  ring

theorem phi5_eq_cyclotomic : phi5 = Polynomial.cyclotomic 5 ℤ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Polynomial.cyclotomic_prime ℤ 5]
  unfold phi5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_one]
  ring

theorem phi7_eq_cyclotomic : phi7 = Polynomial.cyclotomic 7 ℤ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Polynomial.cyclotomic_prime ℤ 7]
  unfold phi7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_one]
  ring

theorem phi11_eq_cyclotomic : phi11 = Polynomial.cyclotomic 11 ℤ := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  rw [Polynomial.cyclotomic_prime ℤ 11]
  unfold phi11
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_one]
  ring

theorem phi13_eq_cyclotomic : phi13 = Polynomial.cyclotomic 13 ℤ := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  rw [Polynomial.cyclotomic_prime ℤ 13]
  unfold phi13
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_one]
  ring

theorem phi17_eq_cyclotomic : phi17 = Polynomial.cyclotomic 17 ℤ := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  rw [Polynomial.cyclotomic_prime ℤ 17]
  unfold phi17
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_one]
  ring

end ZInQ.PolynomialCertificates
