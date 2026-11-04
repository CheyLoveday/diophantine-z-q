module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Boolean Hamming-weight digit polynomials

`hammingBitPolynomial n j` is the elementary symmetric polynomial of degree `2 ^ j` in the
variables `X i` (`i : Fin n`) over `ZMod 2`.

* Degree: every monomial `∏ i ∈ s, X i` with `#s = 2 ^ j` has total degree at most `2 ^ j`.
* Evaluation: at a Boolean point `x`, the monomial `∏ i ∈ s, X i` evaluates to `1` exactly when
  `s` lies in the true-coordinate set `T = {i | x i = true}`, and to `0` otherwise.  Hence the
  polynomial counts the `2 ^ j`-subsets of `T`, i.e. it evaluates to
  `Nat.choose #T (2 ^ j) = Nat.choose (∑ i, (x i).toNat) (2 ^ j)` modulo `2`.
* Digit: by Lucas's theorem for `p = 2` (Mathlib's
  `Choose.choose_modEq_choose_mod_mul_choose_div_nat`), applied inductively in `j`,
  `choose m (2 ^ j)` is congruent modulo `2` to bit `j` of `m`.

All endpoints are covered uniformly: `n = 0`, `j = 0`, and `2 ^ j > n` (where the
`powersetCard` is empty, the binomial coefficient vanishes and the bit is `false`).

This file supplies only the identity for the Hamming weight `H` itself; it makes no claim about
the digits of `-2H` or about any later shift/carry normalization.
-/

open scoped BigOperators

@[expose] public section

noncomputable section

namespace ZInQ.HammingDigits

/-- The elementary symmetric polynomial of degree `2 ^ j` in `n` variables over `ZMod 2`. -/
def hammingBitPolynomial (n j : Nat) : MvPolynomial (Fin n) (ZMod 2) :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard (2 ^ j),
    ∏ i ∈ s, MvPolynomial.X i

end ZInQ.HammingDigits

end

end

public section

namespace ZInQ.HammingDigits

/-- The Hamming weight of a Boolean vector is the size of its true-coordinate set. -/
private theorem sum_toNat_eq_card_filter {n : Nat} (x : Fin n → Bool) :
    (∑ i : Fin n, (x i).toNat) = (Finset.univ.filter (fun i => x i = true)).card := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl ?_
  intro i _
  cases x i <;> simp

/-- Lucas parity for `p = 2`: `choose m (2 ^ j)` reduced modulo `2` is bit `j` of `m`.

Proved by induction on `j` from Mathlib's one-step Lucas congruence
`choose m k ≡ choose (m % 2) (k % 2) * choose (m / 2) (k / 2) [MOD 2]`. -/
private theorem choose_two_pow_cast_eq_ite (m j : Nat) :
    (Nat.choose m (2 ^ j) : ZMod 2) = (if m.testBit j then 1 else 0) := by
  induction j generalizing m with
  | zero =>
    rw [Nat.pow_zero, Nat.choose_one_right, Nat.testBit_zero, ← ZMod.natCast_mod m 2]
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
  | succ j ih =>
    have hlucas : Nat.choose m (2 ^ (j + 1)) ≡
        Nat.choose (m % 2) (2 ^ (j + 1) % 2) * Nat.choose (m / 2) (2 ^ (j + 1) / 2) [MOD 2] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    have hmod : 2 ^ (j + 1) % 2 = 0 := by
      rw [Nat.pow_succ]
      exact Nat.mul_mod_left _ _
    have hdiv : 2 ^ (j + 1) / 2 = 2 ^ j := by
      rw [Nat.pow_succ]
      exact Nat.mul_div_cancel _ (by decide)
    rw [hmod, hdiv, Nat.choose_zero_right, Nat.one_mul] at hlucas
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hlucas, ih (m / 2), Nat.testBit_add_one]

theorem totalDegree_hammingBitPolynomial_le (n j : Nat) :
    (hammingBitPolynomial n j).totalDegree <= 2 ^ j := by
  unfold hammingBitPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  have hcard : s.card = 2 ^ j := (Finset.mem_powersetCard.mp hs).2
  calc (∏ i ∈ s, (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod 2))).totalDegree
      ≤ ∑ i ∈ s, (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree :=
        MvPolynomial.totalDegree_finsetProd s _
    _ = ∑ _i ∈ s, 1 := Finset.sum_congr rfl (fun i _ => MvPolynomial.totalDegree_X i)
    _ = s.card := (Finset.card_eq_sum_ones s).symm
    _ = 2 ^ j := hcard

theorem eval_hammingBitPolynomial_eq_choose (n j : Nat)
    (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => ((x i).toNat : ZMod 2))
      (hammingBitPolynomial n j) =
      (Nat.choose (∑ i : Fin n, (x i).toNat) (2 ^ j) : ZMod 2) := by
  have hx : ∀ i, ((x i).toNat : ZMod 2) = if x i = true then 1 else 0 := by
    intro i
    cases x i <;> simp
  -- Each monomial becomes the indicator of `s ⊆ T`.  The indicator is stated here, so that its
  -- `Decidable` instance is the one synthesized in this context (the one `Finset.sum_boole` and
  -- `Finset.mem_filter` check against), rather than the generic `Finset.decidableDforallFinset`
  -- produced by `Finset.prod_boole`.  The proof uses only `if_pos`/`if_neg`, which accept any
  -- `Decidable` instance.
  have hprod : ∀ s : Finset (Fin n),
      (∏ i ∈ s, (if x i = true then (1 : ZMod 2) else 0)) =
        if ∀ i ∈ s, x i = true then 1 else 0 := by
    intro s
    by_cases h : ∀ i ∈ s, x i = true
    · rw [if_pos h]
      exact Finset.prod_eq_one fun i hi => if_pos (h i hi)
    · rw [if_neg h]
      have hex : ∃ i ∈ s, ¬ x i = true :=
        Classical.byContradiction fun hne =>
          h fun i hi => Classical.byContradiction fun hxi => hne ⟨i, hi, hxi⟩
      rcases hex with ⟨i, hi, hxi⟩
      exact Finset.prod_eq_zero hi (if_neg hxi)
  -- The sum of indicators becomes a cardinality.
  simp only [hammingBitPolynomial, map_sum, map_prod, MvPolynomial.eval_X, hx, hprod,
    Finset.sum_boole]
  refine congrArg (Nat.cast : Nat → ZMod 2) ?_
  rw [sum_toNat_eq_card_filter x, ← Finset.card_powersetCard]
  refine congrArg Finset.card ?_
  ext s
  rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hcard⟩, hs⟩
    exact ⟨fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hs i hi⟩, hcard⟩
  · rintro ⟨hsub, hcard⟩
    exact ⟨⟨Finset.subset_univ s, hcard⟩, fun i hi => (Finset.mem_filter.mp (hsub hi)).2⟩

theorem eval_hammingBitPolynomial_eq_bit (n j : Nat)
    (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => ((x i).toNat : ZMod 2))
      (hammingBitPolynomial n j) =
      (if (∑ i : Fin n, (x i).toNat).testBit j then 1 else 0) := by
  rw [eval_hammingBitPolynomial_eq_choose]
  exact choose_two_pow_cast_eq_ite _ _

end ZInQ.HammingDigits

end
