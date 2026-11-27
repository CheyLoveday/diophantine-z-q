import ZInQKernel.Target
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Group.Unbundled.Int

/-!
# Theorem 1.1 as printed, and `ZInQ.FrozenTarget` (`Contrib/OneProof/PrintedTheorem11.lean`)

A cross-check of the frozen target against the manuscript's own statement, as asked in
elliotglazer/diophantine-z-q#6. `Theorem11` is Theorem 1.1 (`thm:target`, "A polynomial definition of the
integers") of the 11/5 manuscript, written from its printed text and the tower notation defined just before it
(`\tw 1 = 2`, `\tw (r+1) = 2^{\tw r}`), not from `ZInQKernel/Target.lean`. `theorem11_iff_frozenTarget`
proves it equivalent to `ZInQ.FrozenTarget` in both directions.

The two statements differ only in how they are written, and the proof turns each difference into a lemma:

* the tower `tw` against Mathlib's `hyperoperation 4 2` (`tw_eq_hyperoperation`, by induction);
* `|[X^α]P| < tw 8` with the absolute value in `ℤ` against `(P.coeff α).natAbs < hyperoperation 4 2 8`
  (`abs_lt_natCast_iff`);
* "`q ∈ ℤ`, the ordinary embedded integers" as membership in the range of `ℤ → ℚ` against
  `∃ z : ℤ, (z : ℚ) = q`, and the two sides of the equivalence in the printed order;
* `P(q, w₁, …)` as the evaluation of `P`'s image in `ℚ[X]` at `Fin.cons q w` against `eval₂` with
  `Int.castRingHom ℚ` (`MvPolynomial.eval_map`).

The reading choices are stated in `Theorem11`'s docstring. Standard axioms only; no `sorry`. This file proves no
open hypothesis: it is a statement check, not a step of the proof. It never imports `ZInQKernel.OneProof.Main`.
Written with Claude (Anthropic).
-/

namespace ZInQ.PrintedTheorem11

open MvPolynomial

/-- The manuscript's tower (diophantine_zq.tex, the paragraph before Theorem 1.1): `\tw 1 = 2` and
`\tw (r+1) = 2 ^ \tw r`, associated to the right. The value at `0` is `1`, so that `tw 1 = 2 ^ 1 = 2`; the
theorem uses only `tw 7` and `tw 8`. -/
def tw : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 ^ tw r

theorem tw_one : tw 1 = 2 := rfl

theorem tw_succ (r : ℕ) : tw (r + 1) = 2 ^ tw r := rfl

/-- **Theorem 1.1** (`thm:target`, "A polynomial definition of the integers"), as printed in the 11/5
manuscript: one polynomial `P ∈ ℤ[X₀, X₁, …, X₂₉₂₈₉₀₂₃₁₉₀₄]` with `deg P < tw 7`, `|[X^α]P| < tw 8` for every
multi-index `α`, and, for `q ∈ ℚ`, `q ∈ ℤ` if and only if `P(q, w₁, …, w₂₉₂₈₉₀₂₃₁₉₀₄) = 0` for some rational
`w`. Read here: `X₀` takes `q` and `X_{i+1}` takes `wᵢ₊₁` (`Fin.cons`); `P(q, w)` is the evaluation of `P`'s
image in `ℚ[X]`; `|·|` is the absolute value in `ℤ`; "`q ∈ ℤ`, the ordinary embedded integers" is
membership in the range of `ℤ → ℚ`. -/
def Theorem11 : Prop :=
  ∃ P : MvPolynomial (Fin 292890231905) ℤ,
    P.totalDegree < tw 7 ∧
    (∀ α : Fin 292890231905 →₀ ℕ, |P.coeff α| < (tw 8 : ℤ)) ∧
    ∀ q : ℚ, q ∈ Set.range (Int.cast : ℤ → ℚ) ↔
      ∃ w : Fin 292890231904 → ℚ, eval (Fin.cons q w) (map (Int.castRingHom ℚ) P) = 0

/-- The tower is Mathlib's `hyperoperation 4 2`. -/
theorem tw_eq_hyperoperation (r : ℕ) : tw r = hyperoperation 4 2 r := by
  induction r with
  | zero => exact (hyperoperation_ge_three_eq_one 1 2).symm
  | succ r ih =>
    rw [tw_succ, ih]
    have h := hyperoperation_recursion 3 2 r
    rw [hyperoperation_three] at h
    exact h.symm

theorem abs_lt_natCast_iff (c : ℤ) (N : ℕ) : |c| < (N : ℤ) ↔ c.natAbs < N := by
  rw [← Int.natCast_natAbs, Nat.cast_lt]

/-- **Theorem 1.1 as printed is equivalent to `ZInQ.FrozenTarget`**, in both directions. -/
theorem theorem11_iff_frozenTarget : Theorem11 ↔ FrozenTarget := by
  unfold Theorem11 FrozenTarget
  simp only [tw_eq_hyperoperation, abs_lt_natCast_iff, Set.mem_range, eval_map]
  constructor
  · rintro ⟨P, hd, hc, hq⟩
    exact ⟨P, hd, hc, fun q => (hq q).symm⟩
  · rintro ⟨P, hd, hc, hq⟩
    exact ⟨P, hd, hc, fun q => (hq q).symm⟩

theorem frozenTarget_of_theorem11 (h : Theorem11) : FrozenTarget := theorem11_iff_frozenTarget.mp h

theorem theorem11_of_frozenTarget (h : FrozenTarget) : Theorem11 := theorem11_iff_frozenTarget.mpr h

end ZInQ.PrintedTheorem11
