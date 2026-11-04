module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Order.Ring.Rat

/-!
# Finite rational equation compression and coefficient clearing

This module formalizes the algebraic core of compiling a finite positive
combination of rational polynomial equations into a single polynomial equation,
and then clearing rational coefficients to obtain an integer-coefficient
polynomial with the same rational zero set.

* `conjoin` encodes an `n`-ary conjunction as a sum of squares and `disjoin`
  encodes an `n`-ary disjunction as a product. The empty conjunction is the
  zero polynomial (always true) and the empty disjunction is the polynomial `1`
  (always false).
* `compile` is a recursive compiler for binary formulas, with truth represented
  by the value `0` and falsehood by the value `1`.
* `leftVars` and `rightVars` embed two private witness blocks into a common
  variable type, so that branch witnesses are never shared accidentally.
* `commonDenominator` is the product of the denominators of all coefficients
  in the support; multiplying by it clears all denominators.

The supplied definitions appear below byte-for-byte as specified; their
docstrings are attached afterwards with `add_decl_doc`.

## Main results

* `eval_conjoin_eq_zero_iff`, `eval_disjoin_eq_zero_iff`
* `eval_compile_eq_zero_iff`
* `exists_conjunction_fresh_iff`, `exists_disjunction_fresh_iff`
* `commonDenominator_pos`, `exists_integer_multiple`
* `exists_integer_equation`

This is not DPRM and does not prove anything about a concrete parser; the
formula syntax starts from already-formed polynomial equations.
-/

public section

noncomputable section

namespace ZInQ.EquationCompression

inductive EquationFormula (n : Nat) where
  | equation : MvPolynomial (Fin n) Rat → EquationFormula n
  | verum : EquationFormula n
  | falsum : EquationFormula n
  | conj : EquationFormula n → EquationFormula n → EquationFormula n
  | disj : EquationFormula n → EquationFormula n → EquationFormula n

@[expose] def holds {n : Nat} (x : Fin n → Rat) : EquationFormula n → Prop
  | .equation P => MvPolynomial.eval x P = 0
  | .verum => True
  | .falsum => False
  | .conj F G => holds x F ∧ holds x G
  | .disj F G => holds x F ∨ holds x G

@[expose] def compile {n : Nat} : EquationFormula n → MvPolynomial (Fin n) Rat
  | .equation P => P
  | .verum => 0
  | .falsum => 1
  | .conj F G => compile F ^ 2 + compile G ^ 2
  | .disj F G => compile F * compile G

@[expose] def leftVars {n m k : Nat} :
    Sum (Fin n) (Fin m) → Sum (Fin n) (Sum (Fin m) (Fin k))
  | .inl i => .inl i
  | .inr j => .inr (.inl j)

@[expose] def rightVars {n m k : Nat} :
    Sum (Fin n) (Fin k) → Sum (Fin n) (Sum (Fin m) (Fin k))
  | .inl i => .inl i
  | .inr j => .inr (.inr j)

@[expose] def commonDenominator {n : Nat}
    (P : MvPolynomial (Fin n) Rat) : Nat :=
  P.support.prod (fun d => (P.coeff d).den)

@[expose] def conjoin {n : Nat}
    (ps : List (MvPolynomial (Fin n) Rat)) : MvPolynomial (Fin n) Rat :=
  (ps.map (fun P => P ^ 2)).sum

@[expose] def disjoin {n : Nat}
    (ps : List (MvPolynomial (Fin n) Rat)) : MvPolynomial (Fin n) Rat :=
  ps.prod

/-- Finite positive formulas whose atoms are rational polynomial equations. -/
add_decl_doc EquationFormula

/-- Truth of a formula at a rational point. -/
add_decl_doc holds

/-- Compile a formula to a single rational polynomial; truth is the value `0`,
`verum` compiles to `0` and `falsum` compiles to `1`. -/
add_decl_doc compile

/-- Embed the left branch variables (shared block plus left witness block). -/
add_decl_doc leftVars

/-- Embed the right branch variables (shared block plus right witness block). -/
add_decl_doc rightVars

/-- The product of the denominators of all coefficients in the support. -/
add_decl_doc commonDenominator

/-- `n`-ary conjunction as a sum of squares; the empty conjunction is `0`. -/
add_decl_doc conjoin

/-- `n`-ary disjunction as a product; the empty disjunction is `1`. -/
add_decl_doc disjoin

/-! ### List operations -/

/-- Helper: a sum of squares evaluates to a nonnegative rational. -/
theorem eval_conjoin_nonneg {n : Nat}
    (ps : List (MvPolynomial (Fin n) Rat)) (x : Fin n → Rat) :
    0 ≤ MvPolynomial.eval x (conjoin ps) := by
  induction ps with
  | nil => simp [conjoin]
  | cons P ps ih =>
    simp only [conjoin, List.map_cons, List.sum_cons, map_add, map_pow] at ih ⊢
    exact add_nonneg (sq_nonneg _) ih

theorem eval_conjoin_eq_zero_iff {n : Nat}
    (ps : List (MvPolynomial (Fin n) Rat)) (x : Fin n → Rat) :
    MvPolynomial.eval x (conjoin ps) = 0 ↔
      ∀ P ∈ ps, MvPolynomial.eval x P = 0 := by
  induction ps with
  | nil => simp [conjoin]
  | cons P ps ih =>
    have hnn := eval_conjoin_nonneg ps x
    simp only [conjoin, List.map_cons, List.sum_cons, map_add, map_pow] at ih hnn ⊢
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) hnn, pow_eq_zero_iff two_ne_zero, ih,
      List.forall_mem_cons]

theorem eval_disjoin_eq_zero_iff {n : Nat}
    (ps : List (MvPolynomial (Fin n) Rat)) (x : Fin n → Rat) :
    MvPolynomial.eval x (disjoin ps) = 0 ↔
      ∃ P ∈ ps, MvPolynomial.eval x P = 0 := by
  induction ps with
  | nil => simp [disjoin]
  | cons P ps ih =>
    simp only [disjoin, List.prod_cons, map_mul] at ih ⊢
    rw [mul_eq_zero, ih]
    constructor
    · rintro (h | ⟨Q, hQ, h⟩)
      · exact ⟨P, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact ⟨Q, List.mem_cons.mpr (Or.inr hQ), h⟩
    · rintro ⟨Q, hQ, h⟩
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact Or.inl h
      · exact Or.inr ⟨Q, hQ, h⟩

/-! ### The recursive formula compiler -/

theorem eval_compile_eq_zero_iff {n : Nat}
    (F : EquationFormula n) (x : Fin n → Rat) :
    MvPolynomial.eval x (compile F) = 0 ↔ holds x F := by
  induction F with
  | equation P => simp [compile, holds]
  | verum => simp [compile, holds]
  | falsum => simp [compile, holds]
  | conj F G ihF ihG =>
    simp only [compile, holds, map_add, map_pow]
    rw [sq_add_sq_eq_zero, ihF, ihG]
  | disj F G ihF ihG =>
    simp only [compile, holds, map_mul]
    rw [mul_eq_zero, ihF, ihG]

/-! ### Fresh witness blocks -/

/-- Helper: evaluating after `leftVars` only reads the left witness block. -/
theorem sum_elim_comp_leftVars {n m k : Nat} (x : Fin n → Rat)
    (yz : Sum (Fin m) (Fin k) → Rat) :
    Sum.elim x yz ∘ leftVars (n := n) (m := m) (k := k) = Sum.elim x (yz ∘ Sum.inl) := by
  funext i
  cases i <;> rfl

/-- Helper: evaluating after `rightVars` only reads the right witness block. -/
theorem sum_elim_comp_rightVars {n m k : Nat} (x : Fin n → Rat)
    (yz : Sum (Fin m) (Fin k) → Rat) :
    Sum.elim x yz ∘ rightVars (n := n) (m := m) (k := k) = Sum.elim x (yz ∘ Sum.inr) := by
  funext i
  cases i <;> rfl

theorem exists_conjunction_fresh_iff {n m k : Nat}
    (P : MvPolynomial (Sum (Fin n) (Fin m)) Rat)
    (Q : MvPolynomial (Sum (Fin n) (Fin k)) Rat)
    (x : Fin n → Rat) :
    (∃ yz : Sum (Fin m) (Fin k) → Rat,
      MvPolynomial.eval (Sum.elim x yz)
        ((MvPolynomial.rename (leftVars (n := n) (m := m) (k := k)) P) ^ 2 +
         (MvPolynomial.rename (rightVars (n := n) (m := m) (k := k)) Q) ^ 2) = 0)
    ↔
    ((∃ y : Fin m → Rat, MvPolynomial.eval (Sum.elim x y) P = 0) ∧
     (∃ z : Fin k → Rat, MvPolynomial.eval (Sum.elim x z) Q = 0)) := by
  simp only [map_add, map_pow, MvPolynomial.eval_rename, sum_elim_comp_leftVars,
    sum_elim_comp_rightVars, sq_add_sq_eq_zero]
  constructor
  · rintro ⟨yz, hP, hQ⟩
    exact ⟨⟨yz ∘ Sum.inl, hP⟩, ⟨yz ∘ Sum.inr, hQ⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    refine ⟨Sum.elim y z, ?_, ?_⟩
    · rw [Sum.elim_comp_inl]
      exact hy
    · rw [Sum.elim_comp_inr]
      exact hz

theorem exists_disjunction_fresh_iff {n m k : Nat}
    (P : MvPolynomial (Sum (Fin n) (Fin m)) Rat)
    (Q : MvPolynomial (Sum (Fin n) (Fin k)) Rat)
    (x : Fin n → Rat) :
    (∃ yz : Sum (Fin m) (Fin k) → Rat,
      MvPolynomial.eval (Sum.elim x yz)
        (MvPolynomial.rename (leftVars (n := n) (m := m) (k := k)) P *
         MvPolynomial.rename (rightVars (n := n) (m := m) (k := k)) Q) = 0)
    ↔
    ((∃ y : Fin m → Rat, MvPolynomial.eval (Sum.elim x y) P = 0) ∨
     (∃ z : Fin k → Rat, MvPolynomial.eval (Sum.elim x z) Q = 0)) := by
  simp only [map_mul, MvPolynomial.eval_rename, sum_elim_comp_leftVars,
    sum_elim_comp_rightVars, mul_eq_zero]
  constructor
  · rintro ⟨yz, hP | hQ⟩
    · exact Or.inl ⟨yz ∘ Sum.inl, hP⟩
    · exact Or.inr ⟨yz ∘ Sum.inr, hQ⟩
  · rintro (⟨y, hy⟩ | ⟨z, hz⟩)
    · -- the inactive right witness block is arbitrary (here constantly zero)
      refine ⟨Sum.elim y (fun _ => 0), Or.inl ?_⟩
      rw [Sum.elim_comp_inl]
      exact hy
    · -- the inactive left witness block is arbitrary (here constantly zero)
      refine ⟨Sum.elim (fun _ => 0) z, Or.inr ?_⟩
      rw [Sum.elim_comp_inr]
      exact hz

/-! ### Coefficient clearing -/

theorem commonDenominator_pos {n : Nat}
    (P : MvPolynomial (Fin n) Rat) :
    0 < commonDenominator P := by
  unfold commonDenominator
  exact Finset.prod_induction _ (fun d => 0 < d) (fun _ _ ha hb => Nat.mul_pos ha hb)
    Nat.one_pos (fun d _ => (P.coeff d).den_pos)

/-- Helper: each coefficient times the common denominator is an integer. -/
theorem exists_int_eq_commonDenominator_mul_coeff {n : Nat}
    (P : MvPolynomial (Fin n) Rat) (d : Fin n →₀ ℕ) :
    ∃ z : Int, (z : Rat) = (commonDenominator P : Rat) * P.coeff d := by
  by_cases hd : d ∈ P.support
  · obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun d => (P.coeff d).den) hd
    have hcd : commonDenominator P = (P.coeff d).den * e := he
    refine ⟨(e : Int) * (P.coeff d).num, ?_⟩
    rw [hcd, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, mul_comm ((P.coeff d).den : Rat),
      mul_assoc, Rat.den_mul_eq_num]
  · refine ⟨0, ?_⟩
    rw [MvPolynomial.notMem_support_iff.mp hd, mul_zero, Int.cast_zero]

theorem exists_integer_multiple {n : Nat}
    (P : MvPolynomial (Fin n) Rat) :
    ∃ Q : MvPolynomial (Fin n) Int,
      MvPolynomial.map (Int.castRingHom Rat) Q =
        MvPolynomial.C (commonDenominator P : Rat) * P := by
  have h : MvPolynomial.C (commonDenominator P : Rat) * P ∈
      Set.range (MvPolynomial.map (σ := Fin n) (Int.castRingHom Rat)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    rw [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hc
    obtain ⟨d, -, rfl⟩ := hc
    obtain ⟨z, hz⟩ := exists_int_eq_commonDenominator_mul_coeff P d
    exact ⟨z, by rw [MvPolynomial.coeff_C_mul, ← hz, Int.coe_castRingHom]⟩
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q, hQ⟩

theorem exists_integer_equation {n : Nat} (F : EquationFormula n) :
    ∃ Q : MvPolynomial (Fin n) Int,
      ∀ x : Fin n → Rat,
        (MvPolynomial.eval₂ (Int.castRingHom Rat) x Q = 0 ↔ holds x F) := by
  obtain ⟨Q, hQ⟩ := exists_integer_multiple (compile F)
  have hne : (commonDenominator (compile F) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (commonDenominator_pos (compile F)).ne'
  refine ⟨Q, fun x => ?_⟩
  rw [← MvPolynomial.eval_map, hQ, map_mul, MvPolynomial.eval_C, mul_eq_zero,
    eval_compile_eq_zero_iff]
  exact or_iff_right hne

end ZInQ.EquationCompression
