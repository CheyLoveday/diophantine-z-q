/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ZInQ.CircuitEncoding
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Polynomial equations for typed rational circuits

The three literal polynomial definitions and four proofs are the reviewed
circuit-polynomial-author-001 result. Inputs and gate values use disjoint
finite blocks. The selected output can be any actual gate. This module proves
typed rational-circuit reification; it does not verify a JavaScript parser,
call expansion, integer semantics, or the complete Diophantine compiler.
-/

@[expose] public section

namespace ZInQ.CircuitEncoding

noncomputable section

/-- The polynomial for one gate's right-hand side, before adding its output variable. -/
def Gate.rhsPolynomial {inputCount available : Nat} :
    Gate Rat inputCount available ->
      MvPolynomial (Fin (inputCount + available)) Rat
  | .input index => MvPolynomial.X (Fin.castAdd available index)
  | .constant value => MvPolynomial.C value
  | .add left right =>
      MvPolynomial.X (Fin.natAdd inputCount left) +
        MvPolynomial.X (Fin.natAdd inputCount right)
  | .mul left right =>
      MvPolynomial.X (Fin.natAdd inputCount left) *
        MvPolynomial.X (Fin.natAdd inputCount right)

/-- One residual per gate: output variable minus the gate's right-hand side.
Extending a circuit appends a variable and preserves every earlier variable index. -/
def Circuit.residualPolynomials {inputCount : Nat} :
    {gateCount : Nat} -> Circuit Rat inputCount gateCount ->
      Fin gateCount -> MvPolynomial (Fin (inputCount + gateCount)) Rat
  | 0, .empty => Fin.elim0
  | n + 1, .snoc previous gate =>
      Fin.lastCases
        (MvPolynomial.X (Fin.last (inputCount + n)) -
          MvPolynomial.rename
            (fun j : Fin (inputCount + n) => j.castSucc)
            (Gate.rhsPolynomial gate))
        (fun i => MvPolynomial.rename
          (fun j : Fin (inputCount + n) => j.castSucc)
          (Circuit.residualPolynomials previous i))

/-- A single polynomial imposing every gate equation and a zero selected output.
An actual `Fin gateCount` output is required; no output is invented for an empty circuit. -/
def Circuit.zeroOutputPolynomial {inputCount gateCount : Nat}
    (circuit : Circuit Rat inputCount gateCount) (output : Fin gateCount) :
    MvPolynomial (Fin (inputCount + gateCount)) Rat :=
  (MvPolynomial.X (Fin.natAdd inputCount output)) ^ 2 +
    Finset.univ.sum (fun i : Fin gateCount =>
      (Circuit.residualPolynomials circuit i) ^ 2)

end

end ZInQ.CircuitEncoding

public section

namespace ZInQ.CircuitEncoding

theorem Gate.eval_rhs_polynomial {inputCount available : Nat}
    (gate : Gate Rat inputCount available)
    (inputs : Fin inputCount -> Rat) (values : Fin available -> Rat) :
    MvPolynomial.eval (Fin.append inputs values) (Gate.rhsPolynomial gate) =
      Gate.eval (fun x y : Rat => x + y) (fun x y : Rat => x * y)
        inputs values gate := by
  cases gate with
  | input index =>
    rw [Gate.rhsPolynomial, MvPolynomial.eval_X, Fin.append_left]
    rfl
  | constant value =>
    rw [Gate.rhsPolynomial, MvPolynomial.eval_C]
    rfl
  | add left right =>
    rw [Gate.rhsPolynomial, map_add, MvPolynomial.eval_X, MvPolynomial.eval_X,
      Fin.append_right, Fin.append_right]
    rfl
  | mul left right =>
    rw [Gate.rhsPolynomial, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X,
      Fin.append_right, Fin.append_right]
    rfl

/-- Restricting the joint valuation of an extended circuit along `Fin.castSucc`
gives the joint valuation of the prefix circuit. -/
private theorem append_comp_castSucc {inputCount n : Nat}
    (inputs : Fin inputCount → Rat) (values : Fin (n + 1) → Rat) :
    (Fin.append inputs values ∘ fun j : Fin (inputCount + n) => j.castSucc) =
      Fin.append inputs (fun i : Fin n => values i.castSucc) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have hidx : ((Fin.castAdd n i).castSucc : Fin (inputCount + (n + 1))) =
        Fin.castAdd (n + 1) i := Fin.ext rfl
    rw [Function.comp_apply, hidx, Fin.append_left, Fin.append_left]
  · have hidx : ((Fin.natAdd inputCount i).castSucc : Fin (inputCount + (n + 1))) =
        Fin.natAdd inputCount i.castSucc := Fin.ext rfl
    rw [Function.comp_apply, hidx, Fin.append_right, Fin.append_right]

/-- The last variable of an extended circuit is the variable of its last gate. -/
private theorem append_last {inputCount n : Nat}
    (inputs : Fin inputCount → Rat) (values : Fin (n + 1) → Rat) :
    Fin.append inputs values (Fin.last (inputCount + n)) = values (Fin.last n) := by
  have hidx : (Fin.last (inputCount + n) : Fin (inputCount + (n + 1))) =
      Fin.natAdd inputCount (Fin.last n) := Fin.ext rfl
  rw [hidx, Fin.append_right]

/-- Evaluating an earlier residual of an extended circuit: the renamed residual sees
exactly the prefix valuation. -/
private theorem eval_residual_snoc_castSucc {inputCount n : Nat}
    (previous : Circuit Rat inputCount n) (gate : Gate Rat inputCount n)
    (inputs : Fin inputCount → Rat) (values : Fin (n + 1) → Rat) (i : Fin n) :
    MvPolynomial.eval (Fin.append inputs values)
        (Circuit.residualPolynomials (Circuit.snoc previous gate) i.castSucc) =
      MvPolynomial.eval (Fin.append inputs (fun j : Fin n => values j.castSucc))
        (Circuit.residualPolynomials previous i) := by
  rw [Circuit.residualPolynomials]
  dsimp only
  rw [Fin.lastCases_castSucc]
  refine (MvPolynomial.eval_rename _ _ _).trans ?_
  exact congrArg (fun g => MvPolynomial.eval g (Circuit.residualPolynomials previous i))
    (append_comp_castSucc inputs values)

/-- Evaluating the residual of the last gate of an extended circuit. -/
private theorem eval_residual_snoc_last {inputCount n : Nat}
    (previous : Circuit Rat inputCount n) (gate : Gate Rat inputCount n)
    (inputs : Fin inputCount → Rat) (values : Fin (n + 1) → Rat) :
    MvPolynomial.eval (Fin.append inputs values)
        (Circuit.residualPolynomials (Circuit.snoc previous gate) (Fin.last n)) =
      values (Fin.last n) -
        Gate.eval (fun x y : Rat => x + y) (fun x y : Rat => x * y) inputs
          (fun j : Fin n => values j.castSucc) gate := by
  rw [Circuit.residualPolynomials]
  dsimp only
  rw [Fin.lastCases_last, map_sub, MvPolynomial.eval_X, append_last,
    ← Gate.eval_rhs_polynomial gate inputs (fun j : Fin n => values j.castSucc)]
  congr 1
  refine (MvPolynomial.eval_rename _ _ _).trans ?_
  exact congrArg (fun g => MvPolynomial.eval g (Gate.rhsPolynomial gate))
    (append_comp_castSucc inputs values)

theorem Circuit.eval_residual_polynomials_eq_zero_iff {inputCount gateCount : Nat}
    (circuit : Circuit Rat inputCount gateCount)
    (inputs : Fin inputCount -> Rat) (values : Fin gateCount -> Rat) :
    (∀ i : Fin gateCount,
      MvPolynomial.eval (Fin.append inputs values)
        (Circuit.residualPolynomials circuit i) = 0) ↔
      Circuit.satisfies (fun x y : Rat => x + y) (fun x y : Rat => x * y)
        inputs circuit values := by
  -- `values` depends on the circuit index, so `induction` generalizes it automatically.
  induction circuit with
  | empty =>
    exact ⟨fun _ => True.intro, fun _ i => Fin.elim0 i⟩
  | @snoc n previous gate ih =>
    rw [Circuit.satisfies, ← ih (fun i : Fin n => values i.castSucc)]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · rw [← eval_residual_snoc_castSucc previous gate inputs values i]
        exact h i.castSucc
      · rw [← sub_eq_zero, ← eval_residual_snoc_last previous gate inputs values]
        exact h (Fin.last n)
    · rintro ⟨hprev, hlast⟩ i
      induction i using Fin.lastCases with
      | last =>
        rw [eval_residual_snoc_last previous gate inputs values, sub_eq_zero]
        exact hlast
      | cast j =>
        rw [eval_residual_snoc_castSucc previous gate inputs values j]
        exact hprev j

theorem Circuit.eval_zero_output_polynomial_eq_zero_iff {inputCount gateCount : Nat}
    (circuit : Circuit Rat inputCount gateCount) (output : Fin gateCount)
    (inputs : Fin inputCount -> Rat) (values : Fin gateCount -> Rat) :
    MvPolynomial.eval (Fin.append inputs values)
      (Circuit.zeroOutputPolynomial circuit output) = 0 ↔
      (Circuit.satisfies (fun x y : Rat => x + y) (fun x y : Rat => x * y)
        inputs circuit values ∧ values output = 0) := by
  rw [← Circuit.eval_residual_polynomials_eq_zero_iff circuit inputs values,
    Circuit.zeroOutputPolynomial, map_add, map_pow, MvPolynomial.eval_X, Fin.append_right,
    map_sum]
  simp only [map_pow]
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    pow_eq_zero_iff two_ne_zero, Finset.sum_sq_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies]
  exact and_comm

theorem Circuit.exists_zero_output_polynomial_eq_zero_iff {inputCount gateCount : Nat}
    (circuit : Circuit Rat inputCount gateCount) (output : Fin gateCount)
    (inputs : Fin inputCount -> Rat) :
    (∃ values : Fin gateCount -> Rat,
      MvPolynomial.eval (Fin.append inputs values)
        (Circuit.zeroOutputPolynomial circuit output) = 0) ↔
      Circuit.eval (fun x y : Rat => x + y) (fun x y : Rat => x * y)
        inputs circuit output = 0 := by
  refine Iff.trans ?_
    (Circuit.exists_output_iff (fun x y : Rat => x + y) (fun x y : Rat => x * y)
      inputs circuit output 0)
  exact exists_congr fun values =>
    Circuit.eval_zero_output_polynomial_eq_zero_iff circuit output inputs values

end ZInQ.CircuitEncoding
