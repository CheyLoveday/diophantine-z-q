module

public import Init.Data.Fin.Lemmas

/-!
# Acyclic circuit evaluation and gate equations

A gate can use external inputs, constants, and earlier gate values. The local
constraints on a proposed valuation hold exactly when it equals the computed
valuation. Consequently, existential gate witnesses preserve a chosen output.

The carrier and its two operations are arbitrary. This module proves the
abstract circuit semantics; it does not identify a concrete compiler's output
with these circuits or prove a polynomial conversion.
-/

public section

universe u

namespace ZInQ.CircuitEncoding

/-- One gate, with operands restricted to the `available` earlier gates. -/
inductive Gate (α : Type u) (inputCount available : Nat) : Type u where
  | input (index : Fin inputCount)
  | constant (value : α)
  | add (left right : Fin available)
  | mul (left right : Fin available)

/-- An acyclic circuit, indexed by its number of gates. -/
inductive Circuit (α : Type u) (inputCount : Nat) : Nat → Type u where
  | empty : Circuit α inputCount 0
  | snoc {gateCount : Nat} (previous : Circuit α inputCount gateCount)
      (gate : Gate α inputCount gateCount) : Circuit α inputCount (gateCount + 1)

/-- Evaluate one gate using the supplied inputs and earlier gate values. -/
@[expose] def Gate.eval {α : Type u} {inputCount available : Nat}
    (addOp mulOp : α → α → α) (inputs : Fin inputCount → α)
    (values : Fin available → α) : Gate α inputCount available → α
  | .input index => inputs index
  | .constant value => value
  | .add left right => addOp (values left) (values right)
  | .mul left right => mulOp (values left) (values right)

/-- Compute the valuation of all gates in circuit order. -/
@[expose] def Circuit.eval {α : Type u} {inputCount : Nat}
    (addOp mulOp : α → α → α) (inputs : Fin inputCount → α) :
    {gateCount : Nat} → Circuit α inputCount gateCount → (Fin gateCount → α)
  | _, .empty => Fin.elim0
  | _, .snoc previous gate =>
    let values := Circuit.eval addOp mulOp inputs previous
    Fin.lastCases (Gate.eval addOp mulOp inputs values gate) values

/-- Local gate equations for a supplied valuation of the entire circuit. -/
@[expose] def Circuit.satisfies {α : Type u} {inputCount : Nat}
    (addOp mulOp : α → α → α) (inputs : Fin inputCount → α) :
    {gateCount : Nat} → Circuit α inputCount gateCount → (Fin gateCount → α) → Prop
  | _, .empty, _ => True
  | _, .snoc previous gate, values =>
    Circuit.satisfies addOp mulOp inputs previous (fun i => values i.castSucc) ∧
      values (Fin.last _) =
        Gate.eval addOp mulOp inputs (fun i => values i.castSucc) gate

end ZInQ.CircuitEncoding

namespace ZInQ.CircuitEncoding.Circuit

variable {α : Type u} {inputCount gateCount : Nat}
variable (addOp mulOp : α → α → α) (inputs : Fin inputCount → α)

/-- On an earlier gate index, the evaluation of an extended circuit agrees with the
evaluation of the prefix circuit. -/
private theorem eval_snoc_castSucc {n : Nat} (previous : Circuit α inputCount n)
    (gate : Gate α inputCount n) (i : Fin n) :
    eval addOp mulOp inputs (Circuit.snoc previous gate) i.castSucc =
      eval addOp mulOp inputs previous i := by
  simp only [eval, Fin.lastCases_castSucc]

/-- The last coordinate of the evaluation of an extended circuit is the value of the
last gate computed from the evaluation of the prefix circuit. -/
private theorem eval_snoc_last {n : Nat} (previous : Circuit α inputCount n)
    (gate : Gate α inputCount n) :
    eval addOp mulOp inputs (Circuit.snoc previous gate) (Fin.last n) =
      Gate.eval addOp mulOp inputs (eval addOp mulOp inputs previous) gate := by
  simp only [eval, Fin.lastCases_last]

theorem eval_satisfies (c : Circuit α inputCount gateCount) :
    satisfies addOp mulOp inputs c (eval addOp mulOp inputs c) := by
  induction c with
  | empty => exact True.intro
  | @snoc n previous gate ih =>
    have hprefix :
        (fun i : Fin n => eval addOp mulOp inputs (Circuit.snoc previous gate) i.castSucc) =
          eval addOp mulOp inputs previous :=
      funext (eval_snoc_castSucc addOp mulOp inputs previous gate)
    rw [satisfies, hprefix, eval_snoc_last]
    exact ⟨ih, rfl⟩

/-- Forward direction of `satisfies_iff_eq_eval`, by induction on the circuit with the
proposed valuation allowed to vary. -/
private theorem eq_eval_of_satisfies (c : Circuit α inputCount gateCount) :
    ∀ values : Fin gateCount → α,
      satisfies addOp mulOp inputs c values → values = eval addOp mulOp inputs c := by
  induction c with
  | empty =>
    intro values _
    funext i
    exact Fin.elim0 i
  | @snoc n previous gate ih =>
    intro values h
    rw [satisfies] at h
    obtain ⟨hprev, hlast⟩ := h
    have hprefix : (fun i : Fin n => values i.castSucc) = eval addOp mulOp inputs previous :=
      ih _ hprev
    funext i
    induction i using Fin.lastCases with
    | last =>
      rw [eval_snoc_last, hlast, hprefix]
    | cast j =>
      rw [eval_snoc_castSucc]
      exact congrFun hprefix j

theorem satisfies_iff_eq_eval (c : Circuit α inputCount gateCount)
    (values : Fin gateCount → α) :
    satisfies addOp mulOp inputs c values ↔ values = eval addOp mulOp inputs c := by
  constructor
  · exact eq_eval_of_satisfies addOp mulOp inputs c values
  · intro h
    rw [h]
    exact eval_satisfies addOp mulOp inputs c

theorem exists_unique_satisfies (c : Circuit α inputCount gateCount) :
    ∃ values : Fin gateCount → α,
      satisfies addOp mulOp inputs c values ∧
        ∀ other : Fin gateCount → α,
          satisfies addOp mulOp inputs c other → other = values := by
  refine ⟨eval addOp mulOp inputs c, eval_satisfies addOp mulOp inputs c, ?_⟩
  intro other h
  exact (satisfies_iff_eq_eval addOp mulOp inputs c other).mp h

theorem exists_output_iff (c : Circuit α inputCount gateCount)
    (output : Fin gateCount) (value : α) :
    (∃ values : Fin gateCount → α,
      satisfies addOp mulOp inputs c values ∧ values output = value) ↔
      eval addOp mulOp inputs c output = value := by
  constructor
  · intro h
    obtain ⟨values, hsat, hout⟩ := h
    rw [← (satisfies_iff_eq_eval addOp mulOp inputs c values).mp hsat]
    exact hout
  · intro h
    exact ⟨eval addOp mulOp inputs c, eval_satisfies addOp mulOp inputs c, h⟩

end ZInQ.CircuitEncoding.Circuit

end
