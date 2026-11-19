import Lean

/-!
Minimal source-coupling proof adapted from the Rule 110 / powerful-triple method.
This does not change an existing DZQ theorem. A real arithmetic consumer must
supply the source type and the two observations.
-/

namespace Research.StrategyTransfer

universe u v w
variable {S : Type u} {A : Type v} {B : Type w}

/-- Two observations from one common source witness. -/
def Coupled (a : S → A) (b : S → B) (p : A × B) : Prop :=
  ∃ s : S, a s = p.1 ∧ b s = p.2

/-- Each observation is individually realizable, possibly by different sources. -/
def Marginal (a : S → A) (b : S → B) (p : A × B) : Prop :=
  (∃ s : S, a s = p.1) ∧ (∃ s : S, b s = p.2)

/-- One common source implies both marginal existence statements. -/
theorem coupled_implies_marginal (a : S → A) (b : S → B) (p : A × B)
    (h : Coupled a b p) : Marginal a b p := by
  obtain ⟨s, ha, hb⟩ := h
  exact ⟨⟨s, ha⟩, ⟨s, hb⟩⟩

theorem coupled_of_common_source (a : S → A) (b : S → B) (s : S) :
    Coupled a b (a s, b s) := by
  exact ⟨s, rfl, rfl⟩

/-- Both marginals contain true even though they require different witnesses. -/
theorem bool_marginal :
    Marginal (fun s : Bool => s) (fun s : Bool => !s) (true, true) := by
  exact ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩

/-- Independently realizable does not imply jointly realizable. -/
theorem bool_not_coupled :
    ¬ Coupled (fun s : Bool => s) (fun s : Bool => !s) (true, true) := by
  intro h
  obtain ⟨s, ha, hb⟩ := h
  cases s with
  | false => cases ha
  | true => cases hb

end Research.StrategyTransfer

#print axioms Research.StrategyTransfer.coupled_implies_marginal
#print axioms Research.StrategyTransfer.coupled_of_common_source
#print axioms Research.StrategyTransfer.bool_marginal
#print axioms Research.StrategyTransfer.bool_not_coupled
