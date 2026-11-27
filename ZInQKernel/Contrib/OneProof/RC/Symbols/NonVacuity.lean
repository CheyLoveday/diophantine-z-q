import ZInQKernel.Contrib.OneProof.RC.Symbols.Witness
import ZInQKernel.Contrib.OneProof.RC.Symbols.Address

/-!
# Lane RC2: the address lemmas apply to an actual symbol (non-vacuity)

The forest-weight symbol of `Witness.lean` satisfies the coefficient rules and the terminal
hypotheses; the address lemmas therefore have instances. This is a consistency check, not part of
the manuscript.
-/

namespace ZInQ.Manuscript.RC.Symbols

/-- **Non-vacuity of `one_symbol_address`** (tex 2222–2238). Kind: PROVED. There are a symbol
satisfying the coefficient rules and a nonempty stationary list with nonzero terminal polynomial,
so the lemma applies for every `b ≥ 1`. -/
theorem one_symbol_address_nonvacuous (b : ℕ) (hb : 1 ≤ b) :
    ∃ (A : Config (ZMod 2) → ZMod 2) (Γ : Config (ZMod 2)),
      CoefficientRules 0 A ∧ Γ.Compatible 0 ∧ Γ.V.Nonempty ∧ TerminalNonzero A Γ ∧
      AddressConclusion 0 ![A, A] Γ (fun _ => (none : Option (Fin b → ZMod 2))) := by
  obtain ⟨A, Γ, hA, hΓ, hne, hT⟩ := witness_one_symbol
  exact ⟨A, Γ, hA, hΓ, hne, hT, one_symbol_address hA Γ hΓ hne hT b hb⟩

/-- **Non-vacuity of `two_symbol_address`** (tex 2240–2258). Kind: PROVED. There are a symbol
satisfying the coefficient rules and a configuration of terminals with nonzero linear
activations, one of every activation, with nonzero terminal polynomials at every nonzero
address, so the lemma applies for every `b ≥ 1`. -/
theorem two_symbol_address_nonvacuous (b : ℕ) (hb : 1 ≤ b) :
    ∃ (A : Config (ZMod 2) → ZMod 2) (Γ : Config (ZMod 2)) (act' : ℕ → Option (Fin b → ZMod 2)),
      CoefficientRules 0 A ∧ Γ.Compatible 0 ∧ (∀ v ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' v = some w) ∧
      (∀ w : Fin b → ZMod 2, w ≠ 0 → ∃ v ∈ Γ.V, act' v = some w) ∧
      (∀ x : Fin b → ZMod 2, x ≠ 0 → TerminalNonzero A (Γ.at act' x)) ∧
      AddressConclusion 0 ![A, A] Γ act' := by
  obtain ⟨A, Γ, act', hA, hΓ, hact, hall, hT⟩ := witness_two_symbol b hb
  exact ⟨A, Γ, act', hA, hΓ, hact, hall, hT,
    two_symbol_address hA hA b hb Γ hΓ act' hact hall hT hT⟩

end ZInQ.Manuscript.RC.Symbols
