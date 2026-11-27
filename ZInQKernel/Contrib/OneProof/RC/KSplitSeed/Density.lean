import ZInQKernel.Contrib.OneProof.RC.EvenReading.DensityLeaf
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Constituents

/-! Source support and passage from finite constituent quotients to the
address density models. No common finite extension for all prime sets is used. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KSplitSeed

open Finset Filter AddressGenuine EvenReading Wiring PrintsArith
open ZInQ.Manuscript.RC.Even
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-- Match the label modulus to the full stationary coefficient support.
The reverse inclusion alone is the condition for transferring a good-prime
test to the source. Tex 9471–9483, 10292–10295. -/
theorem evenGood_iff {ℓ : ℕ} {W : WData ℓ} (D : LabelData W) {S : Finset ℕ}
    (hS : D.m₂.primeFactors = S) {q : ℕ} :
    D.T₂.Good q ↔ q.Prime ∧ q ∉ S := by
  change (q.Prime ∧ q.Coprime D.m₂) ↔ _
  rw [← hS]
  constructor
  · rintro ⟨hp, hc⟩
    exact ⟨hp, fun h => hp.coprime_iff_not_dvd.mp hc (Nat.dvd_of_mem_primeFactors h)⟩
  · rintro ⟨hp, hq⟩
    exact ⟨hp, hp.coprime_iff_not_dvd.mpr fun hd =>
      hq (Nat.mem_primeFactors.mpr ⟨hp, hd, D.m₂_pos.ne'⟩)⟩

/-- Good primes of the coordinated label modulus are good for the actual
half-integral eigenform, including its level after the source was selected. -/
theorem not_dvd_even_level {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    {C : CentralNormalization (Ecurve ℓ)} {hk : W.kfin < 0} {S : Finset ℕ}
    (G : GenuineEvenSource C hk S) (hS : S ⊆ D.m₂.primeFactors)
    {q : ℕ} (hq : D.T₂.Good q) : ¬ q ∣ G.P.N := by
  intro hd
  exact hq.1.coprime_iff_not_dvd.mp hq.2
    (Nat.dvd_of_mem_primeFactors (hS (G.P.hNS q hq.1 hd)))

section Quotient

variable {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R R' : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
variable {B : ℕ} {χ : GalQ →* Multiplicative L}

/-- A finite quotient and its inertia bound can be supplied separately for
each tested set. The bound is on the field of that quotient and then descends
to the subgroup which sees the reduced expansions (tex 9663–9668, 9745–9750).
Changing the indexing symbol uses equality only at the tested prime sets. -/
def densityOfFiniteFields (X : GaloisConstituentModel T R ap B χ) (hX : X.Inputs)
    (hR : ∀ V : Finset ℕ, (∀ q ∈ V, T.Good q) → V.card ≤ B → R' V = R V)
    (hfields : ∀ U : Finset ℕ, (∀ q ∈ U, T.Good q) → U.card + 1 ≤ B →
      ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧ E.fixingSubgroup ≤ X.N U ∧
        ∀ q : ℕ, T.Good q → q ∉ U → ∀ Q : Ideal Zbar, Q.IsMaximal →
          ((q : ℤ) : Zbar) ∈ Q → Q.inertia GalQ ≤ E.fixingSubgroup) :
    GaloisDensityModel T R' ap B χ := by
  let Y := X.toGaloisDensityModel hX
    (X.galNOpen_of_N fun U hU hB => by
      obtain ⟨E, hE, hN, _⟩ := hfields U hU hB
      exact ⟨E, hE, hN⟩)
    (by
      intro U hU hB
      obtain ⟨E, _, hN, hI⟩ := hfields U hU hB
      refine ⟨∅, fun q hq hqU _ Q hQ hqQ => ?_⟩
      rw [X.galN_eq_N U hU hB]
      exact (hI q hq hqU Q hQ hqQ).trans hN)
  exact {
    M := Y.M
    instM := Y.instM
    instMod := Y.instMod
    t := Y.t
    d := Y.d
    F := Y.F
    read := Y.read
    frob := Y.frob
    frob_spec := Y.frob_spec
    trace_mul := Y.trace_mul
    det_orbit := Y.det_orbit
    two_fresh := Y.two_fresh
    trace_one := Y.trace_one
    t_class := Y.t_class
    kummer := Y.kummer
    isOpen := Y.isOpen
    unramified := Y.unramified
    reading := fun U q hU hq hqU hB => by
      rw [hR (insert q U) (fun p hp => by
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact hq
        · exact hU p hp) hB]
      exact Y.reading U q hU hq hqU hB
    o12 := Y.o12 }

end Quotient

/-- Even density models use the same reading at every budget. Tex
9450–9455, 10288–10318. The selected source is an explicit argument. -/
theorem evenDensityModels_of_constituent_fields {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    {C : CentralNormalization (Ecurve ℓ)} {hk : W.kfin < 0} {S : Finset ℕ}
    (G : GenuineEvenSource C hk S)
    (h : ∀ B : ℕ, ∃ X : GaloisConstituentModel D.T₂ (RevGen S G.r) (apk W) B (typChar D.m₂),
      X.Inputs ∧ ∀ U : Finset ℕ, (∀ q ∈ U, D.T₂.Good q) → U.card + 1 ≤ B →
        ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧ E.fixingSubgroup ≤ X.N U ∧
          ∀ q : ℕ, D.T₂.Good q → q ∉ U → ∀ Q : Ideal Zbar, Q.IsMaximal →
            ((q : ℤ) : Zbar) ∈ Q → Q.inertia GalQ ≤ E.fixingSubgroup) :
    EvenDensityModels W D (RevGen S G.r) := by
  intro B
  obtain ⟨X, hX, hF⟩ := h B
  exact ⟨densityOfFiniteFields X hX (fun _ _ _ => rfl) hF⟩

/-- Transfer the genuine odd constituent readings on each eventual set of
valid stages. The agreement hypothesis can use `O12StageVal.rodd_eq_intrinsic`.
The lifting and finite fields are required only at the chosen cutoff.
Tex 10208–10255, 10533–10548. -/
theorem oddDensityModels_of_stage_fields {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    (stageRead : ℕ → Finset ℕ → ZMod 2)
    (hR : ∀ θ U, (∀ q ∈ U, q.Prime) → Rodd W D θ U = stageRead θ U)
    (h : ∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ),
      ∃ X : GaloisConstituentModel (D.T₁ θ) (stageRead θ) (apo ℓ) (Wc + 1)
        (stageChar D.m₁ (D.ℓ₀ θ)),
        X.Inputs ∧ ∀ U : Finset ℕ, (∀ q ∈ U, (D.T₁ θ).Good q) → U.card + 1 ≤ Wc + 1 →
          ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧ E.fixingSubgroup ≤ X.N U ∧
            ∀ q : ℕ, (D.T₁ θ).Good q → q ∉ U → ∀ Q : Ideal Zbar, Q.IsMaximal →
              ((q : ℤ) : Zbar) ∈ Q → Q.inertia GalQ ≤ E.fixingSubgroup) :
    OddDensityModels W D := by
  intro Wc
  filter_upwards [h Wc] with θ hθ
  obtain ⟨X, hX, hF⟩ := hθ
  exact ⟨densityOfFiniteFields X hX (fun U hU _ => hR θ U fun q hq => (hU q hq).1) hF⟩

end ZInQ.Manuscript.RC.KSplitSeed
