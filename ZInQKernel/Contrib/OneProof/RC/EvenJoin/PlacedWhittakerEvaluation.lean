import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocal
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation

/-! Realize the finite test coefficients on the actual retained cuspidal
columns and supply the Whittaker premise of the scoped row (tex 9841–9856). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion
open IsDedekindDomain NumberField O12 O12Local PrintsArith Symbols ThetaCoeff Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

set_option Elab.async false
set_option maxHeartbeats 1500000

section Columns

variable {D : Type} [Fintype D] {N : ℕ} [NeZero N] {m : D → ℕ} {a : D → ℕ → ℂ}
variable {A : ∀ b, CuspBlockExpansion (m b) (a b)} {hm : ∀ b, m b ∣ N}
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable (R : PlacedCuspLists A hm v) {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}
variable (T : TypeData L ε) (hIndependent : Li1975OldNewIndependenceWeightTwo)
variable {p : ℕ} (hp : p.Prime)

/-- Evaluate each actual column, including away dilations, in the
receiving completion. The lift uses the placed coefficient of that
column, via the Fourier integral of its genuine level-`N` form. -/
def PlacedCuspLists.whittakerColumnValues :
    WhittakerColumnValues hp.ne_zero
      (fun (x : ↥(distinctCuspColumns A hm)) n => (R.inventory T hIndependent).expansion x n.val) :=
  whittakerColumnsOfForms (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (fun (x : ↥(distinctCuspColumns A hm)) => x.val.form) R.κ _ (by
      intro x n
      rw [x.val.coeff_form]
      exact cuspInventory_coeff _ _ _ _ hIndependent x n.val) hp.ne_zero

end Columns

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
  (evenBlockSeries P hS i b)}
variable [NeZero (movingLevel P U)] [NeZero (conductor W.S)]
variable (D : PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v)
variable (hIndependent : Li1975OldNewIndependenceWeightTwo)

omit [NeZero (conductor W.S)] in
/-- Supply the finite evaluation premise for the placed row. -/
theorem PlacedCuspLists.dilationWhittakerAt_of_forms {p : ℕ} (hp : p.Prime) :
    D.DilationWhittakerAt hIndependent hp.ne_zero :=
  ⟨D.whittakerColumnValues (evenTypes W.S hS.1) hIndependent hp⟩

variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
variable (hB : IsMovingCharacter P U (A none).χ)
variable (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
variable (horder : ∃ e : ℕ, P.phaseData.η ^ (2 ^ e) = 1)
variable (htwo : (2 : 𝓞 F) ∈ v.asIdeal)

include hB hJ in
/-- The row input for the existing scoped budget and joint consumer.
The column integral supplies the Whittaker data used by
`WhittakerComparison.coeff_shift` in the local coefficient calculation. -/
theorem PlacedCuspLists.placedGaloisInput_of_carayol_of_ramified
    (j : C₀.K₀ →+* F) (hK : (FinitePlace.embedding v).comp j = C₀.eK)
    (hC : F.subtype.comp j = C₀.eC) (hCarayol : CarayolRefold.CarayolThmAFrob) (B : ℕ)
    (hR : ∀ q (hq : q ∈ U) (Q : LocalPair q),
      letI : Fact q.Prime := ⟨(hU q hq).1⟩
      D.RamifiedNewvectorAt hIndependent
        (D.attachmentsOfCarayol hIndependent htwo hCarayol) Q) :
    PlacedGaloisInput (hS := hS) C₀ j hK hC htwo hodd horder hIndependent B U hU :=
  D.placedGaloisInput_of_carayol hU C₀ hIndependent hB hJ hodd horder htwo j hK hC hCarayol B hR
    (fun q hq => D.dilationWhittakerAt_of_forms hIndependent (hU q hq).1)

end ZInQ.Manuscript.RC.EvenJoin
