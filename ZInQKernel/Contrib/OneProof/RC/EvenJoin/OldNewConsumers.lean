import ZInQKernel.Contrib.OneProof.RC.EvenJoin.OldNewProof
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedBudget

/-! Specialize the inventory and its placed consumers to the proved
old/new independence theorem. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion IsDedekindDomain
open NumberField O12 O12Local PrintsArith Symbols ThetaCoeff TraceLimits UpperHalfPlane Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 2500000

section Inventory

variable {N : ℕ} [NeZero N] {K L : Type} [Field K] [AddCommGroup L]
variable {ε : L →+ ZMod 2} {T : TypeData L ε}
variable (D : Finset (CuspDilation N)) (κ : K →+* ℂ)
variable (ha : ∀ x : ↥D, ∀ n, ∃ z : K, κ z = x.val.source.coeff n)
variable (hχ : ∀ x : ↥D, ∀ u, ∃ z : K, κ z = (x.val.source.char u : ℂ))

abbrev cuspInventory_proved : Inventory ↥D ↥(cuspSources D) K T N :=
  cuspInventory D κ ha hχ oldNewIndependenceWeightTwo_proved

theorem cuspInventory_coeff_proved (x : ↥D) (n : ℕ) :
    κ ((cuspInventory_proved (T := T) D κ ha hχ).expansion x n) = x.val.coeff n :=
  cuspInventory_coeff D κ ha hχ oldNewIndependenceWeightTwo_proved x n

theorem cuspInventory_char_proved (x : ↥D) (u : (ZMod N)ˣ) :
    κ ((cuspInventory_proved (T := T) D κ ha hχ).χ (cuspOrigin D x) u : K) =
      (x.val.char u : ℂ) :=
  cuspInventory_char D κ ha hχ oldNewIndependenceWeightTwo_proved x u

end Inventory

section PlacedInventory

variable {D : Type} [Fintype D] {N : ℕ} [NeZero N]
variable {m : D → ℕ} {a : D → ℕ → ℂ}
variable {A : ∀ b, CuspBlockExpansion (m b) (a b)} {hm : ∀ b, m b ∣ N}
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable (P : PlacedCuspLists A hm v)
variable {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2} (T : TypeData L ε)

abbrev PlacedCuspLists.inventory_proved :=
  P.inventory T oldNewIndependenceWeightTwo_proved

theorem PlacedCuspLists.block_span_proved (b : D) :
    a b ∈ Submodule.span ℂ (blockColumns (P.inventory_proved T) P.κ (m b) (P.blockChar b)) :=
  P.block_span T oldNewIndependenceWeightTwo_proved b

end PlacedInventory

section PlacedRow

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
  (evenBlockSeries P hS i b)}
variable [NeZero (movingLevel P U)]
variable (D : PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v)
variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
variable (hκ : D.κ.comp (D.fieldMap.comp C₀.eK) = C₀.eC)
variable (hB : IsMovingCharacter P U (A none).χ)
variable (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)

abbrev PlacedCuspLists.evenBasis_proved :=
  D.evenBasis hU oldNewIndependenceWeightTwo_proved

abbrev PlacedCuspLists.seed_proved :=
  D.seed hU oldNewIndependenceWeightTwo_proved C₀ hκ

theorem PlacedCuspLists.seed_complex_proved (n : ℕ) :
    D.κ ((D.evenBasis_proved hU).eval n (D.seed_proved hU C₀ hκ)) =
      (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n :=
  D.seed_complex hU oldNewIndependenceWeightTwo_proved C₀ hκ hodd n

include hodd in
theorem PlacedCuspLists.seed_integral_proved (n : ℕ) :
    (D.evenBasis_proved hU).eval n (D.seed_proved hU C₀ hκ) =
      algebraMap (FixedRing D.w) (FixedField D.w)
        (D.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n)) :=
  D.seed_integral hU oldNewIndependenceWeightTwo_proved C₀ hκ hodd n

include hB hJ hodd in
theorem placed_diamond_eval_proved (u : (ZMod (movingLevel P U))ˣ) :
    ∃ (ψ : FixedRing D.w) (c : ↥(subscripts U) → FixedRing D.w),
      (D.blockChar none u : FixedField D.w) = algebraMap _ _ ψ ∧ ∀ n,
      (D.evenBasis_proved hU).eval n
          ((D.evenBasis_proved hU).diamond u (D.seed_proved hU C₀ hκ)) =
        algebraMap (FixedRing D.w) (FixedField D.w)
          (ψ * D.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n) +
            ∑ j : ↥(subscripts U), c j * D.ringMap
              (timesTheta (unaryCoeff (evenTypes W.S hS.1).Good C₀.η i j.val) n)) :=
  placed_diamond_eval hU D C₀ hκ oldNewIndependenceWeightTwo_proved hB hJ u hodd

include hB hJ hodd in
theorem PlacedCuspLists.integral_diamonds_proved :
    ∀ u n, (D.evenBasis_proved hU).eval n
      ((D.evenBasis_proved hU).diamond u (D.seed_proved hU C₀ hκ)) ∈
        integralRange (O := FixedRing D.w) :=
  D.integral_diamonds hU C₀ hκ oldNewIndependenceWeightTwo_proved hB hJ hodd

theorem PlacedCuspLists.fresh_coeff_mem_proved {m : Ideal (FixedRing D.w)}
    (h2 : (2 : FixedRing D.w) ∈ m) (q r n : ℕ) (hn : n ≠ 0)
    (hq : (evenTypes W.S hS.1).Good q) (hr : (evenTypes W.S hS.1).Good r)
    (hqU : q ∉ U) (hrU : r ∉ U) (hqr : q ≠ r) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n) :
    let basis := D.evenBasis_proved hU
    let seed := D.seed_proved hU C₀ hκ
    oneCoeff basis seed Subtype.val_injective
      (D.integral_diamonds_proved hU C₀ hκ hB hJ hodd) (r * (q * n))
      (oneLatSeed basis (O := FixedRing D.w) seed U) ∈ m :=
  D.fresh_coeff_mem hU C₀ hκ oldNewIndependenceWeightTwo_proved hB hJ hodd h2
    q r n hn hq hr hqU hrU hqr hqn hrn

variable (H : D.sourceAttachments (hS := hS) oldNewIndependenceWeightTwo_proved)
variable (horder : ∃ e : ℕ, P.phaseData.η ^ (2 ^ e) = 1)

abbrev PlacedCuspLists.determinantData_proved {m : Ideal (FixedRing D.w)}
    (hm : m.IsMaximal) (h2 : (2 : FixedRing D.w) ∈ m) :=
  D.determinantData hU C₀ hκ oldNewIndependenceWeightTwo_proved hB hJ hodd H hm h2 horder

variable [NeZero (conductor W.S)]
variable (htwo : (2 : 𝓞 F) ∈ v.asIdeal)

abbrev PlacedCuspLists.model_proved (B : ℕ) : Σ X : Model P hS B, FourierData X :=
  D.model hU C₀ hκ oldNewIndependenceWeightTwo_proved hB hJ hodd H horder htwo B

theorem PlacedCuspLists.model_coordinates_proved (B n : ℕ) (hn : n ≠ 0) :
    let M := D.model_proved hU C₀ hκ hB hJ hodd H horder htwo B
    D.κ (algebraMap M.1.O M.1.K (M.2.coeff n (M.1.F U))) =
      (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n :=
  D.model_coordinates hU C₀ hκ oldNewIndependenceWeightTwo_proved hB hJ hodd H horder htwo B n hn

end PlacedRow

section Budget

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} [NeZero (conductor W.S)]
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
variable (j : C₀.K₀ →+* F)
variable (hK : (FinitePlace.embedding v).comp j = C₀.eK) (hC : F.subtype.comp j = C₀.eC)
variable (htwo : (2 : 𝓞 F) ∈ v.asIdeal)
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
variable (horder : ∃ e : ℕ, P.phaseData.η ^ (2 ^ e) = 1)

abbrev PlacedGaloisInput_proved (B : ℕ) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p) : Prop :=
  PlacedGaloisInput (hS := hS) C₀ j hK hC htwo hodd horder oldNewIndependenceWeightTwo_proved B U hU

theorem budgetRealization_of_placed_proved (B : ℕ)
    (H : ∀ U hU, U.card + 1 ≤ B → PlacedGaloisInput_proved (hS := hS) C₀ j hK hC
      htwo hodd horder B U hU) :
    BudgetRealizationScoped (hS := hS) C₀ i B :=
  budgetRealization_of_placed C₀ j hK hC htwo hodd horder oldNewIndependenceWeightTwo_proved B H

theorem rules_and_seed_of_placed_joint_proved
    (H : ∀ B U hU, U.card + 1 ≤ B → PlacedGaloisInput_proved (hS := hS) C₀ j hK hC
      htwo hodd horder B U hU) :
    CoefficientRules (evenSign W.S) (P.symbol hS) ∧
      ∃ Γ, IsUnitSeed (evenSign W.S) (P.symbol hS) Γ :=
  rules_and_seed_of_placed_joint C₀ j hK hC htwo hodd horder oldNewIndependenceWeightTwo_proved H

end Budget

end ZInQ.Manuscript.RC.EvenJoin
