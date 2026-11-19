import ZInQKernel.Contrib.CloudB3E2Norm.GenCxActualForm
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19Staged

/-!
# `GenCxResidualIso` for the staged presentation

Manuscript `diophantine_zq.tex`, tex 3455–3498, 4385–4414.

**`genCxResidualIso_staged`** (PROVED): for lane RC32's staged presentation `P` at the stage
`s` (the genuine `C_∅` of `stagedCx P s ∅`), `GenCxResidualIso` holds from finite residual
cohomology with ranks `Rk` of the actual-conditions form
`selCx (galoisSelData K (P.S s) (StageRing s') (famM P s s') (actualFormConds …))`, given that the
places of the chain are distinct (`hpl : Function.Injective P.pl`; a formalization requirement:
the text's chain has two distinct places above each unused prime, tex 4142–4146). The covering
`P.S s = P.S₀ s ∪ range P.pl` holds by definition, the unramified split inclusions are the genuine
inflations by `famEU_i`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.St0Shape

open IsLocalRing NumberField IsDedekindDomain
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Limits ZInQ.Manuscript.RC.Wiring
  ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53 (Ecurve)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {Ψ : FamilyMovingCharacter C.K ℓ Fam.Q}
  (P : StagedPresentation C D Fam x Ψ)

/-- The places of `S s` are those of `S₀ s` and of the chain (PROVED). -/
theorem staged_cov (s : ℕ) :
    ∀ v ∈ P.S s, v ∈ P.S₀ s ∨ ∃ j, (P.place s j).1 = v := by
  intro v hv
  rcases hv with h | ⟨j, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, rfl⟩

/-- **`GenCxResidualIso` for the staged presentation** (PROVED from the residual data of the
actual-conditions form and the distinctness of the places of the chain). -/
theorem genCxResidualIso_staged (s : ℕ) {Rk : ℕ → ℤ → ℕ} (hpl : Function.Injective P.pl)
    (hfin : ∀ s' [NeZero s'] n, Module.Finite (ResidueField (StageRing s'))
      (residualCohomologyAt (selCx (galoisSelData C.K (P.S s) (StageRing s') (famM P s s')
        (actualFormConds (P.hS s)
          (fun s' => Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s'))
          (famConds P s) s'))) n))
    (hrank : ∀ s' [NeZero s'] n, Module.finrank (ResidueField (StageRing s'))
      (residualCohomologyAt (selCx (galoisSelData C.K (P.S s) (StageRing s') (famM P s s')
        (actualFormConds (P.hS s)
          (fun s' => Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s'))
          (famConds P s) s'))) n) = Rk s' n) :
    GenCxResidualIso C.K (P.S₀ s) (P.S s) (famM P s) (famConds P s) (P.place s) (famX P s)
      (famEU P s) Rk :=
  genCxResidualIso_of_actualForm (P.hS s)
    (fun s' => Mcoef C.K (P.S₀ s) ((Ecurve ℓ).baseChange C.K) s' (P.alphaF s s'))
    (famConds P s) (P.place s) (P.hwp s) (famEU P s) (fun s' j => by rw [famEU_i]; rfl)
    (fun j j' h => hpl (congrArg Subtype.val h)) (staged_cov P s) hfin hrank

end ZInQ.Contrib.CloudB3E2.St0Shape
