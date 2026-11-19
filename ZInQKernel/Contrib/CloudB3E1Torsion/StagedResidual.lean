import ZInQKernel.Contrib.CloudB3E1Torsion.OldRingChange
import ZInQKernel.Contrib.CloudB3E2Norm.GenCxStaged

/-!
# The staged presentation against the standard-old family

Manuscript `diophantine_zq.tex`, tex 2743–2760, 3455–3498, 4385–4414.

This file supplies piece (3) of `GenCxResidualIso` for lane RC32's staged presentation `P` at the
stage `s` and the precisions `s' = j + 1`. Lane E2's `genCxResidualIso_staged` needs residual
finiteness and ranks of the actual-conditions Selmer complex over `StageRing s'`. Here they are
identified with those of the standard-old family over `A_{s'} = Acoef s'`
(`actualSelData … standardOldAt …`, the contributor's `standardOld_producerBounds`), through
`stageEquiv s'`.

* `stagedLabel`, `stagedIota`, `stagedIota_smul` (definitions, PROVED): the reference choices.
  The label is Kummer (`2`) at the places of `Pk` and full (`1`) elsewhere. The curve is the
  local twist `localTwist W h v`, the level is `2^{s'}`, and the coefficient map is
  `kummerIotaS` at `Pk` and `0` elsewhere. These are the old conditions of the presentation
  (`stageCondsK`).
* `stagedOldCond` (definition): the presentation's old condition at `v ∈ S₀ s`, over
  `StageRing s'`, against the reference one over `A_{s'}`.
* **`staged_residual`** (PROVED): residual finiteness and ranks of the staged actual-conditions
  complex over `StageRing (j + 1)` equal those of the standard-old complex over `Acoef (j + 1)`.
* **`genCxResidualIso_staged_of_standardOld`** (PROVED): lane E2's `GenCxResidualIso` for the
  staged presentation, from finite residual cohomology of the standard-old family with ranks
  `Rk`, given distinct places of the chain.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open IsLocalRing NumberField IsDedekindDomain
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Limits ZInQ.Manuscript.RC.Wiring
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53 (Ecurve)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Contrib.RC53Assist.ResidualBounds (standardOldAt)
open ZInQ.Contrib.CloudB3E2.NormCochain (stageCondsK condK stageIsoA)
open ZInQ.Contrib.CloudB3E2.St0Shape (actualFormConds oldCond)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} {Ψ : FamilyMovingCharacter C.K ℓ Fam.Q}
  (P : StagedPresentation C D Fam x Ψ)

attribute [local instance] acoefTop acoefTop_discrete

/-- The curve of the stage `s`. Kind: definition. -/
abbrev stW : WeierstrassCurve C.K := (Ecurve ℓ).baseChange C.K

/-- The twist of the stage `s`. Kind: definition. -/
abbrev stH : C.K := ((Fam.h x : ℤ) : C.K)

/-- The local twist is elliptic. Kind: PROVED (instance). -/
instance stTwist_isElliptic (s : ℕ) (v : Places C.K (P.S s)) :
    (localTwist (stW (ℓ := ℓ) (C := C)) (stH (Fam := Fam) (x := x) (C := C)) v.1).IsElliptic :=
  isElliptic_localTwist _ (ne_zero_of_sqrt (P.sh s) (P.hs s) (P.hs0 s)) v.1

/-- **The reference labels**: Kummer (`2`) at `Pk`, full (`1`) elsewhere. Kind: definition. -/
def stagedLabel (s : ℕ) (v : Places C.K (P.S s)) : ℕ := by
  classical
  exact if v.1 ∈ P.Pk then 2 else 1

open scoped Classical in
/-- **The reference coefficient maps**: `kummerIotaS` at `Pk`, `0` elsewhere (label `1` never
reads it). Kind: definition. -/
def stagedIota (s j : ℕ) (v : Places C.K (P.S s)) :
    TorsAlg (v.1.adicCompletion C.K) (localTwist (stW (ℓ := ℓ) (C := C))
      (stH (Fam := Fam) (x := x) (C := C)) v.1) (2 ^ (j + 1)) →+
      ResMod (locMap C.K (P.S s) v.1)
        (MinS (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))) :=
  if v.1 ∈ P.Pk then
    kummerIotaS (P.hS s) _ (j + 1) (P.sh s) (P.hs s) (P.hs0 s) (P.alphaF s (j + 1))
      (HasFullTwoTorsion.full (j + 1)) v
  else 0

open scoped Classical in
/-- The reference coefficient maps are equivariant. Kind: PROVED. -/
theorem stagedIota_smul (s j : ℕ) (v : Places C.K (P.S s)) (σ : Gloc C.K v.1)
    (t : TorsAlg (v.1.adicCompletion C.K) (localTwist (stW (ℓ := ℓ) (C := C))
      (stH (Fam := Fam) (x := x) (C := C)) v.1) (2 ^ (j + 1))) :
    stagedIota P s j v (σ • t) = σ • stagedIota P s j v t := by
  unfold stagedIota
  split_ifs with hP
  · exact kummerIotaS_smul (P.hS s) _ (j + 1) (P.sh s) (P.hs s) (P.hs0 s) (P.alphaF s (j + 1))
      (HasFullTwoTorsion.full (j + 1)) v
      (ZInQ.Contrib.CloudB3E2.NormCochain.isLocallyQuadAt_stage (j + 1) (P.sh s) (P.hs s)
        (P.hs0 s) (P.ξ s) (P.ψf s (j + 1)) (P.hΨ s (j + 1)) v.1 hP) σ t
  · simp

/-- The coefficient module of the stage `s` at the precision `j + 1`. Kind: definition. -/
abbrev stM (s j : ℕ) : Type :=
  Mcoef C.K (P.S₀ s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))

omit [(Ecurve ℓ).IsElliptic] in
/-- Its `StageRing`-module structure is that over `A_{j+1}` through `stageEquiv`. Kind: PROVED. -/
theorem stM_smul (s j : ℕ) (r : StageRing (j + 1)) (m : stM P s j) :
    r • m = stageEquiv (j + 1) r • m := rfl

open scoped Classical in
/-- **The presentation's old condition against the reference one** at `v ∈ S₀ s`, over
`StageRing (j + 1)` against `A_{j+1}`. Kind: definition. -/
def stagedOldCond (s j : ℕ) (v : Places C.K (P.S s)) (h : v.1 ∈ P.S₀ s) :
    CondSEquiv (P.hS s) (stageEquiv (j + 1)) (stM P s j) (stM_smul P s j) v
      (oldCond (P.hS s) (fun s' => Mcoef C.K (P.S₀ s) (stW (ℓ := ℓ) (C := C)) s' (P.alphaF s s'))
        (famConds P s) (j + 1) v h)
      (standardOldAt C.K (P.S s) (Acoef (j + 1))
        (MinS (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))) v
        (stagedLabel P s v) (localTwist (stW (ℓ := ℓ) (C := C))
          (stH (Fam := Fam) (x := x) (C := C)) v.1) (2 ^ (j + 1)) (stagedIota P s j v)
        (stagedIota_smul P s j v)) := by
  by_cases hP : v.1 ∈ P.Pk
  · have hα := ZInQ.Contrib.CloudB3E2.NormCochain.isLocallyQuadAt_stage (j + 1) (P.sh s) (P.hs s)
      (P.hs0 s) (P.ξ s) (P.ψf s (j + 1)) (P.hΨ s (j + 1)) v.1 hP
    have e1 : oldCond (P.hS s)
        (fun s' => Mcoef C.K (P.S₀ s) (stW (ℓ := ℓ) (C := C)) s' (P.alphaF s s'))
        (famConds P s) (j + 1) v h =
        kummerAt (k := StageRing (j + 1)) v (localTwist (stW (ℓ := ℓ) (C := C))
          (stH (Fam := Fam) (x := x) (C := C)) v.1) (2 ^ (j + 1))
          (kummerIotaS (P.hS s) _ (j + 1) (P.sh s) (P.hs s) (P.hs0 s) (P.alphaF s (j + 1))
            (HasFullTwoTorsion.full (j + 1)) v)
          (kummerIotaS_smul (P.hS s) _ (j + 1) (P.sh s) (P.hs s) (P.hs0 s) (P.alphaF s (j + 1))
            (HasFullTwoTorsion.full (j + 1)) v hα) := by
      unfold oldCond famConds stageCondsK condK
      dsimp only
      rw [dite_eq_left_of_eq_true (eq_true hP)]
    have e2 : standardOldAt C.K (P.S s) (Acoef (j + 1))
        (MinS (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))) v
        (stagedLabel P s v) (localTwist (stW (ℓ := ℓ) (C := C))
          (stH (Fam := Fam) (x := x) (C := C)) v.1) (2 ^ (j + 1)) (stagedIota P s j v)
        (stagedIota_smul P s j v) =
        kummerAt (k := Acoef (j + 1)) v (localTwist (stW (ℓ := ℓ) (C := C))
          (stH (Fam := Fam) (x := x) (C := C)) v.1) (2 ^ (j + 1)) (stagedIota P s j v)
          (stagedIota_smul P s j v) := by
      unfold standardOldAt stagedLabel
      simp only [hP, ↓reduceIte]
      rfl
    rw [e1, e2]
    exact kummerAtCond' (P.hS s) (stageEquiv (j + 1)) (stM P s j) (stM_smul P s j) v _ _ _ _ _ _
      (fun t => by simp [stagedIota, hP])
  · have e1 : oldCond (P.hS s)
        (fun s' => Mcoef C.K (P.S₀ s) (stW (ℓ := ℓ) (C := C)) s' (P.alphaF s s'))
        (famConds P s) (j + 1) v h =
        fullAt C.K (P.S s) (StageRing (j + 1))
          (MinS (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))) v := by
      unfold oldCond famConds stageCondsK condK
      dsimp only
      rw [dite_eq_right_of_eq_false (eq_false hP)]
    have e2 : standardOldAt C.K (P.S s) (Acoef (j + 1))
        (MinS (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))) v
        (stagedLabel P s v) (localTwist (stW (ℓ := ℓ) (C := C))
          (stH (Fam := Fam) (x := x) (C := C)) v.1) (2 ^ (j + 1)) (stagedIota P s j v)
        (stagedIota_smul P s j v) =
        fullAt C.K (P.S s) (Acoef (j + 1))
          (MinS (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))) v := by
      unfold standardOldAt stagedLabel
      simp only [hP, ↓reduceIte]
      rfl
    rw [e1, e2]
    exact fullAtCond (P.hS s) (stageEquiv (j + 1)) (stM P s j) (stM_smul P s j) v


open scoped Classical in
/-- **Piece (3) of `GenCxResidualIso` for the staged presentation** (tex 4385–4414): at the stage
`s` and the precision `j + 1`, the residual cohomology of the actual-conditions Selmer complex
over `StageRing (j + 1)` (the `hfin`, `hrank` of `genCxResidualIso_staged`) is finite iff that of
the standard-old Selmer complex over `A_{j+1}` is, with the same ranks. The reference has labels
`stagedLabel` (Kummer at `Pk`, full elsewhere), curves `localTwist W h`, level `2^{j+1}` and
coefficient maps `stagedIota`; its producer bounds are the contributor's
`standardOld_producerBounds`. Kind: PROVED. -/
theorem staged_residual (s j : ℕ) (n : ℤ) :
    (Module.Finite (ResidueField (StageRing (j + 1))) (residualCohomologyAt
        (selCx (galoisSelData C.K (P.S s) (StageRing (j + 1)) (famM P s (j + 1))
          (actualFormConds (P.hS s)
            (fun s' => Mcoef C.K (P.S₀ s) (stW (ℓ := ℓ) (C := C)) s' (P.alphaF s s'))
            (famConds P s) (j + 1)))) n) ↔
      Module.Finite (ResidueField (Acoef (j + 1))) (residualCohomologyAt
        (selCx (actualSelData (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))
          (fun v _ => standardOldAt C.K (P.S s) (Acoef (j + 1))
            (MinS (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))) v
            (stagedLabel P s v) (localTwist (stW (ℓ := ℓ) (C := C))
              (stH (Fam := Fam) (x := x) (C := C)) v.1) (2 ^ (j + 1)) (stagedIota P s j v)
            (stagedIota_smul P s j v)))) n)) ∧
    Module.finrank (ResidueField (StageRing (j + 1))) (residualCohomologyAt
        (selCx (galoisSelData C.K (P.S s) (StageRing (j + 1)) (famM P s (j + 1))
          (actualFormConds (P.hS s)
            (fun s' => Mcoef C.K (P.S₀ s) (stW (ℓ := ℓ) (C := C)) s' (P.alphaF s s'))
            (famConds P s) (j + 1)))) n) =
      Module.finrank (ResidueField (Acoef (j + 1))) (residualCohomologyAt
        (selCx (actualSelData (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))
          (fun v _ => standardOldAt C.K (P.S s) (Acoef (j + 1))
            (MinS (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))) v
            (stagedLabel P s v) (localTwist (stW (ℓ := ℓ) (C := C))
              (stH (Fam := Fam) (x := x) (C := C)) v.1) (2 ^ (j + 1)) (stagedIota P s j v)
            (stagedIota_smul P s j v)))) n) :=
  actualForm_residual (fun v h => stagedOldCond P s j v h) n

open scoped Classical in
/-- **`GenCxResidualIso` for the staged presentation from the standard-old family** (tex
4385–4414). Assume the standard-old Selmer complexes over `A_{s'}` have finite residual cohomology
(the contributor's `stageSelmer_residualCohomologyFinite`) with residual ranks `Rk s'`. Then
`GenCxResidualIso` holds with the ranks `Rk`, given distinct places of the chain. Kind: PROVED. -/
theorem genCxResidualIso_staged_of_standardOld (s : ℕ) (hpl : Function.Injective P.pl)
    {Rk : ℕ → ℤ → ℕ}
    (hfin : ∀ j n, Module.Finite (ResidueField (Acoef (j + 1))) (residualCohomologyAt
      (selCx (actualSelData (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))
        (fun v _ => standardOldAt C.K (P.S s) (Acoef (j + 1))
          (MinS (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))) v
          (stagedLabel P s v) (localTwist (stW (ℓ := ℓ) (C := C))
            (stH (Fam := Fam) (x := x) (C := C)) v.1) (2 ^ (j + 1)) (stagedIota P s j v)
          (stagedIota_smul P s j v)))) n))
    (hrank : ∀ j n, Module.finrank (ResidueField (Acoef (j + 1))) (residualCohomologyAt
      (selCx (actualSelData (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))
        (fun v _ => standardOldAt C.K (P.S s) (Acoef (j + 1))
          (MinS (P.hS s) (stW (ℓ := ℓ) (C := C)) (j + 1) (P.alphaF s (j + 1))) v
          (stagedLabel P s v) (localTwist (stW (ℓ := ℓ) (C := C))
            (stH (Fam := Fam) (x := x) (C := C)) v.1) (2 ^ (j + 1)) (stagedIota P s j v)
          (stagedIota_smul P s j v)))) n) = Rk (j + 1) n) :
    ZInQ.Contrib.CloudB3E2.St0Shape.GenCxResidualIso C.K (P.S₀ s) (P.S s) (famM P s)
      (famConds P s) (P.place s) (famX P s) (famEU P s) Rk :=
  ZInQ.Contrib.CloudB3E2.St0Shape.genCxResidualIso_staged P s hpl
    (fun s' hs' n => match s', hs' with
      | 0, h => absurd rfl h.ne
      | j + 1, _ => (staged_residual P s j n).1.2 (hfin j n))
    (fun s' hs' n => match s', hs' with
      | 0, h => absurd rfl h.ne
      | j + 1, _ => (staged_residual P s j n).2.trans (hrank j n))

end ZInQ.Contrib.CloudB3E1Torsion
