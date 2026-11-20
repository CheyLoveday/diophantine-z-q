import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate17Leaf

/-!
# The genuine stage chains with the global classes given by a class provider

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194, 4157–4172) on
the actual presentation (`CommonCoordinate17Actual.lean`) at the stages of the inner limit
(tex 4385–4451).

In the round-13 form `GenuineStageSTUE`, the global classes `g` of the chain are free data, and the
step identities `hstep` are a field: a choice of the global classes could meet them. Here the
global classes come from a **class provider** `StageClassesAt A s` at the stage `s`: the
classes `g_j`, their global identities `g_{i+1} = e_i g_i + d b_i` with the leaf's point factors,
and their local lifts at the conditions of the supports (the zero classes form a provider,
`StageClassesAt.zero`: a provider alone pins nothing). For the text the provider is lane E2's: the
presentation classes of the Kummer classes of the actual anchored Heegner points with their norm
identity at the switch primes (to be supplied by lane E2). Given a provider:

* `actualConds_injective`, `actualConds_surjective₀`, `actualEU_surjective₀` (PROVED): the old
  conditions of the actual presentation are injective in degree one and surjective in degree zero,
  and the inflations are surjective in degree zero (lane E2's `stageCondK_injective`,
  `stageCondK_surjective₀`, `genuineιq_surjective₀`);
* **`exists_stepHyps_provider`** (PROVED): at a positive stage the step identities `CMStepHyps`
  of the chain are DERIVED from the pins (the classes of the chain are the presentation's classes
  of the provider's global classes; the relaxed functionals are lane RC30's paired functionals),
  the provider's global identities and lane RC30's retention (`exists_stepHyps_of_E2_RC30`);
* `chooseOn`, `chooseOn_spec`: witnesses chosen on a set of stages;
* **`StageChainsK`**, `StageChainsK.bw`, `StageChainsK.μ`, **`StageChainsK.hstep`**,
  `StageChainsK.limV`: the genuine stage chains on the actual presentation with the classes of a
  provider, without fields for the global classes, the boundaries, the coboundaries or the step
  identities (the boundaries and coboundaries are chosen from the derivation);
  **`GenuineStageSTUK`** with the end identifications, and **`GenuineStageSTUK.toSTUE`**: the
  round-13 form.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion MilneADT_I_2_8)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Local (IwasawaGenerators GenuineCochainsInjective)
open ZInQ.Contrib.CloudB3E2.NormCochain (stageCondK_injective stageCondK_surjective₀
  genuineιq_surjective₀ stageIsoA)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b} (A : ActualPresentation C D Fam x)

/-! ### The local maps of the actual presentation -/

section LocalMaps

/-- **The old conditions are injective in degree one** at the positive stages (lane E2's
`stageCondK_injective`; tex 2743–2760). Kind: PROVED. -/
theorem actualConds_injective (t : ℕ) (v₀ : Places C.K A.S₀) :
    Function.Injective (((actualConds A (t + 1)).i v₀).f 1 1 rfl) := by
  let _ := acoefTop (t + 1)
  have _ := acoefTop_discrete (t + 1)
  let _ := stageIsoA (t + 1)
  exact stageCondK_injective A.hS ((Ecurve ℓ).baseChange C.K) (t + 1) A.sh A.hs A.hs0
    (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk (A.hΨ (t + 1))
    (StageRing (t + 1)) v₀

/-- **The old conditions are surjective in degree zero** at the positive stages (lane E2's
`stageCondK_surjective₀`; tex 2743–2760). Kind: PROVED. -/
theorem actualConds_surjective₀ (t : ℕ) (v₀ : Places C.K A.S₀) :
    Function.Surjective (((actualConds A (t + 1)).i v₀).f 0 0 rfl) := by
  let _ := acoefTop (t + 1)
  have _ := acoefTop_discrete (t + 1)
  let _ := stageIsoA (t + 1)
  exact stageCondK_surjective₀ A.hS ((Ecurve ℓ).baseChange C.K) (t + 1) A.sh A.hs A.hs0
    (HasFullTwoTorsion.full (t + 1)) (A.π (t + 1)) (A.ψ (t + 1)) A.Pk (A.hΨ (t + 1))
    (StageRing (t + 1)) v₀

/-- **The genuine inflations are surjective in degree zero** (lane E2's
`genuineιq_surjective₀`, along `urId`; tex 3470–3487). Kind: PROVED. -/
theorem actualEU_surjective₀ (s : ℕ) (j : A.ι × Bool) :
    Function.Surjective ((actualEU A s j).i.f 0 0 rfl) := by
  rw [actualEU_i A s j]
  exact genuineιq_surjective₀ (A.place j) _ _ _
    (urId_bijective (StageRing s) _ A.hS (newPlace (A.place j) (A.hwp j))).2

end LocalMaps

/-! ### Class providers -/

section Provider

/-- **A class provider at the stage `s`** (tex 4157–4172): global classes `g_j` of the actual
coefficient module, the global identities `g_{i+1} = e_i g_i + d b_i` at the steps with the
leaf's point factors `e_i = a_i − z_i − z_i⁻¹` at the stage, and local lifts of `g_j` at the
conditions of the support `C_{T_j}`. The zero classes form a provider (`StageClassesAt.zero`):
a provider alone pins nothing; the leaf pins the provider to the Kummer classes of the actual
Heegner points. Kind: definition (data). -/
structure StageClassesAt (s : ℕ) : Type where
  /-- the global classes -/
  g : ℕ → (globalCx (StageRing s) (GKS C.K A.S) (actualM A s)).X 1
  /-- the global identities at the steps -/
  hG : ∀ i < A.ps.length,
    ∃ bG : (globalCx (StageRing s) (GKS C.K A.S) (actualM A s)).X 0,
      g (i + 1) = pointFactor (((leafFrobΛ C Fam x A.ps).map (stageMk s)).a i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).z i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).zi i) • g i +
        (globalCx (StageRing s) (GKS C.K A.S) (actualM A s)).d 0 1 rfl bG
  /-- the local lifts at the conditions of the supports -/
  hloc : ∀ j ≤ A.ps.length, ∃ u : (piCx (presCondS C.K A.S₀ A.S (StageRing s)
      (actualM A s) (actualConds A s) A.place (actualX A s)
      (actualEU A s) (chainT A.pidx j)).U).X 1,
    (piMap (presCondS C.K A.S₀ A.S (StageRing s) (actualM A s)
      (actualConds A s) A.place (actualX A s) (actualEU A s)
      (chainT A.pidx j)).i).f 1 1 rfl u =
      (resS (StageRing s) (GKS C.K A.S) (presGv C.K A.S₀ A.S A.place)
        (presLoc C.K A.S₀ A.S A.place) (actualM A s)).f 1 1 rfl (g j)

/-- **The zero provider** (tex 4157–4172): the zero classes satisfy the identities and have
local lifts, so a provider is a constraint only through the leaf's pin. Kind: definition. -/
def StageClassesAt.zero (s : ℕ) : StageClassesAt A s where
  g _ := 0
  hG _ _ := ⟨0, by rw [smul_zero, map_zero, add_zero]⟩
  hloc _ _ := ⟨0, by rw [map_zero, map_zero]⟩

variable {A} {s : ℕ}

open Classical in
/-- The provider's classes, extended by `0` beyond the chain. Kind: definition. -/
def StageClassesAt.gx (HC : StageClassesAt A s) (j : ℕ) :
    (globalCx (StageRing s) (GKS C.K A.S) (actualM A s)).X 1 :=
  if j ≤ A.ps.length then HC.g j else 0

open Classical in
/-- The chosen local lifts of the provider's classes, `0` beyond the chain. Kind: definition. -/
def StageClassesAt.ux (HC : StageClassesAt A s) (j : ℕ) :
    (piCx (presCondS C.K A.S₀ A.S (StageRing s) (actualM A s)
      (actualConds A s) A.place (actualX A s) (actualEU A s)
      (chainT A.pidx j)).U).X 1 :=
  if hj : j ≤ A.ps.length then Classical.choose (HC.hloc j hj) else 0

/-- The chosen lifts lift the extended classes (tex 4157–4172). Kind: PROVED. -/
theorem StageClassesAt.hux (HC : StageClassesAt A s) (j : ℕ) :
    (piMap (presCondS C.K A.S₀ A.S (StageRing s) (actualM A s)
      (actualConds A s) A.place (actualX A s) (actualEU A s)
      (chainT A.pidx j)).i).f 1 1 rfl (HC.ux j) =
      (resS (StageRing s) (GKS C.K A.S) (presGv C.K A.S₀ A.S A.place)
        (presLoc C.K A.S₀ A.S A.place) (actualM A s)).f 1 1 rfl (HC.gx j) := by
  by_cases hj : j ≤ A.ps.length
  · simp only [StageClassesAt.ux, StageClassesAt.gx, hj, ↓reduceDIte, ↓reduceIte]
    exact Classical.choose_spec (HC.hloc j hj)
  · simp only [StageClassesAt.ux, StageClassesAt.gx, hj, ↓reduceDIte, ↓reduceIte, map_zero]

/-- The extended classes satisfy the global identities at the steps (tex 4157–4172).
Kind: PROVED. -/
theorem StageClassesAt.hGx (HC : StageClassesAt A s) {i : ℕ} (hi : i < A.ps.length) :
    ∃ bG : (globalCx (StageRing s) (GKS C.K A.S) (actualM A s)).X 0,
      HC.gx (i + 1) = pointFactor (((leafFrobΛ C Fam x A.ps).map (stageMk s)).a i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).z i)
          (((leafFrobΛ C Fam x A.ps).map (stageMk s)).zi i) • HC.gx i +
        (globalCx (StageRing s) (GKS C.K A.S) (actualM A s)).d 0 1 rfl bG := by
  have h1 : i + 1 ≤ A.ps.length := hi
  have h2 : i ≤ A.ps.length := hi.le
  simp only [StageClassesAt.gx, h1, h2, ↓reduceIte]
  exact HC.hG i hi

end Provider

/-! ### Choice on a set of stages -/

section Choose

/-- **A choice of witnesses on a set of stages** (tex 4401–4406): at the stages of `G` a pair
chosen from an existence statement, `0` elsewhere. Kind: definition. -/
noncomputable def chooseOn {G : Set ℕ} {α β : ℕ → Type} [∀ s, Zero (α s)] [∀ s, Zero (β s)]
    {P : ∀ s, s ∈ G → α s → β s → Prop} (hex : ∀ s (h : s ∈ G), ∃ a b, P s h a b) (s : ℕ) :
    α s × β s := by
  classical
  exact if h : s ∈ G then (Classical.choose (hex s h), Classical.choose (Classical.choose_spec
    (hex s h))) else (0, 0)

/-- The chosen witnesses satisfy the statement (tex 4401–4406). Kind: PROVED. -/
theorem chooseOn_spec {G : Set ℕ} {α β : ℕ → Type} [∀ s, Zero (α s)] [∀ s, Zero (β s)]
    {P : ∀ s, s ∈ G → α s → β s → Prop} (hex : ∀ s (h : s ∈ G), ∃ a b, P s h a b) :
    ∀ s (h : s ∈ G), P s h (chooseOn hex s).1 (chooseOn hex s).2 := by
  intro s h
  classical
  simp only [chooseOn, h, ↓reduceDIte]
  exact Classical.choose_spec (Classical.choose_spec (hex s h))

end Choose

/-! ### The step identities derived from a provider -/

section Chains

variable [DecidableEq (Places C.K A.S₀)]

/-- The leaf's traces at the stage (tex 4169). Kind: definition. -/
abbrev leafTr (s : ℕ) (i : ℕ) : StageRing s := ((leafFrobΛ C Fam x A.ps).map (stageMk s)).a i

variable {A}

/-- **The step identities of a stage chain are derived from a provider** (tex 4157–4172,
4385–4451): at a positive stage, if the classes of the chain are the presentation's classes of the
provider's global classes (`hz0`, `hzR`), the relaxed functionals and the primitive functionals of
the steps are lane RC30's paired functionals of a retention (`hR`, `hP`) with the leaf's point
factors (`he`), and the Frobenius data are the leaf's (`hfrob`), then there are boundaries and
coboundaries with `CMStepHyps` (`exists_stepHyps_of_E2_RC30`, with the old conditions and the
inflations of the actual presentation). Kind: PROVED. -/
theorem exists_stepHyps_provider {h28 : MilneADT_I_2_8} {hI : IwasawaGenerators}
    {hInj : GenuineCochainsInjective} {s m0 m1 m2 : ℕ} (hs : 0 < s)
    (gs : GenuineStageSteps C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A)
      (actualEU A) s m0 m1 m2 A.pidx A.ps.length)
    (HC : StageClassesAt A s)
    (hz0 : gs.st0.z = presClass C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A)
      (actualEU A) s ∅ (HC.gx 0) (HC.ux 0))
    (hzR : ∀ i, gs.zR i = presClass C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A)
      (actualEU A) s (chainT A.pidx (i + 1)) (HC.gx (i + 1)) (HC.ux (i + 1)))
    (R : ∀ i (hi : i < A.ps.length), StepRetention C.K A.S₀ A.S (actualM A) (actualConds A)
      A.place (actualX A) (actualEU A) s (chainT A.pidx i) (A.pidx i) (gs.hnew i hi))
    (he : ∀ i (hi : i < A.ps.length),
      (R i hi).e = pointFactor (leafTr A s i) (gs.z i) (gs.zi i))
    (hR : ∀ i (hi : i < A.ps.length), gs.lamR i =
      pairedFun (R i hi).I.toPlaceRetentionG.toRetainedPairing.QR
        ((R i hi).tr : (coneCx (R i hi).I.toPlaceRetentionG.toRetainedPairing.QR.resE).X 3
          →ₗ[StageRing s] StageRing s) (R i hi).zS)
    (hP : ∀ i (hi : i < A.ps.length), (cmState (gs.toChainM h28 hI hInj) i hi.le).lam =
      pairedFun (R i hi).I.toPlaceRetentionG.toRetainedPairing.QP (R i hi).tr (R i hi).zP)
    (hfrob : StageFrobAt (leafFrobΛ C Fam x A.ps) s (gs.toChainM h28 hI hInj) (leafTr A s)) :
    ∃ (bw : ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A)
        (actualEU A) s (insert (A.pidx i) (chainT A.pidx i))).X 0)
      (μ : ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A)
        (actualEU A) s (chainT A.pidx i)).X 3 →ₗ[StageRing s] StageRing s),
      CMStepHyps (gs.toChainM h28 hI hInj) (leafTr A s) bw μ := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hG : ∀ i, ∃ bG : (globalCx (StageRing (t + 1)) (GKS C.K A.S) (actualM A (t + 1))).X 0,
      i < A.ps.length → HC.gx (i + 1) = pointFactor (leafTr A (t + 1) i)
        ((gs.toChainM h28 hI hInj).z i) ((gs.toChainM h28 hI hInj).zi i) • HC.gx i +
        (globalCx (StageRing (t + 1)) (GKS C.K A.S) (actualM A (t + 1))).d 0 1 rfl bG := by
    intro i
    by_cases hi : i < A.ps.length
    · obtain ⟨bG, hbG⟩ := HC.hGx hi
      obtain ⟨-, -, hz, hzi, -⟩ := hfrob i hi
      refine ⟨bG, fun _ => ?_⟩
      rw [← hz, ← hzi]
      exact hbG
    · exact ⟨0, fun h => absurd h hi⟩
  choose bG hbG using hG
  exact exists_stepHyps_of_E2_RC30 (gs.toChainM h28 hI hInj) (leafTr A (t + 1)) HC.gx HC.ux
    HC.hux hz0 hzR bG hbG (actualConds_injective A t) (actualConds_surjective₀ A t)
    (actualEU_surjective₀ A (t + 1)) gs.hnew R he hR hP

end Chains

/-! ### The genuine stage chains with the classes of a provider -/

section Structure

variable [DecidableEq (Places C.K A.S₀)]

/-- **The genuine stage chains of one address with the classes of a provider** (tex 4142–4194,
4157–4172, 4385–4451): at the retained stages `G` (all positive), the genuine data of the chain on
the actual presentation, with the classes pinned to the presentation's classes of the provider's
global classes, the functionals pinned to lane RC30's paired functionals of a retention (GLUE: the
cup-product data of the retention are not pinned; the genuine cup product of Nekovář 6.2.5–6.4.3
is the intended instance), and the leaf's Frobenius data. There are no fields for the global
classes, the boundaries, the coboundaries or the step identities. Kind: definition (data). -/
structure StageChainsK (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators)
    (hInj : GenuineCochainsInjective) (G : Set ℕ) (HC : ∀ s, s ∈ G → StageClassesAt A s) :
    Type 1 where
  /-- the retained stages are positive (definition; at the zero ring the conditions are not lane
  RC29's) -/
  hpos : ∀ s ∈ G, 0 < s
  /-- the rank of the model of `C_∅` in degree `0` (ELLIOT: bounded ranks; tex 4401–4406) -/
  m0 : ℕ
  /-- the rank of the model of `C_∅` in degree `1` besides the class (ELLIOT; tex 4401–4406) -/
  m1 : ℕ
  /-- the rank of the model of `C_∅` in degree `3` (ELLIOT; tex 4401–4406) -/
  m2 : ℕ
  /-- the genuine data of the chain at the retained stages (data and named inputs; on the actual
  presentation, `actualSteps`; tex 3455–3498, 4142–4194) -/
  gs : ∀ s, s ∈ G → GenuineStageSteps C.K A.S₀ A.S (actualM A) (actualConds A) A.place
    (actualX A) (actualEU A) s m0 m1 m2 A.pidx A.ps.length
  /-- the primitive class of `C_∅` is the class of the provider's first class (pin; tex 4153) -/
  hz0 : ∀ s (h : s ∈ G), (gs s h).st0.z = presClass C.K A.S₀ A.S (actualM A) (actualConds A)
    A.place (actualX A) (actualEU A) s ∅ ((HC s h).gx 0) ((HC s h).ux 0)
  /-- the relaxed classes are the classes of the provider's classes (pin; tex 4169–4171) -/
  hzR : ∀ s (h : s ∈ G) i, (gs s h).zR i = presClass C.K A.S₀ A.S (actualM A) (actualConds A)
    A.place (actualX A) (actualEU A) s (chainT A.pidx (i + 1)) ((HC s h).gx (i + 1))
      ((HC s h).ux (i + 1))
  /-- lane RC30's retention at the switches (GLUE; tex 4160–4172) -/
  R : ∀ s (h : s ∈ G) i (hi : i < A.ps.length), StepRetention C.K A.S₀ A.S (actualM A)
    (actualConds A) A.place (actualX A) (actualEU A) s (chainT A.pidx i) (A.pidx i)
      ((gs s h).hnew i hi)
  /-- the retention's point factor is the leaf's (definition; tex 4158, 4169) -/
  he : ∀ s (h : s ∈ G) i (hi : i < A.ps.length),
    (R s h i hi).e = pointFactor (leafTr A s i) ((gs s h).z i) ((gs s h).zi i)
  /-- the relaxed functionals are the retention's paired functionals (pin; tex 4171–4172) -/
  hR : ∀ s (h : s ∈ G) i (hi : i < A.ps.length), (gs s h).lamR i =
    pairedFun (R s h i hi).I.toPlaceRetentionG.toRetainedPairing.QR
      ((R s h i hi).tr : (coneCx (R s h i hi).I.toPlaceRetentionG.toRetainedPairing.QR.resE).X 3
        →ₗ[StageRing s] StageRing s) (R s h i hi).zS
  /-- the primitive functional of each step is the retention's (pin; tex 4171–4172) -/
  hP : ∀ s (h : s ∈ G) i (hi : i < A.ps.length),
    (cmState ((gs s h).toChainM h28 hI hInj) i hi.le).lam =
      pairedFun (R s h i hi).I.toPlaceRetentionG.toRetainedPairing.QP (R s h i hi).tr
        (R s h i hi).zP
  /-- the leaf's Frobenius data (GLUE: the Frobenius identifications; PROVED for the chains built
  by `actualSteps`, `actualSteps_stageFrobAt`; tex 4144–4145, 4176–4184) -/
  hfrob : ∀ s (h : s ∈ G),
    StageFrobAt (leafFrobΛ C Fam x A.ps) s ((gs s h).toChainM h28 hI hInj) (leafTr A s)

variable {A} {h28 : MilneADT_I_2_8} {hI : IwasawaGenerators} {hInj : GenuineCochainsInjective}
  {G : Set ℕ} {HC : ∀ s, s ∈ G → StageClassesAt A s}

/-- **The step identities hold at every retained stage** (PROVED; `exists_stepHyps_provider`). -/
theorem StageChainsK.ex (P : StageChainsK A h28 hI hInj G HC) :
    ∀ s (h : s ∈ G), ∃ (bw : ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place
        (actualX A) (actualEU A) s (insert (A.pidx i) (chainT A.pidx i))).X 0)
      (μ : ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A)
        (actualEU A) s (chainT A.pidx i)).X 3 →ₗ[StageRing s] StageRing s),
      CMStepHyps ((P.gs s h).toChainM h28 hI hInj) (leafTr A s) bw μ :=
  fun s h => exists_stepHyps_provider (P.hpos s h) (P.gs s h) (HC s h) (P.hz0 s h) (P.hzR s h)
    (P.R s h) (P.he s h) (P.hR s h) (P.hP s h) (P.hfrob s h)

/-- The chosen boundaries of the norm identities (tex 4169–4171). Kind: definition. -/
noncomputable def StageChainsK.bw (P : StageChainsK A h28 hI hInj G HC) (s : ℕ) :
    ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A) (actualEU A) s
      (insert (A.pidx i) (chainT A.pidx i))).X 0 :=
  (chooseOn P.ex s).1

/-- The chosen coboundaries of the functional relations (tex 4171–4172). Kind: definition. -/
noncomputable def StageChainsK.μ (P : StageChainsK A h28 hI hInj G HC) (s : ℕ) :
    ∀ i, (genCx C.K A.S₀ A.S (actualM A) (actualConds A) A.place (actualX A) (actualEU A) s
      (chainT A.pidx i)).X 3 →ₗ[StageRing s] StageRing s :=
  (chooseOn P.ex s).2

/-- **The step identities with the chosen witnesses** (tex 4157–4172). Kind: PROVED. -/
theorem StageChainsK.hstep (P : StageChainsK A h28 hI hInj G HC) :
    ∀ s (h : s ∈ G), CMStepHyps ((P.gs s h).toChainM h28 hI hInj) (leafTr A s) (P.bw s) (P.μ s) :=
  chooseOn_spec P.ex

/-- **The coordinates of the limit chain** (tex 4185–4193, 4401–4406, 4444–4448): the values of
the chain over `Frac Λ` of the ultralimit of the stage data. Kind: definition. -/
noncomputable def StageChainsK.limV (P : StageChainsK A h28 hI hInj G HC) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ cofinite) (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G) (i : ℕ) : FracLam :=
  (fracChain (stageMatsOn G (fun s h => (P.gs s h).toChainM h28 hI hInj) P.bw P.μ) U).chainV
    (fracChain_holds _ hU _ _ (stageMatsOn_hs G _ P.bw P.μ _ U (leafTr A) hG P.hstep P.hfrob)) i

/-- **The genuine stage chains of one address with the classes of a provider, at a fixed
ultrafilter** (tex 4142–4194, 4385–4451): the chains `StageChainsK` on `U`-many stages, and the
end identifications with the leaf's data (`ũ_x` up to the text's unit `ε_x ∈ Λ^×`, `1` when
`U_x = ∅`). Kind: definition (data). -/
structure GenuineStageSTUK (A : ActualPresentation C D Fam x) [DecidableEq (Places C.K A.S₀)]
    (h28 : MilneADT_I_2_8) (hI : IwasawaGenerators) (hInj : GenuineCochainsInjective)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) (G : Set ℕ)
    (HC : ∀ s, s ∈ G → StageClassesAt A s) : Type 1 where
  /-- the graph primes are primes of good reduction (definition: admissibility; tex 4143) -/
  hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q
  /-- the retained stages are `U`-many (ELLIOT: the ranks are fixed along `U`; tex 4401–4406) -/
  hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G
  /-- the chains at the retained stages -/
  pre : StageChainsK A h28 hI hInj G HC
  /-- the primitive coordinate of the limit has `t`-expansion `u_{prim,x}` (definition of
  `u_{prim,x}` in the normalized basis; tex 4153, 4185–4193) -/
  hprim : IsTExpansion (pre.limV U hU hG 0) (D.uPrim Fam x)
  /-- the corrected coordinate at `U_x` is `ũ_x` up to the text's unit (definition of `ũ_x`;
  tex 4147, 4150–4152, 4187–4194) -/
  htildeE : ∃ ε : Lambdaˣ, (A.ps = [] → ε = 1) ∧
    IsTExpansion (lamToF (ε : Lambda) * (etaF ℓ Fam x * pre.limV U hU hG A.ps.length))
      (D.uTilde Fam x)

/-- **The round-13 form from a provider** (tex 4142–4194, 4385–4451): the global classes are the
provider's, the boundaries and coboundaries are the chosen witnesses, and the step identities are
derived. Kind: definition. -/
noncomputable def GenuineStageSTUK.toSTUE {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ cofinite}
    (Gs : GenuineStageSTUK A h28 hI hInj U hU G HC) :
    ActualGenuineStageSTUE A h28 hI hInj U hU where
  hprime := A.hprime
  hgood := Gs.hgood
  ps := A.ps
  hnd := A.hnd
  hps := A.hps
  m0 := Gs.pre.m0
  m1 := Gs.pre.m1
  m2 := Gs.pre.m2
  G := G
  hG := Gs.hG
  gs := Gs.pre.gs
  a := leafTr A
  g s h := (HC s h).gx
  u s h := (HC s h).ux
  hu s h := (HC s h).hux
  hz0 := Gs.pre.hz0
  hzR := Gs.pre.hzR
  R := Gs.pre.R
  he := Gs.pre.he
  hR := Gs.pre.hR
  hP := Gs.pre.hP
  bw := Gs.pre.bw
  μ := Gs.pre.μ
  hstep := Gs.pre.hstep
  hfrob := Gs.pre.hfrob
  hprim := Gs.hprim
  htildeE := Gs.htildeE

/-- The round-13 form relaxes the presentation's primes (tex 4142–4146). Kind: PROVED. -/
theorem GenuineStageSTUK.toSTUE_ps {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ cofinite}
    (Gs : GenuineStageSTUK A h28 hI hInj U hU G HC) : Gs.toSTUE.ps = A.ps :=
  rfl

/-- The round-13 form has the same retained stages (tex 4401–4406). Kind: PROVED. -/
theorem GenuineStageSTUK.toSTUE_G {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ cofinite}
    (Gs : GenuineStageSTUK A h28 hI hInj U hU G HC) : Gs.toSTUE.G = G :=
  rfl

end Structure

end ZInQ.Manuscript.RC.Wiring
