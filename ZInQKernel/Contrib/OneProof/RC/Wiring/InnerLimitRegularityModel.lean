import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitSwitchModel
import ZInQKernel.Contrib.RC53Assist.SwitchWiring.Boundary

/-!
# Theorem 5.3, Lane RC0 round 14: the height-one leaf on the inner-limit route with side models

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5200), on the text's
inner-limit route at nonquadratic specializations (tex 5027–5086, 4834–4907, 4385–4451) and with
homology-level single-sign and mixed switches at quadratic specializations (tex 5005–5054,
5116–5136).

`PrimRegularityInputsILM D`: the two PRINTs of residual finiteness (Milne, Arithmetic duality
theorems, I.2.3 for the local and I.4.10 for the global cohomology with finite coefficients), and
for every final family and address a `t`-expansion `u` of the primitive coordinate with
`RegularityInputsILM u`: either `u = 0`, or at every height-one prime `𝔭 ≠ (2)` a
configuration family genuine at `𝔭` and
* at a nonquadratic specialization: a number field `K`, a set of places `S`, the actual conjugation,
  the curve `W = E_ℓ ⊗ K` (the address's curve over `K`) with full two-torsion, and
  `InnerLimitSwitchActual` over the family (`InnerLimitSwitchModel.lean`: the switches on the
  actual stage complexes with their links, the side models);
* at a quadratic specialization (`t̄ (t̄ + 2) = 0`): `HomologySwitchDataPK` over the family.

PROVED: `RegularityInputsILM.mem_lambdaHalf`, `primRegularityInputs_of_ILM`,
`heightOneTarget_of_ILM` (the consumers of `prim_regular`), and the comparison with the wired leaf
`PrimRegularityInputsHPK` through the common model-level leaf `PrimRegularityInputsMdl`:
`PrimRegularityInputsILM.toMdl` and `PrimRegularityInputsHPK.toMdl` (`HomologySwitchDataPK` at a
nonquadratic specialization gives `SwitchModelInputs`, the literal side equalities giving the side
models), and `PrimRegularityInputsILB.toMdl` for the earlier inner-limit candidate. Neither
`ILM ⇒ HPK` nor `HPK ⇒ ILM` is claimed: the wired leaf asks the switch sides to EQUAL the fibres as
Selmer data, which the inner-limit sides are not (they are the limit sides of the retained data,
homotopy equivalent to the fibres), and its steps need not come from inner-limit data.
Degenerate satisfiability: `primRegularityInputsILM_of_uPrim_zero`.

The earlier inner-limit candidate, whose switch sides EQUAL the fibres, has no inputs at a fibre
of dimension above three (`no_ILSwitchInputsPK_of_large_fibre`, and the `A` and `B` forms): a
successor reached as a singular side cannot start a further switch (the RC53 group's
`finite_singular_ne`). The side models of this leaf remove that restriction.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing Module
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Rings (isDiscreteValuationRing_atPrime_of_height_one)
open ZInQ.Manuscript.RC.Uniform (Lambda lambdaHalfToFrac mem_range_lambdaHalf_iff_forall_height_one)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness MilneGlobalFiniteness)
open ZInQ.Contrib.RC53Assist.ResidualBounds (MilneLocalDimensionTwo)
open ZInQ.Contrib.CloudB3RC53.RankCounts (MilneADT_I_4_10_totallyComplex)

/-! **The homology-level data at a nonquadratic specialization give the model-level inputs** -/

section HomologyToModel

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]
  {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- **`HomologySwitchDataPK` at a nonquadratic specialization gives `SwitchModelInputs`**: the
frame from its stages, models and starting data, and each switch from its nonquadratic step, whose
literal side equalities give the side models (`HomotopyEquiv.refl`). Kind: PROVED. -/
def HomologySwitchDataPK.toModelInputs (G : HomologySwitchDataPK Φ ι ρ u)
    (hnq : ¬ Φ.quadratic ρ) : SwitchModelInputs Φ ι ρ u where
  stage := G.stage
  model := G.model
  hz0 := G.hz0
  hw0 := G.hw0
  hu0 := G.hu0
  hnq := hnq
  class_ne_zero := G.class_ne_zero
  step c hc h1 := by
    obtain ⟨p, hcs, -, hN⟩ := G.switch_mixed c hc (Or.inl hnq) h1
    obtain ⟨N, hF, hS⟩ := hN hnq
    refine ⟨p, hcs, N, ?_, ?_⟩
    · rw [hF]
      exact ⟨HomotopyEquiv.refl _⟩
    · rw [hS]
      exact ⟨HomotopyEquiv.refl _⟩

end HomologyToModel

/-! **The earlier inner-limit candidate gives the inputs with side models** -/

section EarlierCandidate

variable {h410 : MilneADT_I_4_10_totallyComplex} {hlcd : MilneLocalDimensionTwo}
  {hmloc : MilneLocalFiniteness} {hmglob : MilneGlobalFiniteness}
  {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {Cn : ActualConj K S} {W : WeierstrassCurve K}
  {hW : W.map (Cn.κ : K →+* K) = W} [W.IsElliptic] [HasFullTwoTorsion K S W]
  {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {ι : Localization.AtPrime P →+* F}
  {u : F}

/-- **The earlier candidate's inputs give the inner-limit inputs with side models**: the literal
side equalities of `ILSwitchInputsB` give the side models (`HomotopyEquiv.refl`). Kind: PROVED. -/
def ILSwitchInputsB.toInner (X : ILSwitchInputsB h410 hlcd hmloc hmglob P Cn W hW Φ ι u) :
    InnerLimitSwitchModel P Φ ι u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  hnq := X.hnq
  class_ne_zero := X.class_ne_zero
  step c hc h1 := by
    obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    refine ⟨p, hcs, (Y.toILStageStepActual h410 hlcd hmloc hmglob).toStepData hmloc hmglob,
      ?_, ?_⟩
    · rw [hF]
      exact ⟨HomotopyEquiv.refl _⟩
    · rw [hS]
      exact ⟨HomotopyEquiv.refl _⟩

end EarlierCandidate

/-! **The earlier candidate is uninhabitable above fibre dimension three** -/

section LiteralBoundary

open ZInQ.Contrib.RC53Assist.SwitchWiring (finite_singular_ne)

variable {h410 : MilneADT_I_4_10_totallyComplex} {hlcd : MilneLocalDimensionTwo}
  {hmloc : MilneLocalFiniteness} {hmglob : MilneGlobalFiniteness}
  {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {Cn : ActualConj K S} {W : WeierstrassCurve K}
  {hW : W.map (Cn.κ : K →+* K) = W} [W.IsElliptic] [HasFullTwoTorsion K S W]
  {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {ι : Localization.AtPrime P →+* F}
  {u : F}

/-- **A successor reached as a literal singular side is terminal** for the earlier inner-limit
candidate (its switch sides EQUAL the fibres): a further switch would make the successor's fibre
both a singular and a finite inner-limit side, which differ as Selmer data (the RC53 group's
`finite_singular_ne`). Kind: PROVED. -/
theorem ILSwitchInputsPK.successor_dimension_le_one (X : ILSwitchInputsPK P Cn W hW Φ ι u)
    {c : Φ.Config} {p : Φ.Prime} (hc : Reach Φ.next Φ.actual c)
    (Y : InnerLimitStepData P (X.stage c) (X.stage (Φ.next c p)))
    (hS : Y.toStep.SS.Dside = Φ.fibre (Φ.next c p)) :
    (X.stage (Φ.next c p)).fiberDim (resAt P) ≤ 1 := by
  by_contra! h1
  obtain ⟨p', -, Z, hF, -⟩ := X.step (Φ.next c p) (Reach.step p hc) h1
  exact finite_singular_ne _ _ (hF.trans hS.symm)

/-- **Every reached stage of the earlier candidate has fiber dimension at most three** (one
switch drops the dimension by two, and its successor is terminal). Kind: PROVED. -/
theorem ILSwitchInputsPK.reachable_dimension_le_three (X : ILSwitchInputsPK P Cn W hW Φ ι u)
    {c : Φ.Config} (hc : Reach Φ.next Φ.actual c) : (X.stage c).fiberDim (resAt P) ≤ 3 := by
  by_cases h1 : 1 < (X.stage c).fiberDim (resAt P)
  · obtain ⟨p, -, Y, -, hS⟩ := X.step c hc h1
    have hn := X.successor_dimension_le_one hc _ hS
    have hd := Y.toStepData.toStep.toNonquadDims.drop
    omega
  · omega

/-- **The earlier candidate has no inputs at a fibre of dimension above three**: the side
equalities of `ILSwitchInputsPK` (hence of `ILSwitchInputsA`, `ILSwitchInputsB`, and of the
nonquadratic branches of the leaves `PrimRegularityInputsILA`, `PrimRegularityInputsILB`) cannot be
met when `dim H¹` of the actual fibre exceeds three; the side models of `InnerLimitSwitchModel`
replace them. Kind: PROVED. -/
theorem no_ILSwitchInputsPK_of_large_fibre
    (h : 3 < finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1)) :
    ¬ Nonempty (ILSwitchInputsPK P Cn W hW Φ ι u) := by
  rintro ⟨X⟩
  have hb := X.reachable_dimension_le_three Reach.start
  have he := fiberDim_eq_h1 (ResAt P) (Localization.AtPrime P) F ι (resAt P)
    (X.stage Φ.actual) (Φ.fibre Φ.actual) ⟨X.model Φ.actual⟩
  omega

/-- The same for `ILSwitchInputsA` (`ILSwitchInputsA.toPK`). Kind: PROVED. -/
theorem no_ILSwitchInputsA_of_large_fibre
    (h : 3 < finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1)) :
    ¬ Nonempty (ILSwitchInputsA hmloc hmglob P Cn W hW Φ ι u) :=
  fun ⟨X⟩ => no_ILSwitchInputsPK_of_large_fibre h ⟨X.toPK⟩

/-- The same for `ILSwitchInputsB` (`ILSwitchInputsB.toA`). Kind: PROVED. -/
theorem no_ILSwitchInputsB_of_large_fibre
    (h : 3 < finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1)) :
    ¬ Nonempty (ILSwitchInputsB h410 hlcd hmloc hmglob P Cn W hW Φ ι u) :=
  fun ⟨X⟩ => no_ILSwitchInputsA_of_large_fibre h ⟨X.toA⟩

end LiteralBoundary

/-! **The leaves** -/

section Leaves

/-- **The regularity inputs on the inner-limit route with side models** (tex 4976–5200), for the
curve `E_ℓ` and the two PRINTs of residual finiteness: `u = 0` (tex 5196–5197; ELLIOT), or at every
height-one prime `𝔭 ≠ (2)` of `Λ` a configuration family `Φ` genuine at `𝔭` (`IsGenuineFamilyAt`;
GLUE) with
* `InnerLimitSwitchActual` over `Φ` starting at `u`, for a number field `K`, places `S`, the actual
  conjugation `Cn` and the curve `W = E_ℓ ⊗ K` fixed by it with full two-torsion (the address's
  curve; data and GLUE), the switches on the actual stage complexes with their links and side
  models (fields and kinds at `InnerLimitSwitchActual`, `ILStageStepLinked`,
  `ILStageStepActual`); its frame makes the specialization nonquadratic;
* or, at a quadratic specialization (tex 5005–5008), `HomologySwitchDataPK` over `Φ` (the
  homology-level mixed and single-sign switches; fields at `HomologySwitchDataPK`).

Kind: definition. -/
def RegularityInputsILM (ℓ : ℕ) (hmloc : MilneLocalFiniteness)
    (hmglob : MilneGlobalFiniteness) (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      ((∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
          (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
          (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
          W = (Ecurve ℓ).baseChange K ∧
          Nonempty (InnerLimitSwitchActual P Cn W hW hmloc hmglob Φ
            (UniformSwitch.toFracAt P) u)) ∨
        (Φ.quadratic (resAt P) ∧
          Nonempty (HomologySwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u)))

/-- **The model-level regularity inputs** (tex 4976–5200): `u = 0`, or at every height-one prime
`𝔭 ≠ (2)` a configuration family genuine at `𝔭` with `SwitchModelInputs` (homology-level
nonquadratic switches with side models) or, at a quadratic specialization,
`HomologySwitchDataPK`. The common weakening of `RegularityInputsILM` and `RegularityInputsHPK`.
Kind: definition. -/
def RegularityInputsMdl (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      (Nonempty (SwitchModelInputs Φ (UniformSwitch.toFracAt P) (resAt P) u) ∨
        (Φ.quadratic (resAt P) ∧
          Nonempty (HomologySwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u)))

variable {ℓ : ℕ} {h410 : MilneADT_I_4_10_totallyComplex} {hlcd : MilneLocalDimensionTwo}
  {hmloc : MilneLocalFiniteness} {hmglob : MilneGlobalFiniteness} {u : FractionRing Lambda}

/-- **The inner-limit inputs give the model-level inputs** (`InnerLimitSwitchActual.toInner`,
`InnerLimitSwitchModel.toModelInputs`). Kind: PROVED. -/
theorem RegularityInputsILM.toMdl (h : RegularityInputsILM ℓ hmloc hmglob u) :
    RegularityInputsMdl u := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Φ, hΦ, hb⟩ := h P hP hne
    refine ⟨Φ, hΦ, ?_⟩
    rcases hb with ⟨K, _, _, S, Cn, W, hW, _, _, -, ⟨X⟩⟩ | hq
    · exact Or.inl ⟨(X.toInner hmloc hmglob).toModelInputs⟩
    · exact Or.inr hq

/-- **The wired homology-level inputs give the model-level inputs**
(`HomologySwitchDataPK.toModelInputs` at a nonquadratic specialization). Kind: PROVED. -/
theorem RegularityInputsHPK.toMdl (h : RegularityInputsHPK u) : RegularityInputsMdl u := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Φ, hΦ, ⟨G⟩⟩ := h P hP hne
    refine ⟨Φ, hΦ, ?_⟩
    by_cases hq : Φ.quadratic (resAt P)
    · exact Or.inr ⟨hq, ⟨G⟩⟩
    · exact Or.inl ⟨G.toModelInputs hq⟩

/-- **The earlier candidate leaf's inputs give the model-level inputs**
(`ILSwitchInputsB.toInner`, and `GenuineSwitchDataPK.toHomology` at a quadratic specialization).
Kind: PROVED. -/
theorem RegularityInputsILB.toMdl (h : RegularityInputsILB h410 hlcd hmloc hmglob u) :
    RegularityInputsMdl u := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Φ, hΦ, hb⟩ := h P hP hne
    refine ⟨Φ, hΦ, ?_⟩
    rcases hb with ⟨K, _, _, S, Cn, W, hW, _, _, ⟨X⟩⟩ | ⟨hq, ⟨G⟩⟩
    · exact Or.inl ⟨X.toInner.toModelInputs⟩
    · exact Or.inr ⟨hq, ⟨G.toHomology⟩⟩

/-- **`u ∈ Λ[1/2]` from the model-level inputs** (tex 4976–5195, 5190–5194): at every height-one
prime `𝔭 ≠ (2)`, `u ∈ ι(Λ_𝔭)` (`regular_of_switchModelInputs` or `regular_of_homologyPK` over the
DVR `Λ_𝔭`), then the intersection formula. Kind: PROVED. -/
theorem RegularityInputsMdl.mem_lambdaHalf (h : RegularityInputsMdl u) :
    u ∈ lambdaHalfToFrac.range := by
  rw [mem_range_lambdaHalf_iff_forall_height_one]
  intro P _ hP hne
  rcases h with rfl | h
  · exact Subalgebra.zero_mem _
  · obtain ⟨Φ, -, hb⟩ := h P hP hne
    have := isDiscreteValuationRing_atPrime_of_height_one P hP
    rcases hb with ⟨⟨X⟩⟩ | ⟨-, ⟨G⟩⟩
    · obtain ⟨a, ha⟩ := regular_of_switchModelInputs (UniformSwitch.toFracAt_injective P)
        (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx) X
      rw [← ha]
      exact ⟨a, rfl⟩
    · obtain ⟨a, ha⟩ := regular_of_homologyPK (UniformSwitch.toFracAt_injective P)
        (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx) G
      rw [← ha]
      exact ⟨a, rfl⟩

/-- `u ∈ Λ[1/2]` from the inner-limit inputs. Kind: PROVED. -/
theorem RegularityInputsILM.mem_lambdaHalf (h : RegularityInputsILM ℓ hmloc hmglob u) :
    u ∈ lambdaHalfToFrac.range :=
  h.toMdl.mem_lambdaHalf

variable (D : RCData ℓ)

/-- **The height-one leaf on the inner-limit route with side models** (tex 4976–5200, at the ring
instances of the final field): the two PRINTs, and for every final family `F` and address `x` a
`u ∈ Frac Λ` with `IsTExpansion u (D.uPrim F x)` (tex 3877–3892; GLUE) and
`RegularityInputsILM ℓ … u`. Kind: definition. -/
def PrimRegularityInputsILM : Prop :=
  ∃ (hmloc : MilneLocalFiniteness) (hmglob : MilneGlobalFiniteness),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧
        RegularityInputsILM ℓ hmloc hmglob u

/-- **The model-level height-one leaf**: for every final family and address a `t`-expansion `u`
with `RegularityInputsMdl u`. Kind: definition. -/
def PrimRegularityInputsMdl : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧ RegularityInputsMdl u

/-- The inner-limit leaf gives the model-level leaf. Kind: PROVED. -/
theorem PrimRegularityInputsILM.toMdl (h : PrimRegularityInputsILM D) :
    PrimRegularityInputsMdl D := by
  obtain ⟨_, _, h⟩ := h
  intro Co Ce F hF x
  obtain ⟨u, hT, hu⟩ := h Co Ce F hF x
  exact ⟨u, hT, hu.toMdl⟩

/-- The wired leaf gives the model-level leaf. Kind: PROVED. -/
theorem PrimRegularityInputsHPK.toMdl (h : PrimRegularityInputsHPK D) :
    PrimRegularityInputsMdl D := by
  intro Co Ce F hF x
  obtain ⟨u, hT, hu⟩ := h Co Ce F hF x
  exact ⟨u, hT, hu.toMdl⟩

/-- The earlier candidate leaf (round 12) gives the model-level leaf. Kind: PROVED. -/
theorem PrimRegularityInputsILB.toMdl (h : PrimRegularityInputsILB D) :
    PrimRegularityInputsMdl D := by
  obtain ⟨_, _, _, _, h⟩ := h
  intro Co Ce F hF x
  obtain ⟨u, hT, hu⟩ := h Co Ce F hF x
  exact ⟨u, hT, hu.toMdl⟩

/-- **`PrimRegularityInputs` from the model-level leaf**: every primitive coordinate is in
`Λ[1/2]`. Kind: PROVED. -/
theorem primRegularityInputs_of_Mdl (h : PrimRegularityInputsMdl D) : PrimRegularityInputs D := by
  apply (primRegularityInputs_iff D).mpr
  intro Co Ce F hF x
  obtain ⟨u, hT, hu⟩ := h Co Ce F hF x
  exact inLamHalf_of_isTExpansion hT hu.mem_lambdaHalf

/-- **`PrimRegularityInputs` from the inner-limit leaf** (the form consumed by the base-zero step).
Kind: PROVED. -/
theorem primRegularityInputs_of_ILM (h : PrimRegularityInputsILM D) : PrimRegularityInputs D :=
  primRegularityInputs_of_Mdl D h.toMdl

/-- **`RCSteps.height_one`** from the inner-limit leaf and (4.7). Kind: PROVED (from the inputs). -/
theorem heightOneTarget_of_ILM (h : PrimRegularityInputsILM D) (h47 : CommonCoordinateTarget D) :
    HeightOneTarget D :=
  heightOneTarget_of_inputs D (primRegularityInputs_of_ILM D h) h47

/-- **Degenerate satisfiability**: given the two PRINTs, the leaf holds when the primitive
coordinates vanish (the `u = 0` branch). Kind: PROVED. -/
theorem primRegularityInputsILM_of_uPrim_zero (hmloc : MilneLocalFiniteness)
    (hmglob : MilneGlobalFiniteness) (hD : ∀ F x, D.uPrim F x = 0) :
    PrimRegularityInputsILM D :=
  ⟨hmloc, hmglob, fun _ _ F _ x =>
    ⟨0, by rw [hD F x]; exact isTExpansion_zero, Or.inl rfl⟩⟩

end Leaves

end ZInQ.Manuscript.RC.Wiring
