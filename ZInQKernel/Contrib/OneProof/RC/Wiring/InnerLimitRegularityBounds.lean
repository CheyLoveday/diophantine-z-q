import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularityLeaf
import ZInQKernel.Contrib.RC53Assist.ResidualBounds.StageBounds

/-!
# Theorem 5.3, Lane RC0 round 12: the rank bounds of the inner-limit leaf discharged

Lemma `ex:limits-inner-limit` (tex 4385–4451; tex 4400–4406: "a tuple whose model ranks are
bounded"). The inputs of one switch with the actual stage complexes (`ILStageStepActual`) carry the
range `lo, hi` and the uniform bound `B` of the residual ranks of the stage complexes as ELLIOT
fields. The RC53 group's stage bounds (`RC53Assist/ResidualBounds/StageBounds.lean`) prove them for
the actual stage Selmer complexes with the standard old conditions, from the finiteness and
dimension PRINTs: the range `[0, 3]` (`actualStageSelmer_hbdd`) and the bound
`oldSelmerRankBound` (`actualStandardOldSelmer_hB`).

Scope of the discharge (the cases covered):
* fixed supports `S₀ ⊆ S` at every stage (the coefficient support `S₀` and the Selmer support `S`
  do not move with `i`), `S` finite and containing the primes above `2`, `K` totally complex, and
  `E[2^i]` defined over `K_{S₀}` for every `i`;
* the old conditions at `S₀` are the standard ones (`standardOldAt`): at each stage and each place a
  label chooses the zero condition, the full condition or a Kummer condition (attached to an
  elliptic curve over `K_v` and an equivariant map from its `m_i`-torsion); arbitrary old condition
  complexes (`CondAt`) are NOT covered;
* the unramified conditions at the places of `S − S₀`, as in `actualSelData`.

`ILStageStepActualB` is `ILStageStepActual` in this setting, without `lo`, `hi`, `hbdd`, `B`, `hB`
(PROVED, with `lo = 0`, `hi = 3`, `B = oldSelmerRankBound`) and without `hcres` (PROVED for the
standard old conditions from Milne I.2.3, `standardOldAt_residualCohomologyFinite`). The flat terms
of the old conditions are PROVED for the zero and full conditions and remain an input only for the
Kummer conditions (`hcflatK`). The PRINTs are explicit inputs of `toILStageStepActual`: Milne I.2.3
and I.4.10 (`MilneLocalFiniteness`, `MilneGlobalFiniteness`), the totally complex form of I.4.10
(`MilneADT_I_4_10_totallyComplex`) and the local cohomological dimension two (Remark 1.12,
`MilneLocalDimensionTwo`).

The candidate leaf `PrimRegularityInputsILB` takes the switches in this form;
`PrimRegularityInputsILB.toILA` gives `PrimRegularityInputsILA`, so the consumers of
`prim_regular` carry over (`heightOneTarget_of_inputsILB`, `primRegularityInputs_of_ILB`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (SwitchFamily Reach fiberH1 twoTermFiberComplex)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages fibreLimitGlobal
  limitRelaxed finiteLimitSide singularLimitSide Vec2)
open ZInQ.Manuscript.RC.FibreDuality (RetainedLimitPairingStages RetainedGlobalDualityStages
  conjMatrix transportedPairing localPairingOfMat splitSelData stageLocMat
  stageA_isNilpotent_maximalIdeal)
open ZInQ.Manuscript.RC.Limits (residualCohomologyAt StageA stageMap stageIdeal)
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane)
open ZInQ.Manuscript.RC.CoefModules (ActualConj CondAt MinS Mcoef IsOpenKer FullTorsion
  actualSelData fullAt zeroAt)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Manuscript.RC.SelmerComplex (GKS Places Gloc locMap ResMod)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (ResidualCohomologyFinite MilneLocalFiniteness
  MilneGlobalFiniteness LocalDegreeTwoCoordinate)
open ZInQ.Contrib.RC53Assist.ResidualFiniteness (localCx_residualCohomologyFinite
  residualCohomologyFinite_zeroCx residualCohomologyFinite_cocycleCondition)
open ZInQ.Contrib.RC53Assist.ResidualBounds (standardOldAt standardOldAt_amplitude
  actualStageSelmer_hbdd actualStandardOldSelmer_hB oldSelmerRankBound MilneLocalDimensionTwo)
open ZInQ.Contrib.CloudB3RC53.RankCounts (MilneADT_I_4_10_totallyComplex)
open ZInQ.Manuscript.RC.CoefModules (TorsAlg)

/-! **The standard old conditions** -/

section OldConditions

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]

/-- **The standard old conditions have finite residual cohomology** (zero condition: zero terms;
full condition and Kummer conditions: Milne I.2.3, through `localCx_residualCohomologyFinite` and
`residualCohomologyFinite_cocycleCondition`). Kind: PROVED (from the PRINT). -/
theorem standardOldAt_residualCohomologyFinite (hloc : MilneLocalFiniteness) (v : Places K S)
    [DecidableEq (v.1.adicCompletion K)] (label : ℕ)
    (E : WeierstrassCurve (v.1.adicCompletion K)) [E.IsElliptic] (m : ℕ) [NeZero m]
    (ιK : TorsAlg (v.1.adicCompletion K) E m →+ ResMod (locMap K S v.1) (MinS hS W i α))
    (hιK : ∀ (g : Gloc K v.1) t, ιK (g • t) = g • ιK t) :
    ResidualCohomologyFinite
      (standardOldAt K S (Acoef i) (MinS hS W i α) v label E m ιK hιK).U := by
  have _ : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  unfold standardOldAt
  split_ifs with h0 h1
  · exact residualCohomologyFinite_zeroCx
  · exact localCx_residualCohomologyFinite K S (MinS hS W i α) hloc v
  · have : Finite (ResMod (locMap K S v.1) (MinS hS W i α)) :=
      inferInstanceAs (Finite (MinS hS W i α))
    exact residualCohomologyFinite_cocycleCondition _ _
      (hloc K v.1 (Acoef i) (ResMod (locMap K S v.1) (MinS hS W i α)) inferInstance 1)

/-- **The zero and full standard old conditions have flat terms** (`zeroAt_free`, `fullAt_free`,
for `E[2^i]` defined over `K_{S₀}`). Kind: PROVED. -/
theorem standardOldAt_flat_of_label (hfull : FullTorsion K S₀ W (2 ^ i)) (v : Places K S)
    [DecidableEq (v.1.adicCompletion K)] (label : ℕ) (hl : label = 0 ∨ label = 1)
    (E : WeierstrassCurve (v.1.adicCompletion K)) [E.IsElliptic] (m : ℕ) [NeZero m]
    (ιK : TorsAlg (v.1.adicCompletion K) E m →+ ResMod (locMap K S v.1) (MinS hS W i α))
    (hιK : ∀ (g : Gloc K v.1) t, ιK (g • t) = g • ιK t) (n : ℤ) :
    Module.Flat (Acoef i)
      ((standardOldAt K S (Acoef i) (MinS hS W i α) v label E m ιK hιK).U.X n) := by
  have _ : Module.Free (Acoef i) (Mcoef K S₀ W i α) := mcoef_free W i α hfull
  have _ : Module.Flat (Acoef i) (MinS hS W i α) :=
    inferInstanceAs (Module.Flat (Acoef i) (Mcoef K S₀ W i α))
  rcases hl with rfl | rfl
  · have e : standardOldAt K S (Acoef i) (MinS hS W i α) v 0 E m ιK hιK =
        zeroAt K S (Acoef i) (MinS hS W i α) v :=
      rfl
    rw [e]
    have := zeroAt_free (k := Acoef i) (S := S) (MinS hS W i α) v n
    infer_instance
  · have e : standardOldAt K S (Acoef i) (MinS hS W i α) v 1 E m ιK hιK =
        fullAt K S (Acoef i) (MinS hS W i α) v :=
      rfl
    rw [e]
    have := fullAt_free (k := Acoef i) (stageA_isNilpotent_maximalIdeal i) (MinS hS W i α) v n
    infer_instance

end OldConditions

/-! **One switch with the rank bounds discharged** -/

section Std

variable {K : Type} [Field K] [NumberField K] {S₀ Ssel : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ Ssel) (W : WeierstrassCurve K) [W.IsElliptic]
  (α : ∀ i, GKS K S₀ →* (Acoef i)ˣ) [hα : ∀ i, IsOpenKer (α i)]
  (Bv : ∀ v : Places K Ssel, WeierstrassCurve (v.1.adicCompletion K)) [hBv : ∀ v, (Bv v).IsElliptic]
  (label : ℕ → Places K Ssel → ℕ) (m : ℕ → ℕ) [hm : ∀ i, NeZero (m i)]
  (ιK : ∀ i (v : Places K Ssel), TorsAlg (v.1.adicCompletion K) (Bv v) (m i) →+
    ResMod (locMap K Ssel v.1) (MinS hS W i (α i)))
  (hιK : ∀ i (v : Places K Ssel) (g : Gloc K v.1) t, ιK i v (g • t) = g • ιK i v t)

open Classical in
/-- **The standard old conditions at every stage** (`standardOldAt`, chosen by `label`), as the old
conditions of `actualStageCx` with the constant supports. Kind: definition. -/
def stdOldConditions : ∀ i, ∀ v : Places K ((fun _ : ℕ => Ssel) i), v.1 ∈ (fun _ : ℕ => S₀) i →
    CondAt K ((fun _ : ℕ => Ssel) i) (Acoef i) (MinS ((fun _ : ℕ => hS) i) W i (α i)) v :=
  fun i v _ => standardOldAt K Ssel (Acoef i) (MinS hS W i (α i)) v (label i v) (Bv v) (m i)
    (ιK i v) (hιK i v)

/-- The actual stage complexes with the standard old conditions. Kind: definition. -/
abbrev stdStageCx : ∀ i, GCx (StageA i) :=
  actualStageCx W (fun _ : ℕ => hS) α (stdOldConditions hS W α Bv label m ιK hιK)

end Std

/-! **One switch with the rank bounds discharged** -/

section Step

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

open Classical in
/-- **The inputs of one switch on the inner-limit route, with the rank bounds discharged** (tex
4385–4451, 4834–4907, 5027–5086): the fields of `ILStageStepActual` with fixed supports
`S₀ ⊆ Ssel`, the standard old conditions at `S₀` (`stdOldConditions`, chosen by `label`), and
without `lo`, `hi`, `hbdd`, `B`, `hB`, `hcres` (PROVED from the PRINTs, see the module docstring).
Fields (kind; tex):
* `S₀`, `Ssel`, `hS`, `hSfin`, `h2`, `hK`: the supports (data), `Ssel` finite and containing the
  primes above `2`, `K` totally complex (GLUE, conditions on the data; tex 3442, 3458–3463,
  4526, 4547);
* `α`, `hα`: the characters `α_i` with open kernel (data; tex 2781–2796);
* `hTor`: `E[2^i]` defined over `K_{S₀}` for every `i` (GLUE, Néron–Ogg–Shafarevich;
  tex 2725–2727);
* `Bv`, `hBv`, `label`, `m`, `hm`, `ιK`, `hιK`: the standard old conditions: the label (`0` zero,
  `1` full, otherwise Kummer) and the Kummer data at each place (data; tex 2743–2760, 4883–4885);
* `hcflatK`: the Kummer conditions have flat terms (OPEN; the zero and full conditions are
  PROVED, `standardOldAt_flat_of_label`);
* `q`, `eM`, `cmp`, `hcmp`, `U`, `hU`, `Uc`, `ιc`, `Q`, `tr`, `htr`, `hdual`, `C`, `D`, `E`,
  `hlift`, `hrank`, `hrankB`, `ε₀`, `ε₂`, `ε`, `σ`, `hε₂`, `hε`, `hσ`, `hloc`, `hdet`, `φ`, `φ'`:
  as in `ILStageStepActual` (kinds there), on the stage complexes `stdStageCx`, with `hrankB`
  against `oldSelmerRankBound`. -/
structure ILStageStepActualB (Z₀ Z₁ : TwoTermStage ι) where
  /-- The coefficient support. -/
  S₀ : Set (HeightOneSpectrum (𝓞 K))
  /-- The Selmer support. -/
  Ssel : Set (HeightOneSpectrum (𝓞 K))
  hS : S₀ ⊆ Ssel
  /-- The Selmer support is finite. -/
  hSfin : Ssel.Finite
  /-- The Selmer support contains the primes above `2`. -/
  h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ Ssel
  /-- `K` is totally complex. -/
  hK : IsTotallyComplex K
  /-- The characters `α_i`. -/
  α : ∀ i, GKS K S₀ →* (Acoef i)ˣ
  [hα : ∀ i, IsOpenKer (α i)]
  /-- `E[2^i]` is defined over `K_{S₀}`. -/
  hTor : ∀ i, FullTorsion K S₀ W (2 ^ i)
  /-- The curves of the Kummer conditions. -/
  Bv : ∀ v : Places K Ssel, WeierstrassCurve (v.1.adicCompletion K)
  [hBv : ∀ v, (Bv v).IsElliptic]
  /-- The labels of the old conditions: `0` zero, `1` full, otherwise Kummer. -/
  label : ℕ → Places K Ssel → ℕ
  /-- The torsion levels of the Kummer conditions. -/
  m : ℕ → ℕ
  [hm : ∀ i, NeZero (m i)]
  /-- The equivariant maps of the Kummer conditions. -/
  ιK : ∀ i (v : Places K Ssel), TorsAlg (v.1.adicCompletion K) (Bv v) (m i) →+
    ResMod (locMap K Ssel v.1) (MinS hS W i (α i))
  hιK : ∀ i (v : Places K Ssel) (g : Gloc K v.1) t, ιK i v (g • t) = g • ιK i v t
  /-- The Kummer conditions have flat terms. -/
  hcflatK : ∀ i [NeZero i] (v : Places K Ssel) (h : v.1 ∈ S₀) (n : ℤ), label i v ≠ 0 →
    label i v ≠ 1 → Module.Flat (Acoef i)
      (((stdOldConditions hS W α Bv label m ιK hιK) i v h).U.X n)
  /-- The stage primes. -/
  q : ℕ → HeightOneSpectrum (𝓞 K)
  /-- A basis `M_i ≃ A_i²`. -/
  eM : ∀ i [NeZero i], stageLocMod W (fun _ : ℕ => hS) α i (q i) ≃ₗ[Acoef i] Vec2 (Acoef i)
  /-- The comparison of the actual local cochains at `q i` with the split model. -/
  cmp : ∀ i [NeZero i], GHom (stageLocalCx W (fun _ : ℕ => hS) α i (q i))
    (splitLocalComplex (StageA i))
  /-- Its degree-two part is a degree-two coordinate `H²(K_{q_i}, M_i) ≅ M_i`. -/
  hcmp : ∀ i [NeZero i], LocalDegreeTwoCoordinate (R := Acoef i) (G := Gloc K (q i))
    (M := stageLocMod W (fun _ : ℕ => hS) α i (q i)) ((eM i).symm.toLinearMap ∘ₗ (cmp i).f 2 2 rfl)
  /-- The ultrafilter of the inner limit. -/
  U : Ultrafilter ℕ
  hU : (U : Filter ℕ) ≤ cofinite
  /-- The local condition at the stage prime. -/
  Uc : ∀ i, GCx (StageA i)
  /-- The local condition map into the split local model. -/
  ιc : ∀ i, GHom (Uc i) (splitLocalComplex (StageA i))
  /-- The Selmer pairing datum with the split local model. -/
  Q : ∀ i, SelPairData
    (splitSelData (stdStageCx hS W α Bv label m ιK hιK i)
      (actualRes W (fun _ : ℕ => hS) α (stdOldConditions hS W α Bv label m ιK hιK) q cmp i)
      (Uc i) (ιc i))
    (splitSelData (stdStageCx hS W α Bv label m ιK hιK i)
      (actualRes W (fun _ : ℕ => hS) α (stdOldConditions hS W α Bv label m ιK hιK) q cmp i)
      (Uc i) (ιc i))
  /-- The trace. -/
  tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[StageA i] StageA i
  htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0
  /-- The global duality quasi-isomorphism at the stages. -/
  hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i)))
  /-- The retained stage complexes. -/
  C : ComplexStages (R := Lambda) stageIdeal U
  /-- The retained pairing data. -/
  D : RetainedLimitPairingStages U C
  /-- The retained global duality. -/
  E : RetainedGlobalDualityStages D
  /-- The retained local pairing lifts the stage local pairings `tr(0, · ∪ ·)`. -/
  hlift : ∀ i, i ≠ 0 → ∀ a b, (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b
  /-- The model ranks are the residual ranks of the stage complexes on a `U`-large set. -/
  hrank : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
    C.rank n = Module.finrank (ResidueField (StageA i))
      (residualCohomologyAt (stdStageCx hS W α Bv label m ιK hιK i) n)
  /-- The model ranks are bounded by the producer's bound. -/
  hrankB : ∀ n, C.rank n ≤ oldSelmerRankBound hS W Bv hSfin
  ε₀ : ResAt P
  ε₂ : ResAt P
  ε : ResAt P
  σ : ResAt P
  hε₂ : ε₂ ≠ 0
  hε : ε ≠ 0
  hσ : σ ≠ 0
  /-- The residue identity at the derivative label (tex 5037). -/
  hloc : localPairingOfMat (D.locK P) = transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P)
  /-- Detection `F ≤ U`. -/
  hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
    (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).U
  /-- The finite side and the stage `Z₀`. -/
  φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology
    1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₀
  /-- The singular side and the stage `Z₁`. -/
  φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P C)
    (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) Z₁

variable {P Cn W hW}

open Classical in
/-- **`ILStageStepActual` from the inputs with the rank bounds discharged**: constant supports,
the standard old conditions; `hcflat` from `standardOldAt_flat_of_label` (zero and full) and
`hcflatK` (Kummer); `hcres` from `standardOldAt_residualCohomologyFinite` (Milne I.2.3); `lo = 0`,
`hi = 3`, `hbdd` from the RC53 group's `actualStageSelmer_hbdd` (with `standardOldAt_amplitude`;
Milne I.4.10 in the totally complex form and the local dimension two), `B = oldSelmerRankBound`
and `hB` from `actualStandardOldSelmer_hB` (Milne I.2.3, I.4.10, the local dimension two).
Kind: PROVED (from the four PRINTs). -/
def ILStageStepActualB.toILStageStepActual (h410 : MilneADT_I_4_10_totallyComplex)
    (hlcd : MilneLocalDimensionTwo) (hmloc : MilneLocalFiniteness)
    (hmglob : MilneGlobalFiniteness) {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepActualB P Cn W hW Z₀ Z₁) : ILStageStepActual P Cn W hW Z₀ Z₁ where
  S₀ := fun _ => X.S₀
  Ssel := fun _ => X.Ssel
  hS := fun _ => X.hS
  hSfin := fun _ => X.hSfin
  h2 := fun _ => X.h2
  α := X.α
  hα := X.hα
  hfull := fun i => X.hTor i
  c := stdOldConditions X.hS W X.α (hα := X.hα) X.Bv (hBv := X.hBv) X.label X.m (hm := X.hm)
    X.ιK X.hιK
  hcflat := fun i _ v h n => by
    have := X.hα i
    have := X.hBv
    have := X.hm i
    by_cases h01 : X.label i v = 0 ∨ X.label i v = 1
    · exact standardOldAt_flat_of_label X.hS W i (X.α i) (X.hTor i) v (X.label i v) h01
        (X.Bv v) (X.m i) (X.ιK i v) (X.hιK i v) n
    · exact X.hcflatK i v h n (fun e => h01 (Or.inl e)) (fun e => h01 (Or.inr e))
  hcres := fun i _ v _ => by
    have := X.hα i
    have := X.hBv
    have := X.hm i
    exact standardOldAt_residualCohomologyFinite X.hS W i (X.α i) hmloc v (X.label i v) (X.Bv v)
      (X.m i) (X.ιK i v) (X.hιK i v)
  q := X.q
  eM := X.eM
  cmp := X.cmp
  hcmp := X.hcmp
  U := X.U
  hU := X.hU
  Uc := X.Uc
  ιc := X.ιc
  Q := X.Q
  tr := X.tr
  htr := X.htr
  hdual := X.hdual
  lo := 0
  hi := 3
  hbdd := fun i _ n hn => by
    have := X.hα
    have := X.hBv
    have := X.hm
    cases i with
    | zero => exact absurd rfl (NeZero.ne 0)
    | succ j =>
      exact actualStageSelmer_hbdd X.hS (j + 1) W (X.α (j + 1)) h410 hlcd X.hK X.hSfin X.h2 _
        (fun v _ => standardOldAt_amplitude K X.Ssel (Acoef (j + 1))
          (MinS X.hS W (j + 1) (X.α (j + 1))) v (X.label (j + 1) v) (X.Bv v) (X.m (j + 1))
          (X.ιK (j + 1) v) (X.hιK (j + 1) v)) n hn
  B := oldSelmerRankBound X.hS W X.Bv X.hSfin
  hB := fun i _ n => by
    have := X.hα
    have := X.hBv
    have := X.hm
    cases i with
    | zero => exact absurd rfl (NeZero.ne 0)
    | succ j =>
      exact actualStandardOldSelmer_hB X.hS W X.Bv j (X.α (j + 1)) (X.hTor (j + 1)) (X.hTor j)
        (by simpa using X.hTor 1) h410 hlcd hmloc hmglob X.hK X.hSfin X.h2 (X.label (j + 1))
        (X.m (j + 1)) (X.ιK (j + 1)) (X.hιK (j + 1)) n
  C := X.C
  D := X.D
  E := X.E
  hlift := X.hlift
  hrank := X.hrank
  hrankB := X.hrankB
  ε₀ := X.ε₀
  ε₂ := X.ε₂
  ε := X.ε
  σ := X.σ
  hε₂ := X.hε₂
  hε := X.hε
  hσ := X.hσ
  hloc := X.hloc
  hdet := X.hdet
  φ := X.φ
  φ' := X.φ'

end Step

/-! **The family and the candidate leaf with the rank bounds discharged** -/

section Family

variable (h410 : MilneADT_I_4_10_totallyComplex) (hlcd : MilneLocalDimensionTwo)
  (hmloc : MilneLocalFiniteness) (hmglob : MilneGlobalFiniteness)
variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F]
variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **Nonquadratic switching inputs on the inner-limit route, with the rank bounds discharged**:
the fields of `ILSwitchInputsA`, with the inputs of each switch given by `ILStageStepActualB`.
Kind: definition (inputs; fields as at `ILSwitchInputsA` and `ILStageStepActualB`). -/
structure ILSwitchInputsB (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
    (ι : Localization.AtPrime P →+* F) (u : F) where
  /-- The stage two-term models. -/
  stage : Φ.Config → TwoTermStage ι
  /-- Each stage models the family's fibre. -/
  model : ∀ c, HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex (resAt P) (stage c))
  /-- The actual class. -/
  hz0 : ((model Φ.actual).hom.f 1).hom Φ.zAct = fun i => resAt P ((stage Φ.actual).z i)
  /-- The actual paired functional. -/
  hw0 : ∀ y, Φ.lamAct y = (fun i => resAt P ((stage Φ.actual).w i)) ⬝ᵥ
    (((model Φ.actual).hom.f 2).hom y : Fin _ → ResAt P)
  /-- The actual coordinate. -/
  hu0 : (stage Φ.actual).u = u
  /-- The specialization is nonquadratic. -/
  hnq : ¬ Φ.quadratic (resAt P)
  /-- The actual class of every reached configuration is nonzero (tex 4992, 5137–5144). -/
  class_ne_zero : ∀ c, Reach Φ.next Φ.actual c → ∃ i, (stage c).z i ≠ 0
  /-- The inner-limit switch steps, with sides the family's fibres. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ X : ILStageStepActualB P Cn W hW (stage c) (stage (Φ.next c p)),
        ((X.toILStageStepActual h410 hlcd hmloc hmglob).toStepData hmloc hmglob).toStep.SF.Dside =
            Φ.fibre c ∧
          ((X.toILStageStepActual h410 hlcd hmloc hmglob).toStepData hmloc
            hmglob).toStep.SS.Dside = Φ.fibre (Φ.next c p)

variable {h410 hlcd hmloc hmglob P Cn W hW}

/-- **`ILSwitchInputsA` from the inputs with the rank bounds discharged**
(`ILStageStepActualB.toILStageStepActual` at each switch). Kind: PROVED. -/
def ILSwitchInputsB.toA {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
    {ι : Localization.AtPrime P →+* F} {u : F}
    (X : ILSwitchInputsB h410 hlcd hmloc hmglob P Cn W hW Φ ι u) :
    ILSwitchInputsA hmloc hmglob P Cn W hW Φ ι u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  hnq := X.hnq
  class_ne_zero := X.class_ne_zero
  step c hc h1 := by
    obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, Y.toILStageStepActual h410 hlcd hmloc hmglob, hF, hS⟩

end Family

/-- **The height-one regularity inputs on the inner-limit route, with the rank bounds
discharged** (tex 4976–5200): as `RegularityInputsILA`, with `ILSwitchInputsB` at a nonquadratic
specialization (and `GenuineSwitchDataPK` at a quadratic one). Kind: definition. -/
def RegularityInputsILB (h410 : MilneADT_I_4_10_totallyComplex) (hlcd : MilneLocalDimensionTwo)
    (hmloc : MilneLocalFiniteness) (hmglob : MilneGlobalFiniteness)
    (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      ((∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
          (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
          (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
          Nonempty (ILSwitchInputsB h410 hlcd hmloc hmglob P Cn W hW Φ
            (UniformSwitch.toFracAt P) u)) ∨
        (Φ.quadratic (resAt P) ∧
          Nonempty (GenuineSwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u)))

/-- The inputs give `RegularityInputsILA` (`ILSwitchInputsB.toA`). Kind: PROVED. -/
theorem RegularityInputsILB.toILA {h410 : MilneADT_I_4_10_totallyComplex}
    {hlcd : MilneLocalDimensionTwo} {hmloc : MilneLocalFiniteness}
    {hmglob : MilneGlobalFiniteness} {u : FractionRing Lambda}
    (h : RegularityInputsILB h410 hlcd hmloc hmglob u) : RegularityInputsILA hmloc hmglob u := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Φ, hΦ, hb⟩ := h P hP hne
    refine ⟨Φ, hΦ, ?_⟩
    rcases hb with ⟨K, _, _, S, Cn, W, hW, _, _, ⟨X⟩⟩ | hq
    · exact Or.inl ⟨K, inferInstance, inferInstance, S, Cn, W, hW, inferInstance, inferInstance,
        ⟨X.toA⟩⟩
    · exact Or.inr hq

section HeightOneTarget

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The candidate height-one leaf on the inner-limit route, with the rank bounds discharged**
(tex 4976–5200): the four PRINTs (Milne I.2.3, I.4.10, I.4.10 in the totally complex form, the
local cohomological dimension two), and for every final family `F` and every address `x` some
`u ∈ Frac Λ` with `IsTExpansion u (D.uPrim F x)` (tex 3877–3892; GLUE) and
`RegularityInputsILB u`. Kind: definition. -/
def PrimRegularityInputsILB : Prop :=
  ∃ (h410 : MilneADT_I_4_10_totallyComplex) (hlcd : MilneLocalDimensionTwo)
    (hmloc : MilneLocalFiniteness) (hmglob : MilneGlobalFiniteness),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧
        RegularityInputsILB h410 hlcd hmloc hmglob u

/-- **The leaner leaf gives the candidate leaf of round 11** (`RegularityInputsILB.toILA` at every
address), so all its consumers carry over. Kind: PROVED. -/
theorem PrimRegularityInputsILB.toILA (h : PrimRegularityInputsILB D) :
    PrimRegularityInputsILA D := by
  obtain ⟨_, _, hmloc, hmglob, h⟩ := h
  refine ⟨hmloc, hmglob, fun Co Ce F hF x => ?_⟩
  obtain ⟨u, hT, hreg⟩ := h Co Ce F hF x
  exact ⟨u, hT, hreg.toILA⟩

/-- **`RCSteps.height_one`** from the leaner leaf and (4.7). Kind: PROVED from the inputs. -/
theorem heightOneTarget_of_inputsILB (h : PrimRegularityInputsILB D)
    (h47 : CommonCoordinateTarget D) : HeightOneTarget D :=
  heightOneTarget_of_inputsILA D h.toILA h47

/-- **The old leaf `PrimRegularityInputs D`** from the leaner leaf. Kind: PROVED. -/
theorem primRegularityInputs_of_ILB (h : PrimRegularityInputsILB D) : PrimRegularityInputs D :=
  primRegularityInputs_of_ILA D h.toILA

/-- **Degenerate satisfiability**: given the four PRINTs, the leaner leaf holds when the primitive
coordinates vanish (the `u = 0` branch). Kind: PROVED. -/
theorem primRegularityInputsILB_of_uPrim_zero (h410 : MilneADT_I_4_10_totallyComplex)
    (hlcd : MilneLocalDimensionTwo) (hmloc : MilneLocalFiniteness)
    (hmglob : MilneGlobalFiniteness) (hD : ∀ F x, D.uPrim F x = 0) :
    PrimRegularityInputsILB D :=
  ⟨h410, hlcd, hmloc, hmglob, fun _ _ F _ x =>
    ⟨0, by rw [hD F x]; exact isTExpansion_zero, Or.inl rfl⟩⟩

end HeightOneTarget

end ZInQ.Manuscript.RC.Wiring
