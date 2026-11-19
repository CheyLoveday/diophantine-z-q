import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularity
import ZInQKernel.Contrib.RC53Assist.ResidualFiniteness.StageResidual

/-!
Theorem 5.3, Lane RC0 round 11: the actual stage complexes of the inner-limit switch

Lemma `ex:limits-inner-limit` (tex 4385–4451), Lemma `ex:limits-derivative-switch`
(tex 4834–4907) and the switch at a derivative label (tex 5027–5037). The leaf `ILStageStep` of
`InnerLimitRegularity.lean` takes the stage complexes `G i` abstractly, with their flatness
`hflat` and their residual finiteness `hres` as fields. This file fixes `G` to the actual stage
Selmer complexes, proves `hflat` and `hres` from landed theorems, and ties the split-model
localization `res i` to the actual local cochains at a stage prime.

* `actualStageCx`: for `i ≠ 0`, `G i = selCx (actualSelData (hS i) W i (α i) (c i))`, the Selmer
  complex (4.3) of `M_i = (E[2^i] ⊗ A_i)(α_i)` (built over `G_{K,S₀ i}`, inflated to
  `S_i ⊇ S₀ i`) with the old conditions `c i` at `S₀ i` and the unramified conditions at
  `S_i − S₀ i` (tex 3458–3463, 3483–3497); the zero complex at `i = 0` (`A_0` is the zero ring).
  The supports may depend on `i`, so that a stage prime `q_i` may be an old place.
* `actualStageCx_flat` (`hflat`, tex 4392–4395, 4412–4414): `flat_selmerCochains`
  (`InnerLimitArith/StageFlat.lean`) for finite `S_i`, with `M_i` free (`mcoef_free`: under
  `FullTorsion`, `E(K_{S₀ i})[2^i] ≃ (ℤ/2^i)²` by `torsS_addEquiv_prod`, and
  `A_i ⊗ ℤ/2^i ≃ A_i`), the unramified conditions free (`urAt_free`) and the old conditions with
  flat terms (an explicit input, PROVED for full and zero conditions by
  `oldConditions_fullOrZero`).
* `actualStageCx_residual` (`hres`, tex 4392–4394):
  `actualStageSelmer_residualCohomologyFinite` (`ResidualFiniteness/StageResidual.lean`) from
  `MilneLocalFiniteness`, `MilneGlobalFiniteness`, finite `S_i` containing the primes above `2`
  and old conditions with finite residual cohomology.
* `stageRestrict`, `actualRes`: `res i` is the projection of the actual stage complex to the
  global cochains, restriction along `p_{q_i} : G_{K_{q_i}} → G_{K,S_i}`, and a comparison
  `cmp i` of the actual local cochains `C^•_cont(G_{K_{q_i}}, M_i)` with the split model
  `D⁰ ⊕ (F ⊕ S)[−1] ⊕ D²[−2]` whose degree-two part is a `LocalDegreeTwoCoordinate`
  (`H²(K_{q_i}, M_i) ≅ M_i`, tex 4860–4868) through a basis `M_i ≃ A_i²`.
* `ILStageStepActual`: the fields of `ILStageStep` with `G` the actual stage complexes, `res` the
  actual localization, `hflat` and `hres` removed, and the stage data as fields; the kind of
  every field is listed at the structure. `ILStageStepActual.toILStageStep` (PROVED from the two
  finiteness PRINTs) and `ILStageStepActual.toStepData`.

For the cone presentation `Cone(G_i ⊕ U_c → L_{q_i})[−1]` of `ILStageStep` the actual `G_i`
should carry no condition at `q_i`, that is the full condition: `q_i ∈ S₀ i` with `c i` the full
condition there (`M_i` is unramified at `q_i`, tex 3486–3491). With `q_i ∈ S_i − S₀ i` the
complex `G_i` is instead the one with the unramified (finite) condition at `q_i`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (fiberH1 InnerLimitStepData)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages fibreLimitGlobal
  limitRelaxed finiteLimitSide singularLimitSide Vec2)
open ZInQ.Manuscript.RC.FibreDuality (RetainedLimitPairingStages RetainedGlobalDualityStages
  conjMatrix transportedPairing localPairingOfMat splitSelData stageLocMat
  stageA_isNilpotent_maximalIdeal)
open ZInQ.Manuscript.RC.Limits (residualCohomologyAt StageA stageMap stageIdeal)
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane)
open ZInQ.Manuscript.RC.CoefModules (ActualConj CondAt MinS Mcoef CoefMod IsOpenKer FullTorsion
  actualSelData fullAt zeroAt torsS_addEquiv_prod mulZModEquiv acoefTop acoefTop_discrete urAt
  urOutside actualConditions)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Manuscript.RC.SelmerComplex (GKS Places Gloc locMap ResMod natCx contCochains
  resCochains natHom)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (ResidualCohomologyFinite MilneLocalFiniteness
  MilneGlobalFiniteness flat_selmerCochains free_contCochains free_natX LocalDegreeTwoCoordinate)
open ZInQ.Contrib.RC53Assist.ResidualFiniteness (actualStageSelmer_residualCohomologyFinite)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (frobCx rel01 frob eUr)

/-! **The actual coefficient module is free** -/

section Coefficients

variable {K : Type} [Field K] [NumberField K]

section Module

variable {S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S₀ →* (Acoef i)ˣ)

/-- **The actual coefficient module `M_i = (E[2^i] ⊗ A_i)(α)` is free of rank two over `A_i`**
when `E[2^i]` is defined over `K_{S₀}`: `E(K_{S₀})[2^i] ≃ (ℤ/2^i)²` (`torsS_addEquiv_prod`) and
`A_i ⊗_ℤ ℤ/2^i ≃ A_i` (`mulZModEquiv`). Kind: PROVED. -/
def mcoefEquiv (hfull : FullTorsion K S₀ W (2 ^ i)) :
    (Acoef i × Acoef i) ≃ₗ[Acoef i] Mcoef K S₀ W i α :=
  haveI : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  (((mulZModEquiv (Acoef i) (2 ^ i)).prodCongr (mulZModEquiv (Acoef i) (2 ^ i))).symm.trans
    (TensorProduct.prodRight ℤ (Acoef i) (Acoef i) (ZMod (2 ^ i)) (ZMod (2 ^ i))).symm).trans
    ((LinearEquiv.baseChange ℤ (Acoef i) _ _
      (torsS_addEquiv_prod W hfull).some.toIntLinearEquiv.symm).trans
      (ZInQ.Manuscript.RC.CoefModules.CoefMod.equiv (Acoef i) α _))

/-- `M_i` is a free `A_i`-module under `FullTorsion`. Kind: PROVED. -/
theorem mcoef_free (hfull : FullTorsion K S₀ W (2 ^ i)) :
    Module.Free (Acoef i) (Mcoef K S₀ W i α) :=
  Module.Free.of_equiv (mcoefEquiv W i α hfull)

end Module

variable {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [HasFullTwoTorsion K S W]

omit [NumberField K] in
/-- **The full-torsion input at coefficient supports equal to the support `S` of the `Λ`-adic
module** is the instance `HasFullTwoTorsion K S W` (a parameter of `ILStageStep`). Kind:
PROVED. -/
theorem fullTorsion_of_eq {S₀ : ℕ → Set (HeightOneSpectrum (𝓞 K))} (h : ∀ i, S₀ i = S) :
    ∀ i [NeZero i], FullTorsion K (S₀ i) W (2 ^ i) := by
  intro i _
  rw [h i]
  exact HasFullTwoTorsion.full (K := K) (S := S) (W := W) i

end Coefficients

/-! **Freeness of the local-condition terms** -/

section LocalTerms

/-- The unramified complex `[V --(Φ−1)--> V]` has free terms for a free module `V`. Kind:
PROVED. -/
theorem free_frobCx_X {k : Type} [Ring k] {V : Type} [AddCommGroup V] [Module k V]
    [Module.Free k V] (Φ : V →ₗ[k] V) (n : ℤ) : Module.Free k ((frobCx Φ).X n) := by
  change Module.Free k ((HomologicalComplex.double (ModuleCat.ofHom (Φ - 1)) rel01).X n)
  by_cases h0 : n = 0
  · subst h0
    exact Module.Free.of_equiv
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (Φ - 1)) rel01).toLinearEquiv.symm
  · by_cases h1 : n = 1
    · subst h1
      exact Module.Free.of_equiv (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Φ - 1)) rel01
        (by decide)).toLinearEquiv.symm
    · have : Subsingleton ((HomologicalComplex.double (ModuleCat.ofHom (Φ - 1)) rel01).X n) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (HomologicalComplex.isZero_double_X (ModuleCat.ofHom (Φ - 1)) rel01 n h0 h1)
      exact Module.Free.of_basis (Module.Basis.empty _ : Module.Basis Empty k _)

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S)

/-- **The unramified condition has free terms** for free coefficients. Kind: PROVED. -/
theorem urAt_free {k : Type} [CommRing k] [TopologicalSpace k] [DiscreteTopology k]
    (M₀ : Type) [AddCommGroup M₀] [Module k M₀] [DistribMulAction (GKS K S₀) M₀]
    [SMulCommClass (GKS K S₀) k M₀] [TopologicalSpace M₀] [DiscreteTopology M₀]
    [ContinuousSMul (GKS K S₀) M₀] [Finite M₀] [Module.Free k M₀] (w : Places K S)
    (hw : w.1 ∉ S₀) (n : ℤ) : Module.Free k ((urAt hS k M₀ w hw).U.X n) :=
  haveI : Module.Free k (ZInQ.Manuscript.RC.CoefModules.urRep k M₀
      (ZInQ.Manuscript.RC.CoefModules.newPlace w hw)).V :=
    inferInstanceAs (Module.Free k M₀)
  free_frobCx_X (frob (eUr K w.1) (ZInQ.Manuscript.RC.CoefModules.urRep k M₀
    (ZInQ.Manuscript.RC.CoefModules.newPlace w hw))) n

/-- **The full condition has free terms** over a local ring with nilpotent maximal ideal, for
flat coefficients (`free_contCochains`). Kind: PROVED. -/
theorem fullAt_free {k : Type} [CommRing k] [IsLocalRing k]
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal k)) (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Module.Flat k M] (v : Places K S)
    (n : ℤ) : Module.Free k ((fullAt K S k M v).U.X n) :=
  haveI : CompactSpace (Gloc K v.1) := ZInQ.Manuscript.RC.FibreDuality.compactSpace_Gloc v.1
  haveI : Module.Flat k (ResMod (locMap K S v.1) M) := inferInstanceAs (Module.Flat k M)
  free_natX _ (fun m => free_contCochains (R := k) (G := Gloc K v.1)
    (M := ResMod (locMap K S v.1) M) hnil m) n

/-- **The zero condition has free terms.** Kind: PROVED. -/
theorem zeroAt_free {k : Type} [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] (v : Places K S) (n : ℤ) :
    Module.Free k ((zeroAt K S k M v).U.X n) := by
  change Module.Free k PUnit
  infer_instance

variable (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S₀ →* (Acoef i)ˣ)
  [IsOpenKer α]

/-- **The actual local conditions have free terms**, given flat terms of the old conditions at
`S₀` and free coefficients; the unramified conditions at `S − S₀` are discharged
(`urAt_free`). Kind: PROVED. -/
theorem actualConditions_free [NeZero i] (hM : Module.Free (Acoef i) (Mcoef K S₀ W i α))
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v h (n : ℤ), Module.Flat (Acoef i) ((c v h).U.X n)) (v : Places K S) (n : ℤ) :
    letI := acoefTop i
    haveI := acoefTop_discrete i
    Module.Free (Acoef i) (((actualConditions hS W i α c).U v).X n) := by
  let _ : TopologicalSpace (Acoef i) := acoefTop i
  have _ : DiscreteTopology (Acoef i) := acoefTop_discrete i
  change Module.Free (Acoef i) ((urOutside hS (Acoef i) (Mcoef K S₀ W i α) c v).U.X n)
  unfold urOutside
  by_cases h : v.1 ∈ S₀
  · rw [dite_eq_left h]
    have := hc v h n
    exact ZInQ.Manuscript.RC.Limits.flat_module_free (stageA_isNilpotent_maximalIdeal i)
  · rw [dite_eq_right h]
    exact urAt_free hS (Mcoef K S₀ W i α) v h n

/-- **The actual stage Selmer cochain modules are flat** (`flat_selmerCochains`): finitely many
places, `M_i` free (`mcoef_free`, from `E[2^i]` defined over `K_{S₀}`), the old conditions with
flat terms. Kind: PROVED. -/
theorem actualSelmerCochains_flat [NeZero i] (hSfin : S.Finite)
    (hfull : FullTorsion K S₀ W (2 ^ i))
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v h (n : ℤ), Module.Flat (Acoef i) ((c v h).U.X n)) (n : ℤ) :
    Module.Flat (Acoef i) ((selCx (actualSelData hS W i α c)).X n) := by
  let _ : TopologicalSpace (Acoef i) := acoefTop i
  have _ : DiscreteTopology (Acoef i) := acoefTop_discrete i
  let _ : Fintype (Places K S) := hSfin.fintype
  have _ : ∀ v : Places K S, CompactSpace (Gloc K v.1) := fun v =>
    ZInQ.Manuscript.RC.FibreDuality.compactSpace_Gloc v.1
  have hM : Module.Free (Acoef i) (Mcoef K S₀ W i α) := mcoef_free W i α hfull
  have _ : Module.Flat (Acoef i) (MinS hS W i α) :=
    inferInstanceAs (Module.Flat (Acoef i) (Mcoef K S₀ W i α))
  exact flat_selmerCochains (stageA_isNilpotent_maximalIdeal i) (GKS K S)
    (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) (MinS hS W i α)
    (actualConditions hS W i α c) (actualConditions_free hS W i α hM c hc) n

end LocalTerms

/-! **Old conditions full or zero** -/

section OldConditions

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]

/-- **Full or zero old conditions** (the zero and full conditions at the other primes, tex
4883–4885, and the full condition at a stage prime): their terms are flat and their residual
cohomology is finite, so the old-condition inputs `hcflat` and `hcres` of `ILStageStepActual`
hold at the stage `i`. Kind: PROVED (Milne I.2.3 for the full condition). -/
theorem oldConditions_fullOrZero (hloc : MilneLocalFiniteness)
    (hfull : FullTorsion K S₀ W (2 ^ i))
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hfz : ∀ v h, c v h = fullAt K S (Acoef i) (MinS hS W i α) v ∨
      c v h = zeroAt K S (Acoef i) (MinS hS W i α) v) :
    (∀ v h (n : ℤ), Module.Flat (Acoef i) ((c v h).U.X n)) ∧
      ∀ v h, ResidualCohomologyFinite (c v h).U := by
  have _ : Module.Free (Acoef i) (Mcoef K S₀ W i α) := mcoef_free W i α hfull
  have _ : Module.Flat (Acoef i) (MinS hS W i α) :=
    inferInstanceAs (Module.Flat (Acoef i) (Mcoef K S₀ W i α))
  have _ : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  refine ⟨fun v h n => ?_, fun v h => ?_⟩
  · rcases hfz v h with e | e <;> rw [e]
    · have := fullAt_free (k := Acoef i) (stageA_isNilpotent_maximalIdeal i) (MinS hS W i α) v n
      infer_instance
    · have := zeroAt_free (k := Acoef i) (MinS hS W i α) v n
      infer_instance
  · rcases hfz v h with e | e <;> rw [e]
    · exact ZInQ.Contrib.RC53Assist.ResidualFiniteness.localCx_residualCohomologyFinite K S
        (MinS hS W i α) hloc v
    · exact ZInQ.Contrib.RC53Assist.ResidualFiniteness.residualCohomologyFinite_zeroCx

end OldConditions

/-! **The actual stage complexes** -/

section Stage

variable {K : Type} [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic]
  {S₀ S : ℕ → Set (HeightOneSpectrum (𝓞 K))} (hS : ∀ i, S₀ i ⊆ S i)
  (α : ∀ i, GKS K (S₀ i) →* (Acoef i)ˣ) [hα : ∀ i, IsOpenKer (α i)]
  (c : ∀ i, ∀ v : Places K (S i), v.1 ∈ S₀ i →
    CondAt K (S i) (Acoef i) (MinS (hS i) W i (α i)) v)

/-- **The actual stage complexes** `G i` (tex 4391–4406, 3458–3463): for `i ≠ 0` the actual
stage Selmer complex `C_U(G_{K,S_i}, M_i)` of `M_i = (E[2^i] ⊗ A_i)(α_i)` with the old
conditions `c i` at `S₀ i` and the unramified conditions at `S_i − S₀ i` (`actualSelData`); at
`i = 0` (where `A_0` is the zero ring) the zero complex. Kind: definition. -/
def actualStageCx : ∀ i, GCx (StageA i)
  | 0 => ZInQ.Manuscript.RC.SelmerComplex.zeroCx (StageA 0)
  | i + 1 => selCx (actualSelData (hS (i + 1)) W (i + 1) (α (i + 1)) (c (i + 1)))

theorem actualStageCx_succ (i : ℕ) :
    actualStageCx W hS α c (i + 1) =
      selCx (actualSelData (hS (i + 1)) W (i + 1) (α (i + 1)) (c (i + 1))) :=
  rfl

/-- **The actual stage complexes have flat terms** (`hflat` of `ILStageStep`; tex 4392–4395,
4412–4414: the continuous finite-coefficient cochain modules are flat): from `StageFlat.lean`
(`flat_selmerCochains`) for finite `S_i`, free `M_i` (`mcoef_free`, from `E[2^i]` defined over
`K_{S₀ i}`) and old conditions with flat terms. Kind: PROVED. -/
theorem actualStageCx_flat (hSfin : ∀ i [NeZero i], (S i).Finite)
    (hfull : ∀ i [NeZero i], FullTorsion K (S₀ i) W (2 ^ i))
    (hc : ∀ i [NeZero i] v h (n : ℤ), Module.Flat (Acoef i) ((c i v h).U.X n)) :
    ∀ i n, Module.Flat (StageA i) ((actualStageCx W hS α c i).X n)
  | 0, n => by
    change Module.Flat (StageA 0) PUnit
    infer_instance
  | i + 1, n => actualSelmerCochains_flat (hS (i + 1)) W (i + 1) (α (i + 1)) (hSfin (i + 1))
      (hfull (i + 1)) (c (i + 1)) (hc (i + 1)) n

/-- **The actual stage complexes have finite residual cohomology** (`hres` of `ILStageStep`;
tex 4392–4394): `actualStageSelmer_residualCohomologyFinite` (the base change of continuous
cochains and Milne I.2.3, I.4.10), for finite `S_i` containing the primes above `2` and old
conditions with finite residual cohomology. Kind: PROVED (from the two PRINTs). -/
theorem actualStageCx_residual (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hSfin : ∀ i [NeZero i], (S i).Finite)
    (h2 : ∀ i [NeZero i] (v : HeightOneSpectrum (𝓞 K)), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S i)
    (hc : ∀ i [NeZero i] v h, ResidualCohomologyFinite (c i v h).U) :
    ∀ i [NeZero i], ResidualCohomologyFinite (actualStageCx W hS α c i) := by
  intro i _
  cases i with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ i =>
    exact actualStageSelmer_residualCohomologyFinite (hS (i + 1)) W (i + 1) (α (i + 1)) hloc
      hglob (hSfin (i + 1)) (h2 (i + 1)) (c (i + 1)) (hc (i + 1))

/-! **Restriction to a stage prime and the split-model localization** -/

/-- The stage coefficient module `M_i` with `G_{K_q}` acting through `p_q : G_{K_q} → G_{K,S_i}`.
Kind: definition. -/
abbrev stageLocMod (i : ℕ) (q : HeightOneSpectrum (𝓞 K)) : Type :=
  ResMod (locMap K (S i) q) (MinS (hS i) W i (α i))

/-- **The actual local cochain complex** `C^•_cont(G_{K_q}, M_i)` at a prime `q`. Kind:
definition. -/
abbrev stageLocalCx (i : ℕ) (q : HeightOneSpectrum (𝓞 K)) : GCx (Acoef i) :=
  natCx (contCochains (Acoef i) (Gloc K q) (stageLocMod W hS α i q))

/-- **The restriction of the actual stage Selmer complex to a prime `q`**: the projection
`C_U → C^•_cont(G_{K,S_i}, M_i)`, `(a, u, x) ↦ a`, followed by restriction along `p_q`. Kind:
definition (a chain map). -/
def stageRestrict (i : ℕ) (q : HeightOneSpectrum (𝓞 K)) :
    GHom (selCx (actualSelData (hS i) W i (α i) (c i))) (stageLocalCx W hS α i q) :=
  ghomComp (projG _) (natHom (resCochains (k := Acoef i) (M := MinS (hS i) W i (α i))
    (locMap K (S i) q)))

/-- **The split-model localization of the actual stage complexes** at the stage primes `q i`:
restriction to `q i` followed by a comparison `cmp i` of the actual local cochains with the split
model `D⁰ ⊕ (F ⊕ S)[−1] ⊕ D²[−2]`; zero at `i = 0`. Kind: definition. -/
def actualRes (q : ℕ → HeightOneSpectrum (𝓞 K))
    (cmp : ∀ i [NeZero i], GHom (stageLocalCx W hS α i (q i)) (splitLocalComplex (StageA i))) :
    ∀ i, GHom (actualStageCx W hS α c i) (splitLocalComplex (StageA i))
  | 0 => ZInQ.Contrib.CloudB3RC53.SelmerDuality.zeroGHom _ _
  | i + 1 => ghomComp (stageRestrict W hS α c (i + 1) (q (i + 1))) (cmp (i + 1))

/-- **A retained realization of the actual stage data exists** (`exists_realization`, lane
RC31's producer, with `hflat` and `hres` PROVED by `actualStageCx_flat` and
`actualStageCx_residual`): from the stage data, the comparison at the stage primes, the Selmer
pairing data with the split local model, the duality quasi-isomorphisms and the rank bounds, there
are retained data `C`, `D`, `E` over `Λ` lifting the stage local pairings, with the model ranks
bounded by `B` and equal to the residual ranks of the actual stage complexes on a `U`-large set.
Kind: PROVED (from the two finiteness PRINTs). -/
theorem exists_realization_actual (hmloc : MilneLocalFiniteness)
    (hmglob : MilneGlobalFiniteness) (hSfin : ∀ i [NeZero i], (S i).Finite)
    (h2 : ∀ i [NeZero i] (v : HeightOneSpectrum (𝓞 K)), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S i)
    (hfull : ∀ i [NeZero i], FullTorsion K (S₀ i) W (2 ^ i))
    (hcflat : ∀ i [NeZero i] v h (n : ℤ), Module.Flat (Acoef i) ((c i v h).U.X n))
    (hcres : ∀ i [NeZero i] v h, ResidualCohomologyFinite (c i v h).U)
    (q : ℕ → HeightOneSpectrum (𝓞 K))
    (cmp : ∀ i [NeZero i], GHom (stageLocalCx W hS α i (q i)) (splitLocalComplex (StageA i)))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) (Uc : ∀ i, GCx (StageA i))
    (ιc : ∀ i, GHom (Uc i) (splitLocalComplex (StageA i)))
    (Q : ∀ i, SelPairData
      (splitSelData (actualStageCx W hS α c i) (actualRes W hS α c q cmp i) (Uc i) (ιc i))
      (splitSelData (actualStageCx W hS α c i) (actualRes W hS α c q cmp i) (Uc i) (ιc i)))
    (tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[StageA i] StageA i)
    (htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0)
    (hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i)))) (lo hi : ℤ)
    (hbdd : ∀ i [NeZero i] (n : ℤ), n < lo ∨ hi < n →
      Module.finrank (ResidueField (StageA i))
        (residualCohomologyAt (actualStageCx W hS α c i) n) = 0)
    (B : ℕ) (hB : ∀ i [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (StageA i))
        (residualCohomologyAt (actualStageCx W hS α c i) n) ≤ B) :
    ∃ (C : ComplexStages (R := Lambda) stageIdeal U) (D : RetainedLimitPairingStages U C)
      (_ : RetainedGlobalDualityStages D),
      (∀ i, i ≠ 0 → ∀ a b, (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b) ∧
      (∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
        C.rank n = Module.finrank (ResidueField (StageA i))
          (residualCohomologyAt (actualStageCx W hS α c i) n)) ∧
      ∀ n, C.rank n ≤ B :=
  exists_realization U hU (actualStageCx W hS α c) (actualStageCx_flat W hS α c hSfin hfull hcflat)
    Uc (actualRes W hS α c q cmp) ιc Q tr htr hdual
    (actualStageCx_residual W hS α c hmloc hmglob hSfin h2 hcres) lo hi hbdd B hB

end Stage

/-! **One switch on the inner-limit route with the actual stage complexes** -/

section Step

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **The inputs of one switch on the inner-limit route, with the actual stage complexes**
(tex 4385–4451, 4834–4907, 5027–5086). The fields of `ILStageStep` with `G` the actual stage
complexes (`actualStageCx`), `res` the actual localization (`actualRes`), `hflat` and `hres`
removed (PROVED: `actualStageCx_flat`, `actualStageCx_residual`). Fields (kind; tex; landed
discharge):
* `S₀`, `Ssel`, `hS`: the coefficient supports and the Selmer supports `S_i ⊇ S₀ i` (data;
  tex 3458–3463, 3483–3497);
* `hSfin`, `h2`: `S_i` finite and containing the primes above `2` (GLUE, conditions on the data;
  the hypotheses of Milne I.2.3, I.4.10, tex 3442, 4526, 4547);
* `α`, `hα`: the characters `α_i = χ_hΨ_i` with open kernel (data; tex 2781–2796);
* `hfull`: `E[2^i]` defined over `K_{S₀ i}` (GLUE, Néron–Ogg–Shafarevich; tex 2725–2727;
  `fullTorsion_of_eq` when `S₀ i = S`);
* `c`: the old conditions at `S₀ i` (data; tex 2743–2760, 3483–3497);
* `hcflat`: the old conditions have flat terms (OPEN in general; tex 4392–4395; PROVED for full
  and zero conditions, `oldConditions_fullOrZero`; open for the Kummer conditions);
* `hcres`: the old conditions have finite residual cohomology (OPEN in general; PROVED for full
  and zero conditions, `oldConditions_fullOrZero`; for cocycle conditions, among them the Kummer
  conditions, `residualCohomologyFinite_cocycleCondition` from Milne I.2.3);
* `q`: the stage primes `q_i` (data; tex 4809–4830, 5027–5037; the stage primes of an arithmetic
  label);
* `eM`: a basis `M_i ≃ A_i²` (data; one exists under `hfull`, `mcoefEquiv`);
* `cmp`: a comparison of the actual local cochains at `q_i` with the split model (GLUE; tex
  4859–4868);
* `hcmp`: its degree-two part is a degree-two coordinate `H²(K_{q_i}, M_i) ≅ M_i`
  (`LocalDegreeTwoCoordinate`; OPEN; tex 4860–4868). A normalization by the tame cup product
  (`LocalDegreeTwoNormalized`) certifies nothing alone and may only be added beside this field;
* `U`, `hU`: the ultrafilter of the inner limit (data; tex 5030–5032);
* `Uc`, `ιc`: the condition at `q_i` in the split model (data; tex 4859–4868);
* `Q`: the Selmer pairing datum of the split Selmer data with itself (GLUE; tex 4385–4388,
  4859–4873); a same-condition pairing datum needs self-isotropy of `Uc i` (the plane conditions
  are self-orthogonal, tex 4873), which strict/relaxed orthogonality does not replace;
* `tr`, `htr`: a trace on the compact cone of `Q i` killing coboundaries (GLUE;
  `exists_stageTrace` produces a trace for the actual global Galois pairing data, not for `Q i`);
* `hdual`: the global duality map of `Q i` is a quasi-isomorphism (PRINT shape, Nekovář 5.4.3 at
  `A_i`; not discharged: `stageGlobalDuality` is about the actual global Galois cochains and the
  compact complex of the dual module, not about the self-paired split Selmer data at `q_i`);
* `lo`, `hi`, `hbdd`, `B`, `hB`: bounded residual cohomology and a uniform rank bound (ELLIOT;
  tex 4401–4402);
* `C`, `D`, `E`, `hlift`, `hrank`, `hrankB`: a retained realization (data; one exists from the
  fields above, `exists_realization_actual`);
* `ε₀`, `ε₂`, `ε`, `σ`, `hε₂`, `hε`, `hσ`, `hloc`: the residue identity at the derivative label
  (ELLIOT; tex 5027–5037, 2816–2820, 4888–4890);
* `hdet`: the detection `F ≤ U` (GLUE; tex 5055–5072);
* `φ`, `φ'`: the side-to-stage isomorphisms (GLUE; tex 5040–5054). -/
structure ILStageStepActual (Z₀ Z₁ : TwoTermStage ι) where
  /-- The coefficient supports `S₀ i`. -/
  S₀ : ℕ → Set (HeightOneSpectrum (𝓞 K))
  /-- The Selmer supports `S_i ⊇ S₀ i`. -/
  Ssel : ℕ → Set (HeightOneSpectrum (𝓞 K))
  hS : ∀ i, S₀ i ⊆ Ssel i
  /-- The Selmer supports are finite. -/
  hSfin : ∀ i [NeZero i], (Ssel i).Finite
  /-- The Selmer supports contain the primes above `2`. -/
  h2 : ∀ i [NeZero i] (v : HeightOneSpectrum (𝓞 K)), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ Ssel i
  /-- The characters `α_i` of the coefficient modules. -/
  α : ∀ i, GKS K (S₀ i) →* (Acoef i)ˣ
  hα : ∀ i, IsOpenKer (α i)
  /-- `E[2^i]` is defined over `K_{S₀ i}`. -/
  hfull : ∀ i [NeZero i], FullTorsion K (S₀ i) W (2 ^ i)
  /-- The old conditions at `S₀ i`. -/
  c : ∀ i, ∀ v : Places K (Ssel i), v.1 ∈ S₀ i →
    CondAt K (Ssel i) (Acoef i) (MinS (hS i) W i (α i)) v
  /-- The old conditions have flat terms. -/
  hcflat : ∀ i [NeZero i] v h (n : ℤ), Module.Flat (Acoef i) ((c i v h).U.X n)
  /-- The old conditions have finite residual cohomology. -/
  hcres : ∀ i [NeZero i] v h, ResidualCohomologyFinite (c i v h).U
  /-- The stage primes. -/
  q : ℕ → HeightOneSpectrum (𝓞 K)
  /-- A basis `M_i ≃ A_i²`. -/
  eM : ∀ i [NeZero i], stageLocMod W hS α i (q i) ≃ₗ[Acoef i] Vec2 (Acoef i)
  /-- The comparison of the actual local cochains at `q i` with the split model. -/
  cmp : ∀ i [NeZero i], GHom (stageLocalCx W hS α i (q i)) (splitLocalComplex (StageA i))
  /-- Its degree-two part is a degree-two coordinate `H²(K_{q_i}, M_i) ≅ M_i`. -/
  hcmp : ∀ i [NeZero i], LocalDegreeTwoCoordinate (R := Acoef i) (G := Gloc K (q i))
    (M := stageLocMod W hS α i (q i)) ((eM i).symm.toLinearMap ∘ₗ (cmp i).f 2 2 rfl)
  /-- The ultrafilter of the inner limit. -/
  U : Ultrafilter ℕ
  hU : (U : Filter ℕ) ≤ cofinite
  /-- The local condition at the stage prime. -/
  Uc : ∀ i, GCx (StageA i)
  /-- The local condition map into the split local model. -/
  ιc : ∀ i, GHom (Uc i) (splitLocalComplex (StageA i))
  /-- The Selmer pairing datum with the split local model. -/
  Q : ∀ i, SelPairData
    (splitSelData (actualStageCx W hS α c i) (actualRes W hS α c q cmp i) (Uc i) (ιc i))
    (splitSelData (actualStageCx W hS α c i) (actualRes W hS α c q cmp i) (Uc i) (ιc i))
  /-- The trace. -/
  tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[StageA i] StageA i
  htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0
  /-- The global duality quasi-isomorphism at the stages. -/
  hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i)))
  lo : ℤ
  hi : ℤ
  /-- Bounded residual cohomology. -/
  hbdd : ∀ i [NeZero i] (n : ℤ), n < lo ∨ hi < n →
    Module.finrank (ResidueField (StageA i))
      (residualCohomologyAt (actualStageCx W hS α c i) n) = 0
  /-- The uniform rank bound. -/
  B : ℕ
  hB : ∀ i [NeZero i] (n : ℤ),
    Module.finrank (ResidueField (StageA i))
      (residualCohomologyAt (actualStageCx W hS α c i) n) ≤ B
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
      (residualCohomologyAt (actualStageCx W hS α c i) n)
  hrankB : ∀ n, C.rank n ≤ B
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

/-- **`ILStageStep` from the actual inputs**: `G` is the actual stage complexes, `hflat` and
`hres` are proved (`actualStageCx_flat`, `actualStageCx_residual`), `res` is restriction to the
stage primes followed by the comparison. Kind: PROVED (from the two finiteness PRINTs). -/
def ILStageStepActual.toILStageStep (hmloc : MilneLocalFiniteness)
    (hmglob : MilneGlobalFiniteness) {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepActual P Cn W hW Z₀ Z₁) : ILStageStep P Cn W hW Z₀ Z₁ where
  U := X.U
  hU := X.hU
  G := actualStageCx W X.hS X.α X.c (hα := X.hα)
  hflat := actualStageCx_flat W X.hS X.α X.c (hα := X.hα) X.hSfin X.hfull X.hcflat
  Uc := X.Uc
  res := actualRes W X.hS X.α X.c (hα := X.hα) X.q X.cmp
  ιc := X.ιc
  Q := X.Q
  tr := X.tr
  htr := X.htr
  hdual := X.hdual
  hres := actualStageCx_residual W X.hS X.α X.c (hα := X.hα) hmloc hmglob X.hSfin X.h2 X.hcres
  lo := X.lo
  hi := X.hi
  hbdd := X.hbdd
  B := X.B
  hB := X.hB
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

/-- The inner-limit step data of the RC53 group from the actual inputs. Kind: PROVED. -/
def ILStageStepActual.toStepData (hmloc : MilneLocalFiniteness)
    (hmglob : MilneGlobalFiniteness) {Z₀ Z₁ : TwoTermStage ι}
    (X : ILStageStepActual P Cn W hW Z₀ Z₁) : InnerLimitStepData P Z₀ Z₁ :=
  (X.toILStageStep hmloc hmglob).toStepData

end Step

end ZInQ.Manuscript.RC.Wiring
