import ZInQKernel.Contrib.OneProof.RC.Wiring.Even
import ZInQKernel.Contrib.OneProof.RC.Wiring.Odd
import ZInQKernel.Contrib.OneProof.RC.Wiring.OddMinimum
import ZInQKernel.Contrib.OneProof.RC.Wiring.EvenUpper
import ZInQKernel.Contrib.OneProof.RC.Wiring.Clearing
import ZInQKernel.Contrib.OneProof.RC.Wiring.Genuine
import ZInQKernel.Contrib.OneProof.RC.Wiring.Address
import ZInQKernel.Contrib.OneProof.RC.Wiring.Height
import ZInQKernel.Contrib.OneProof.RC.Boolean.Node
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Uses
import ZInQKernel.Contrib.CloudB3RC53.KummerCorankZero.Basic
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Node34

/-!
# Theorem 5.3, Lane RC0 round 2: every remaining hypothesis in one structure

`restrictedConverseGenuine_of_leaves : Prints → RCLeaves → RestrictedConverseGenuine` (PROVED,
standard axioms). `RCLeaves` collects every hypothesis that remains after the lanes' results are
wired in; each field carries its tex lines, kind and owner. The deduction, for each admissible `ℓ`
with Selmer corank one:

1. root number `−1` (the blueprint's `rootNumberNode_proof`, Dokchitser–Dokchitser);
2. a genus partner `h_*` (lane RC13's `genusPartner`, via `exists_genusPartner`; Hoffstein–Luo and
   BFH's twist sign from lane RC8's literal prints with lane RC18's proved `twistDictionary`);
3. the attained odd minimum `δ_o` (batch 3's (F.4)–(F.6), `exists_oddMinimum`, from the fixed
   visible witness);
4. the thirteen steps `RCSteps` of the skeleton, each a theorem from the leaves and the lanes'
   results (`rcSteps_of_leaves`): `lstar_ne_zero_iff` (RC11), `genus_partner` (RC13),
   `visibility` (RC12), `companion` (from the leaf and RC11), `gz_comparison` (leaf),
   `final_family` (batch 3's `finalFamilyField_proof`, with (F.3) from RC13's `roughCompanion`,
   (3.3b) from RC2's `even_upper_valuation`, (3.5) from RC16 over RC20's genuine `𝒪`, and the
   address input from RC2's `addressInput_of_address` with batch 3's coefficient dictionary and
   RC3's K-split seed), `calibration`, `common_coordinate`, `base_zero` (RC15, base zero over RC20's
   genuine `Λ_(t)`), `height_one` (RC16 with (4.7)), `clearing` (RC7 with batch 3's
   PairedFunctional);
5. the skeleton's Branch 1 / fixed-field package (`rc_of_oddEmptyUnit`, `fixedFieldPackage_of_steps`),
   with the Kummer sequence in rank zero proved by batch 3 (`kummerCorankZero_proof`);
6. the blueprint's assembly with the missing-address node proved by lane RC1.

No field relies on batch 3's SelmerDuality statements (reviewed as GLUE).

**Which theorem carries the reduction.** Given `Prints`, the blueprint's `BranchPackageNode` is
equivalent to Theorem 5.3 (its coefficient data are existential and not tied to `ũ_x`). The
faithful reduction of Theorem 5.3 to Elliot's steps is `restrictedConverseGenuine_of_leaves` here
(and `RC/Assembly.lean`'s `restrictedConverseGenuine_of_steps'`): the step `RCSteps.clearing`,
discharged here from lane RC7, ties `C.u x j = [tʲ] ũ_x`. Claims about the reduction cite these.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

/-! ## Choices substituted into the data -/

/-- The data with the genus partner `h_*` substituted. -/
def WData.withHstar {ℓ : ℕ} (W : WData ℓ) (h : ℤ) : WData ℓ := { W with hstar := h }

/-- The data with the genus partner `h_*` and the odd minimum `δ_o` substituted. -/
def WData.withChoices {ℓ : ℕ} (W : WData ℓ) (h δ : ℤ) : WData ℓ :=
  { W with hstar := h, δo := δ }

/-- The depth set of the odd coefficients of the data (it does not involve `h_*` or `δ_o`). -/
def WData.depthSet {ℓ : ℕ} (W : WData ℓ) : Set ℤ :=
  AppGEndpoints.DepthSet W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd)) W.admissible

/-! ## The final companion -/

/-- **The final companion, as a leaf** (tex 2595–2603): in Branch 2, `k < 0` squarefree,
`k ≠ −1, −3`, its primes in the fixed support, `k ≡ 1 (mod 4)`, a unit square at every prime of `2N`,
prime to `h_*`, and `L_*(k) ≠ 0`. -/
def CompanionLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ¬ W.OddEmptyUnit → W.kfin < 0 ∧ Squarefree W.kfin ∧ W.kfin ≠ -1 ∧ W.kfin ≠ -3 ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.kfin → p ∈ W.S) ∧ W.kfin % 4 = 1 ∧
    (∀ p : ℕ, p.Prime → p ∣ 2 * CST.newformLevel (Ecurve ℓ) → UnitSquareAt p W.kfin) ∧
    IsCoprime W.kfin W.hstar ∧ W.Lstar W.kfin ≠ 0

/-- **`RCSteps.companion`** from the leaf and the normalization of `L_*` (PROVED). -/
theorem companionTarget_of {ℓ : ℕ} {W : WData ℓ} (hL : LstarTarget W.toRCData)
    (h : CompanionLeaf W) : CompanionTarget W.toRCData := fun hU => by
  obtain ⟨hneg, hsf, h1, h3, hS, h4, h2N, hcop, hLk⟩ := h hU
  exact ⟨hneg, hsf, h1, h3, hS, h4, h2N, hcop, (hL _ hneg.ne).mp hLk⟩

/-! ## The leaves -/

/-- **The leaves that do not involve `δ_o`** (at an admissible `ℓ` with Selmer corank one and a
genus partner `h_*`), each with tex lines, kind and owner. -/
structure PreLeaves {ℓ : ℕ} (W : WData ℓ) : Prop where
  /-- `L_*` is lane RC11's normalization (GLUE Birch–Manin; tex 1825–1830; owner RC11). -/
  lstar : LstarNormalized W.toRCData
  /-- The fixed support contains `2, 3` and the primes of `ℓ` (definition; tex 1790–1793). -/
  support : SupportSpec W
  /-- The prepared filter is positive and prime to the support (definition; tex 2404–2410). -/
  prepared_spec : PreparedSpec W
  /-- (O.7), native index, torsion clause (lane RC12's remaining inputs of (O.8); tex 9101–9445;
  PRINT Cornut–Jetchev, CST + ELLIOT; owner RC12 / batch 3 GenusOdd). -/
  visibility : VisibilityInputs W.toRCData
  /-- The ultrafilter on the stages is nonprincipal (definition; App G 10190–10191). -/
  stages_nonprincipal : (W.stages : Filter ℕ) ≤ cofinite
  /-- The stages are indexed with precision `M_θ ≥ θ` ((3.7) supplies arbitrarily advanced stages;
  ELLIOT/definition; App F 8233, 8400–8401; owner batch 3 GenusOdd). -/
  stages_index : ∀ θ : ℕ, θ ≤ W.Mθ θ
  /-- `D = 1` is admissible at every stage (ELLIOT; tex 2586, App F 8209–8212; owner RC12). -/
  one_admissible : ∀ θ : ℕ, W.admissible θ 1
  /-- The fixed visible witness `D_w` ((3.7); ELLIOT + PRINT CST; tex 2460–2546; owner batch 3
  GenusOdd / RC12). -/
  witness : WitnessLeaf W
  /-- The partitionable auxiliary factor (ELLIOT; App G 10055–10150; owner RC2). -/
  aux_factor : ∃ A₀ : ℕ, AuxFactor W A₀
  /-- The inputs of the even upper bound (3.3b) left by lane RC2's `even_upper_valuation`: (3.3a),
  (3.2) and the missing address on the cubes (ELLIOT; tex 2273–2341; owners RC11, RC1, RC2). -/
  even_upper : EvenUpperInputs W
  /-- (3.4) at the rough companions and at the final `k`, one period constant (PRINT
  Cai–Shu–Tian Thm 1.1 + ELLIOT; tex 2436–2440, 2692–2693; owner batch 3 GenusOdd). -/
  gz34 : Gz34Target W
  /-- The inputs of (3.5) left by lane RC16's `exLimitsUniformLowerBound` over the genuine `𝒪`
  (the valuation identification is lane RC20's `valuationOfO_genuine`): height-one and outer
  switching processes, (4.6) at the companion pairs (ELLIOT; tex 2441–2446, 3987–4047,
  4909–5202; owners RC16, RC15, RC6, batch 3). -/
  eq35 : Eq35InputsGenuine W
  /-- Admissible theta parameters lie in the prepared filter (GLUE; tex 2404–2410, 8408–8429;
  owner batch 3 / RC12). -/
  prepared_glue : PreparedGlue W

/-- **The leaves at the chosen `h_*` and `δ_o`**, each with tex lines, kind and owner. -/
structure PostLeaves {ℓ : ℕ} (W : WData ℓ) : Prop where
  /-- The final companion `k`: a unit of the separate even symbol on negative discriminants square
  at `2N` (ELLIOT; tex 2595–2603, 2720–2721; owner RC2 / RC11 / RC13), recorded by the properties the
  deduction uses, with `L_*(k) ≠ 0` (a unit of the symbol has a nonzero coefficient). -/
  companion : CompanionLeaf W
  /-- The inputs of the address construction at `δ_o` left by lane RC2's `addressInput_of_address`
  in the dictionary form: the companion's arithmetic side conditions, the type alphabets, lane
  RC12's readings of the odd stage source and of the even source of `E^{(k)}` (the coefficient
  rules are batch 3's `rulesUpTo_symb`, `coefficientRules_symb`), the nonempty seeds (the K-split
  seed reduces to RC3's congruence), the prime realization and the two readings (ELLIOT/GLUE; App G
  10258–10861, App F 9447–9976; owners RC2, RC12, RC11, RC3, batch 3 AppGEndpoints). -/
  address : AddressPackageDictLeaf W
  /-- The inputs of (4.6) left by lane RC15's `calibration_46` (the integer data of the support
  triangles, Cassels–Milne isogeny invariance, component groups; ELLIOT + PRINT Milne ADT I.7.3,
  Edixhoven Thm 5.3; tex 3987–4141; owners RC15, RC9). -/
  calibration : CalibrationInputs W.toRCData
  /-- The inputs of (4.7) left by lane RC15's `corrected_eq` (the unused-prime comparison and the
  correction `η`; ELLIOT + GLUE Nekovář 6.4.1–6.4.3; tex 4142–4328; owners RC15, RC4). -/
  common_coordinate : CommonCoordinateInputs W.toRCData
  /-- The inputs of height-one regularity of the primitive coordinates left by lane RC16 (the
  height-one switching processes; the terminal step is batch 3's PairedFunctional) (ELLIOT; tex
  4976–5197; owners RC16, batch 3). -/
  prim_regular : PrimRegularityInputs W.toRCData
  /-- The model inputs of (5.9) left by lane RC7's `clearing_nodes` over the genuine `𝒪`: the
  Smith model of the remaining complex, the two generic patterns, Elliot's coordinate identity,
  the entry poles and the budget (5.7) (ELLIOT; tex 5251–5645; owner RC7 with batch 3 RankCounts
  and lane RC4; the exponent `a = 0` and the `μ`-coordinates are discharged by batch 3's
  PairedFunctional). -/
  clearing_model : ClearingModel W.toRCData
  /-- The inputs of the base-zero lemma left by lane RC15's `baseZero_node` over the genuine DVR
  `Λ_(t)` (lane RC20), with the conductor-one height formula proved by lane RC19 from Cai–Shu–Tian
  Thm 1.1 (`Prints.cst`) and the conductor-one Heegner data (`HeegnerData`): the two-term model
  with central dimensions `(1,1)`, the retained boundary (4.5), (4.7) at the base (ELLIOT + GLUE
  `L(E/K,s) = L(E,s)L(E^{(k)},s)`; tex 4330–4376; owners RC15, RC19, batch 3 HeegnerCohomology,
  RankCounts). -/
  base_zero : BaseZeroInputsCST W.toRCData

/-- **Every remaining hypothesis of Theorem 5.3 beyond the blueprint's `Prints`.** -/
structure RCLeaves where
  /-- Hoffstein–Luo over newforms (PRINT, Math. Res. Lett. 4 (1997), p. 436, as stated by lane
  RC8; tex 1985–1991, App G 9996). -/
  hlPrint : PrintsAnalytic.HoffsteinLuoTheorem
  /-- The twisted functional equation over newforms (PRINT, as quoted in Hoffstein–Luo p. 435,
  display (1); lane RC8). -/
  twistedFE : PrintsAnalytic.TwistedFunctionalEquation
  /-- Modularity in newform form: every elliptic curve over `ℚ` has a weight-two newform with the
  same `L`-function (PRINT: BCDT Thm A with Atkin–Lehner/Carayol; lane RC8). -/
  modularNewform : PrintsAnalytic.ModularNewform
  /-- Absolute convergence of `L(E, s)` on `Re s > 3/2` (GLUE, textbook: Hasse's bound; lane RC8). -/
  hasse : PrintsAnalytic.HasseConvergence
  /-- The level of the functional equation is supported on the bad primes (GLUE: the level is the
  conductor; lane RC13). -/
  levelSupport : Nonvanishing.FromRC8.LevelSupport
  /-- The interface data, given the genus partner `h_*`. -/
  data : ∀ ℓ : ℕ, ℤ → WData ℓ
  /-- The leaves not involving `δ_o`, at every genus partner. -/
  pre : ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) → ∀ h : ℤ, IsGenusPartner ℓ h →
    PreLeaves ((data ℓ h).withHstar h)
  /-- The leaves at the chosen `h_*` and the attained odd minimum `δ_o`. -/
  post : ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) → ∀ h : ℤ, IsGenusPartner ℓ h →
    ∀ δ : ℤ, IsLeast (data ℓ h).depthSet δ → PostLeaves ((data ℓ h).withChoices h δ)

/-! ## The steps from the leaves -/

/-- Hoffstein–Luo for elliptic curves (PROVED from the print; lane RC18's `twistDictionary`). -/
theorem RCLeaves.hl (L : RCLeaves) : Nonvanishing.HoffsteinLuo :=
  Nonvanishing.FromRC8.hoffsteinLuo_of_curve
    (TwistDictionary.hoffsteinLuoCurve_of_print L.hlPrint L.modularNewform L.hasse)

/-- BFH's twist sign for elliptic curves (PROVED from the twisted functional equation; lane
RC18's `twistDictionary`; the level-support GLUE). -/
theorem RCLeaves.twistSign (L : RCLeaves) : Nonvanishing.BFHTwistSign :=
  Nonvanishing.FromRC8.bfhTwistSign_of_curve
    (TwistDictionary.twistedRootNumberCurve_of_print L.twistedFE L.modularNewform L.hasse)
    L.levelSupport

/-- Every elliptic curve over `ℚ` has a root number (PROVED from modularity in newform form and
Hasse's convergence; lane RC8's `exists_rootNumber`). -/
theorem RCLeaves.rootNumberExists (L : RCLeaves) : Nonvanishing.FromRC8.RootNumberExists :=
  fun _ hA => PrintsAnalytic.exists_rootNumber L.modularNewform L.hasse hA

/-- **The thirteen steps of the skeleton from the leaves** (PROVED). -/
theorem rcSteps_of_leaves (P : Prints) (L : RCLeaves) {ℓ : ℕ} (hadm : Adm ℓ)
    (hSel : SelmerCorankOne (Ecurve ℓ)) {h : ℤ} (hG : IsGenusPartner ℓ h) :
    ∃ δ : ℤ, RCSteps ((L.data ℓ h).withChoices h δ).toRCData := by
  set W₁ := (L.data ℓ h).withHstar h with hW₁
  have hp := L.pre ℓ hadm hSel h hG
  -- `M_θ → ∞` along the ultrafilter (batch 3's `stagesAdvance_of_nonprincipal`)
  have hstages : Tendsto W₁.Mθ (W₁.stages : Filter ℕ) atTop :=
    ZInQ.Contrib.CloudB3RC53.GenusOdd.stagesAdvance_of_nonprincipal _ hp.stages_nonprincipal _
      hp.stages_index
  have hHL := L.hl
  have hTS := L.twistSign
  have hL : LstarTarget W₁.toRCData := lstarTarget_of hadm.1 L.rootNumberExists hp.lstar
  have hvis : VisibilityTarget W₁.toRCData := visibilityTarget_of_inputs _ hp.visibility
  obtain ⟨A₀, haux⟩ := hp.aux_factor
  obtain ⟨C₁, h33b⟩ := evenUpper33b_of_inputs W₁ P
    ZInQ.Contrib.CloudB3RC53.KummerCorankZero.kummerCorankZero_proof hadm.1 hL hp.even_upper
  have hF3 : F3Target W₁ := f3Target_of W₁ P
    ZInQ.Contrib.CloudB3RC53.KummerCorankZero.kummerCorankZero_proof hHL hTS
    L.rootNumberExists hadm.1 hL hp.support hp.prepared_spec haux h33b
  -- the attained odd minimum
  obtain ⟨Cdet, hCdet⟩ := hvis
  obtain ⟨A, CE, h33⟩ := hF3
  obtain ⟨Cper, h34, h34k⟩ := hp.gz34
  have h35 : Eq35Target W₁ := eq35Target_of_inputs W₁ (eq35Inputs_of_genuine W₁ hp.eq35)
  obtain ⟨CR, h35A⟩ := h35 A
  obtain ⟨δ, hδ⟩ := exists_oddMinimum W₁ h33 h34 h35A hCdet hp.prepared_glue hp.witness
  refine ⟨δ, ?_⟩
  set W₂ := (L.data ℓ h).withChoices h δ with hW₂
  have hq := L.post ℓ hadm hSel h hG δ hδ
  -- the steps for `W₂` (its fields other than `δ_o` are those of `W₁`)
  have hL₂ : LstarTarget W₂.toRCData := hL
  have hvis₂ : VisibilityTarget W₂.toRCData := ⟨Cdet, hCdet⟩
  have hG₂ : GenusPartnerTarget W₂.toRCData := genusPartnerTarget_of hL₂ hG
  have hfam : FinalFamilyTarget W₂.toRCData :=
    finalFamilyTarget_of W₂ hvis₂ hstages ⟨A, CE, h33⟩ ⟨Cper, h34, h34k⟩ h35
      hp.prepared_glue hδ (addressLeaf_of_dictPackage W₂ hq.address)
  have h47 : CommonCoordinateTarget W₂.toRCData :=
    commonCoordinateTarget_of_inputs hq.common_coordinate
  have hheight : HeightOneTarget W₂.toRCData :=
    heightOneTarget_of_inputs _ hq.prim_regular h47
  exact rcSteps_of_targets _ hL₂ hG₂ hvis₂ hstages hp.one_admissible
    (companionTarget_of hL₂ hq.companion)
    ⟨Cper, h34k⟩ hfam (calibrationTarget_of_inputs hq.calibration) h47 hheight
    (clearingTarget_of_model _ hheight hq.clearing_model) (baseZeroTarget_of_inputs P (baseZeroInputs_of_CST hq.base_zero))

/-! ## The node and Theorem 5.3 -/

/-- **`BranchPackageNode` from the leaves** (PROVED). -/
theorem branchPackageNode_of_leaves (P : Prints) (L : RCLeaves) : BranchPackageNode := by
  intro ℓ hadm hSel
  have hw := rootNumberNode_proof P ℓ hadm hSel
  obtain ⟨h, hG⟩ := exists_genusPartner L.hl L.twistSign P.bcdt hadm.1 hw
  obtain ⟨δ, S⟩ := rcSteps_of_leaves P L hadm hSel hG
  by_cases hU : ((L.data ℓ h).withChoices h δ).OddEmptyUnit
  · exact Or.inl (rc_of_oddEmptyUnit _ S hU)
  · exact Or.inr (fixedFieldPackage_of_steps hadm.1 P
      ZInQ.Contrib.CloudB3RC53.KummerCorankZero.kummerCorankZero_proof _ S hSel hU)

/-- **Theorem 5.3 (`hyp:RC`) from the printed leaves `Prints` and the remaining hypotheses
`RCLeaves`** (PROVED; standard axioms): the blueprint's assembly with `branchPackageNode_of_leaves`
and lane RC1's `missingAddressNode`. -/
theorem restrictedConverseGenuine_of_leaves (P : Prints) (L : RCLeaves) :
    RestrictedConverseGenuine :=
  restrictedConverseGenuine_of_nodes P (branchPackageNode_of_leaves P L)
    ZInQ.Manuscript.RC.Boolean.missingAddressNode

end ZInQ.Manuscript.RC.Wiring
