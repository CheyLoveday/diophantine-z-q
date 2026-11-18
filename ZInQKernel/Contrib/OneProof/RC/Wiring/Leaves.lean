import ZInQKernel.Contrib.OneProof.RC.Wiring.CompanionLeaf
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
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenusOdd34
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate3
import ZInQKernel.Contrib.OneProof.RC.Wiring.PreSpec
import ZInQKernel.Contrib.OneProof.RC.Wiring.AuxFactor3
import ZInQKernel.Contrib.OneProof.RC.Wiring.EvenUpper3
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.DensityLeaf
import ZInQKernel.Contrib.OneProof.RC.Wiring.OddModels
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalFinal
import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex3
import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex4
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaLevel
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeaf2
import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Assembly
import ZInQKernel.Contrib.OneProof.RC.Wiring.UniformSwitch
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineEq35Leaf
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate4
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeaf3

/-!
# Theorem 5.3, Lane RC0: every remaining hypothesis in one structure

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
   results (`rcSteps_of_leaves`): `lstar_ne_zero_iff` (RC11, the normalization carried by the
   GenusOdd instance), `genus_partner` (RC13), `visibility` (RC12), `companion` (from the leaf and
   RC11), `gz_comparison` and (3.4) at the companions (batch 3's GenusOdd from `Prints` and
   `ArtinFactorization`, with RC11's `L_*` as a scaled central value), `final_family` (batch 3's
   `finalFamilyField_proof`, with (F.3) from RC13's `roughCompanion`, (3.3b) from batch 3's
   EvenUpper over RC11's (3.2) with the Boolean comparison from RC1, the auxiliary factor from batch
   3's dictionary, (3.5) from RC16 with batch 3's concrete outer switching data over RC20's genuine
   `𝒪`, the stages from the data specification, and the address input from RC2's construction at the
   staged level with the K-split even restriction, constituent models over finite quotients and
   RC3's trace data), `calibration` (RC15 with RC19's regulator, the free generators from `Prints`
   and batch 3's Calibration), `common_coordinate` (batch 3's support-triangle models), `base_zero`
   (RC15 through batch 3's `baseZeroEndToEnd` over RC20's `Λ_(t)`, the height formula by RC19),
   `height_one` (RC16 with batch 3's concrete height-one switching data and (4.7)), `clearing` (RC7
   with batch 3's PairedFunctional and the repaired budget (5.7));
5. the skeleton's Branch 1 / fixed-field package (`rc_of_oddEmptyUnit`, `fixedFieldPackage_of_steps`),
   with the Kummer sequence in rank zero proved by batch 3 (`kummerCorankZero_proof`);
6. the blueprint's assembly with the missing-address node proved by lane RC1.

No field relies on batch 3's SelmerDuality statements (reviewed as GLUE), on batch 3's
`TraceModel`/`ConstituentModel` (which cannot be inhabited: `traceModel_false`), or on the
positivity versions of the budget (5.7).

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

/-! The final companion leaf `CompanionLeaf` and `companionTarget_of` are in `CompanionLeaf.lean`. -/

/-- **The address leaf from the density leaf in the remaining branch** (PROVED: lane RC24's
`addressPackageStagedLeaf_of_genuineLeaf` and `addressGenuineLeaf_of_densityLeaf`, used only where
the staged package is asked for, `¬ W.OddEmptyUnit`). -/
theorem addressLeaf_of_densityLeaf_branch {ℓ : ℕ} {W : WData ℓ} (hℓ : Adm ℓ)
    (hcomp : CompanionLeaf W)
    (h : ¬ W.OddEmptyUnit → ZInQ.Manuscript.RC.AddressGenuine.AddressDensityLeaf W) :
    AddressLeaf W :=
  addressLeaf_of_stagedPackage W fun A CE CR Cper Cdet h33 h34 h35 hvis hU =>
    ZInQ.Manuscript.RC.AddressGenuine.addressPackageStagedLeaf_of_genuineLeaf hℓ hcomp
      (ZInQ.Manuscript.RC.AddressGenuine.addressGenuineLeaf_of_densityLeaf (h hU))
      A CE CR Cper Cdet h33 h34 h35 hvis hU

/-! ## The leaves -/

/-- **The leaves that do not involve `δ_o`** (at an admissible `ℓ` with Selmer corank one and a
genus partner `h_*`), each with tex lines, kind and owner. -/
structure PreLeaves {ℓ : ℕ} (W : WData ℓ) : Prop where
  /-- The data are built to specification (`PreDataSpec`: the support consists of primes and
  contains `2, 3` and the primes of `ℓ`; the hyperfilter on the stages; `M_θ ≥ θ`; the stage support
  is the prepared filter cut by a stage condition holding at `D = 1`; the prepared filter contains
  one) (definitions; tex 1790–1793, 2404–2410, 2586, App F 8209–8212, 8233, 8400–8429, App G
  10190–10191; owner RC0, as batch 3's `PreFieldsSpec`). It gives the support, the stages and the
  stage support (`preFields_of_dataSpec`). -/
  data_spec : PreDataSpec W
  /-- The prepared filter is positive and prime to the support (definition; tex 2404–2410). -/
  prepared_spec : PreparedSpec W
  /-- The specification of the data behind the partitionable auxiliary factor (`AuxFactorInputs`:
  the type data, the conductor on the support, the even sources per total type with RC2's
  coefficient rules and vanishing off their filter, a unit seed at every prepared total type, and
  the meaning of `Partitionable` on the filter of negative squarefree parameters prime to the
  support; definition + ELLIOT; tex 2016–2185, 2296–2297, 2343–2401, App G 10055–10150; owners RC0,
  RC2, batch 3 AuxFactor / CoefficientDictionary). The auxiliary factor itself is PROVED from it
  (the dictionary argument at the prepared types, `auxFactor_of_inputs`). -/
  aux_factor : AuxFactorInputs W
  /-- The remaining inputs of the even upper bound (3.3b) (`EvenUpperRC11Inputs`): (3.3a) at the units
  of the normalized even symbol, lane RC11's (3.2) (`EvenScalar32`), and the realized cubes of units
  at the partitionable parameters (ELLIOT; Proposition `ex:sec7-even-upper`, tex 2295–2341, App G
  10079–10129; owners RC11, batch 3 EvenUpper, RC2). The missing address on the cubes is PROVED
  (batch 3's Boolean comparison from lane RC1), at the single precision the consumer uses
  (`EvenUpperInputsAt`). -/
  even_upper : EvenUpperRC11Inputs W
  /-- The odd side's genuine objects (`OddInstance`): GenusOdd's objects of (3.4) — lane RC11's
  normalization of `L_*` (GLUE Birch–Manin; tex 1825–1830, 7175–7177), the newform data of `E`,
  `L_*(h_*)` over the lattice's `Ω⁻` a nonzero rational (GLUE Manin–Drinfeld, tex 2403), the
  Heegner selections and the identification of the interface data (definitions), the genus
  partner's squares at the level and the final `k`'s conditions (ELLIOT; tex 2403–2416,
  2595–2603) — and, at the same genus selection, lane RC23's visibility models: the multiplier
  killing native torsion, the stage maps, the odd sign of admissible parameters (GLUE), the theta
  side and the comparison argument of (O.7) (ELLIOT + PRINT Cornut–Jetchev; tex 9101–9445), and
  (O.2) at the fixed witness (tex 2460–2546, 8225–8405); owners RC11, batch 3 GenusOdd, RC13, RC23,
  the hosts. PROVED from it: (3.4) (`gz34Target_of_genusOdd`), (O.8)'s inputs
  (`visibilityInputs_of_oddInstance`) and the fixed witness (`witnessLeaf_of_oddInstance`). -/
  odd : Nonempty (OddInstance W)
  /-- The inputs of (3.5) on batch 3's genuine switching data (`Eq35InputsGenuineGG`): the primitive
  coordinates at the companion pairs with batch 3's `GenuineSwitchData` over configuration families
  genuine at every height-one prime (`RegularityInputsG`: lane RC26's Galois fibers, the genuine
  moving variable), (4.6) at the companion pairs, and ONE family of switched minimal models over `𝒪`
  for all ring instances, each a two-term model of genuine Galois Selmer data over `𝒪`, the actual
  models' coordinates having the valuations of `ι_𝒪 u_prim`, with batch 3's
  `GenuineOuterSwitchData` (switch GLUE between the determined stages) for every sequence of
  companion pairs (ELLIOT + GLUE; tex 2441–2446, 3987–4047, 4909–5202; owners RC16, RC15, RC6, RC26,
  batch 3 SwitchInputs). PROVED from them: `pos`, `minor_link`, the integral cycles and functionals,
  the nonzero outer class, the Cramer terminal step, the equal inner valuations, regularity
  (`regular_of_genuineSwitchData`), and RC16's (3.5) over RC20's genuine valuation. Remaining
  freedom: the configuration families and the model family are existentials identified with the
  actual Selmer complexes by GLUE (the coefficient modules and local conditions of the instances
  are not defined in the tree); their stage dimensions are the genuine ones
  (`RegularityInputsG.fiberDim_forced`, `outer_start_forced`). -/
  eq35 : Eq35InputsGenuineGG W

/-- **The leaves at the chosen `h_*` and `δ_o`**, each with tex lines, kind and owner. -/
structure PostLeaves {ℓ : ℕ} (W : WData ℓ) : Prop where
  /-- The final companion `k`: a unit of the separate even symbol on negative discriminants square
  at `2N` (ELLIOT; tex 2595–2603, 2720–2721; owner RC2 / RC11 / RC13), recorded by the properties the
  deduction uses, with `L_*(k) ≠ 0` (a unit of the symbol has a nonzero coefficient). -/
  companion : CompanionLeaf W
  /-- In the remaining branch (`¬ W.OddEmptyUnit`, the scope of the address construction: tex
  2588–2593, 10268–10270, 10501–10505; the odd-empty-unit branch needs no address), the inputs of
  the address construction at `δ_o` over the genuine Galois objects (lane RC24's
  `AddressDensityLeaf`): the label data, a fresh prime of `k`, density models of the odd stage
  source on a set of stages of the ultrafilter and of the transported even source at every budget
  (ELLIOT trace identities and readings, tex 9671–9745, 9905–9918; GLUE Kummer, openness and
  unramifiedness of `N_U`, tex 9524–9548, 9663–9669), the odd witness, the odd and prepared
  filters, the even filter, the K-split seed and the even reading (ELLIOT/GLUE; App G
  10079–10861, App F 9447–9976; owners RC24, RC2, RC12, RC11, RC3, batch 3). Everything else of
  the address package is PROVED over genuine `G_ℚ`, Frobenius elements and characters, Chebotarev
  by the repository's density theorem (`addressLeaf_of_densityLeaf`). -/
  address : ¬ W.OddEmptyUnit → ZInQ.Manuscript.RC.AddressGenuine.AddressDensityLeaf W
  /-- The inputs of (4.6) at every address (`CalibrationInputsH`): the two-primary Ш and torsion
  orders (ELLIOT + PRINT Kolyvagin), the component groups at `p ∣ k` through good models up to
  isomorphism and Edixhoven's print in its model-free form (PRINT Edixhoven Thm 5.3, Rem. 5.4.1, as
  GLUE), the pullback and comparison data, Cassels–Milne isogeny invariance at the genuine canonical
  regulators (PRINT Milne ADT I.7.3 + GLUE), the moving prime in the output form of RC17's moving
  character, and the triangular Kummer model whose quotient block is the direct sum of the local
  blocks at the moving and active places, up to changes of basis with central unit determinants
  (ELLIOT; tex 3987–4141; owners RC15, RC9, RC19, RC4/RC17, batch 3 Calibration). PROVED from them:
  the isogeny and regulator data (RC19's `regulator_inputs_sumDiff`), the free generators (from
  `Prints`), the component fields, the moving-prime fields, the quotient length `2v₂N + 4ω` and
  `hvprim` (batch 3's Calibration). -/
  calibration : CalibrationInputsH W.toRCData
  /-- The inputs of (4.7) at every address, tied to the family and the address
  (`CommonCoordinateInputsG`): the coefficient ring and its evaluation at the character of `x`, with
  `x(g_q) = (−1)^{λ_q(x)}` at the family's graph primes (definition), the Euler-factor identity and
  the invertibility of `e_q` (ELLIOT, the Frobenius model at `q`), the Frobenius matrices of
  determinant `p` at the unused primes `λ_p(x) = 0`, and at each relaxation step the support
  triangle in the original integral bases with functionals from retained Selmer data
  (`NaturalStep`; ELLIOT + GLUE; tex 4142–4328; owners RC15, RC4, batch 3 CommonCoordinate). PROVED
  from them: `x(g_q) = ±1`, the unused primes, `λ_R ∘ i = e_q λ_P`, the multi-prime (4.7) and
  `ε_q ∈ Λ^×` (batch 3's `commonCoordinateInputs_of_natural`). -/
  common_coordinate : CommonCoordinateInputsG W.toRCData
  /-- The inputs of height-one regularity of the primitive coordinates (`PrimRegularityInputsG`): at
  every height-one prime `𝔭 ≠ (2)`, a configuration family genuine at `𝔭` (lane RC26's Galois
  Selmer fibers with finite support and subcomplex conditions, the genuine moving variable) and
  batch 3's `GenuineSwitchData` over it starting at `u_{prim,x}` (homotopy equivalences of the
  genuine fibers with the stages' two-term fibers, the actual class and functional at the start, the
  sign involutions, primitive vectors, and the switches along the configuration sequence with their
  GLUE step data) (ELLIOT + GLUE; tex 4976–5197; owners RC16, RC26, RC15, batch 3 SwitchInputs /
  SignSplitting / ExactSequences). PROVED from them: `pos`, the terminal step, `s₊ + s₋ = s`, the
  nonquadratic `U = F`, regularity (`regular_of_genuineSwitchData`) and the intersection formula.
  Remaining freedom: the family is an existential identified with the address's actual primitive
  scalar Selmer complex by GLUE; its fiber dimensions are the genuine `dim H¹`
  (`RegularityInputsG.fiberDim_forced`), and over a fixed genuine family the data are not implied
  by the target (`exZeroFamily_no_data`). -/
  prim_regular : PrimRegularityInputsG W.toRCData
  /-- The inputs of (5.9) over the genuine Selmer complexes (`ClearingInputsG`): the fixed field
  `K` and the constants before the family; at every final family batch 3's `Identification2G` (the
  pre-cancellation family model with one nonempty block of new local differentials indexed by the
  new places, `T₀ = Y₀ = 0`, the central Smith form, the (5.7) counts, a quasi-isomorphism to lane
  RC26's genuine family Selmer complex, the genuine support change of Nekovář 7.8.8(ii) and the
  tame model as a quasi-isomorphic model of the genuine local cochains; GLUE), the actual cycle,
  the closed functional and the universal correction `η` over `𝒪[G]` (data), and one coordinate
  identification in the original determinant basis, `ũ_x = η_x · c^{orig}_x` where `Δ_x ≠ 0`
  (`OrigCoordLink`, GLUE) (tex 5355–5645, 3470–3499, 3877–3892, 4219–4222; owners RC7, RC15,
  RC26, batch 3 ClearingComplex / CoordLink / RankCounts / PairedFunctional). The support
  comparison is a quasi-isomorphism by the PRINT `NekovarProp788ii` (not an input). PROVED from
  them: the cancellation factor `κ = det B`, the transported functional `μ = λ ∘ incl`, E1a, E1b
  for the Knudsen–Mumford coordinate, the Smith model, the generic patterns, the entry poles, the
  budget (5.7), and (5.9) by lane RC7 over RC20's genuine `𝒪`, with the exponent `a = 0`. -/
  clearing_model : ClearingInputsG W.toRCData
  /-- The inputs of the base-zero lemma left by lane RC25's `baseZeroTarget_of_leaves` (lane RC15's
  `baseZero_node` over lane RC20's `Λ_(t)`, the height formula by lane RC19 from Cai–Shu–Tian Thm 1.1
  and the conductor-one Heegner data): the two-term model with central dimensions `(1,1)`, the
  stages of (4.5) at the base (PRINT (4.1) per stage) with the limit at the centre (ELLIOT), and the
  identification of `u_{prim,0}` (definition); (4.7) at the base, `ũ₀ ∈ Λ[1/2]` and the package's
  datum are PROVED from `common_coordinate` and `prim_regular` (tex 4330–4376, 3895–3921,
  4369–4373, 5703–5706; owners RC15, RC19, RC25, batch 3 HeegnerCohomology, RankCounts). -/
  base_zero : BaseZeroAssembly.BaseZeroLeafInputs W.toRCData

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
  /-- The inert clause of the local factors of `E` over imaginary quadratic fields: at an inert prime
  of good reduction the Euler factor of `E/K` is `L_p(E, X) L_p(E, −X)` in `X²` (GLUE: the Frobenius
  characteristic polynomial; tex 2411–2440; owner batch 3 GenusOdd). With `modularNewform` and
  `hasse` it gives the Artin factorization of the ring-class `L`-functions
  (`artinFactorization_of_newform`), the one GLUE statement of (3.4) (genus theory's square roots,
  the Galois closure, the splitting criterion and good reduction off the level are PROVED). -/
  localFactorInert : ZInQ.Contrib.CloudB3RC53.GenusOdd.LocalFactorInert
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
RC18's `twistDictionary`; the level of the functional equation is supported on the bad primes by
lane RC22's `levelSupport_of_modularNewform`). -/
theorem RCLeaves.twistSign (L : RCLeaves) : Nonvanishing.BFHTwistSign :=
  Nonvanishing.FromRC8.bfhTwistSign_of_curve
    (TwistDictionary.twistedRootNumberCurve_of_print L.twistedFE L.modularNewform L.hasse)
    (GlueSweep.Ana.levelSupport_of_modularNewform L.modularNewform)

/-- The Artin factorization of the ring-class `L`-functions (PROVED from `modularNewform`, `hasse`
and the inert clause; batch 3's `artinFactorization_of_newform`). -/
theorem RCLeaves.artin (L : RCLeaves) : ZInQ.Contrib.CloudB3RC53.GenusOdd.ArtinFactorization :=
  ZInQ.Contrib.CloudB3RC53.GenusOdd.artinFactorization_of_newform L.hasse L.modularNewform
    L.localFactorInert

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
  obtain ⟨hsupp, hnonp, hidx, hone, hglue⟩ := preFields_of_dataSpec hadm.1 hp.data_spec
  -- `M_θ → ∞` along the ultrafilter (batch 3's `stagesAdvance_of_nonprincipal`)
  have hstages : Tendsto W₁.Mθ (W₁.stages : Filter ℕ) atTop :=
    ZInQ.Contrib.CloudB3RC53.GenusOdd.stagesAdvance_of_nonprincipal _ hnonp _ hidx
  have hHL := L.hl
  have hTS := L.twistSign
  obtain ⟨Io⟩ := hp.odd
  have I := Io.toGenusOddInstance
  have hL : LstarTarget W₁.toRCData :=
    lstarTarget_of hadm.1 L.rootNumberExists (lstarNormalized_of_instance I)
  have hvis : VisibilityTarget W₁.toRCData :=
    visibilityTarget_of_inputs _ (visibilityInputs_of_oddInstance P L.artin Io hglue)
  obtain ⟨A₀, haux⟩ := auxFactor_of_inputs W₁ hsupp hp.aux_factor
  obtain ⟨C₁, h33b⟩ := evenUpper33b_of_RC11Inputs W₁ P hadm.1 hL (lstarNormalized_of_instance I)
    hp.even_upper
  have hF3 : F3Target W₁ := f3Target_of W₁ P
    ZInQ.Contrib.CloudB3RC53.KummerCorankZero.kummerCorankZero_proof hHL hTS
    L.rootNumberExists hadm.1 hL hsupp hp.prepared_spec haux h33b
  -- the attained odd minimum
  obtain ⟨Cdet, hCdet⟩ := hvis
  obtain ⟨A, CE, h33⟩ := hF3
  obtain ⟨Cper, h34, h34k⟩ := gz34Target_of_genusOdd P L.artin L.rootNumberExists I
  have h35 : Eq35Target W₁ := eq35Target_of_inputsGG W₁ hp.eq35
  obtain ⟨CR, h35A⟩ := h35 A
  obtain ⟨δ, hδ⟩ := exists_oddMinimum W₁ h33 h34 h35A hCdet hglue
    (witnessLeaf_of_oddInstance Io hstages)
  refine ⟨δ, ?_⟩
  set W₂ := (L.data ℓ h).withChoices h δ with hW₂
  have hq := L.post ℓ hadm hSel h hG δ hδ
  -- the steps for `W₂` (its fields other than `δ_o` are those of `W₁`)
  have hL₂ : LstarTarget W₂.toRCData := hL
  have hvis₂ : VisibilityTarget W₂.toRCData := ⟨Cdet, hCdet⟩
  have hG₂ : GenusPartnerTarget W₂.toRCData := genusPartnerTarget_of hL₂ hG
  have hfam : FinalFamilyTarget W₂.toRCData :=
    finalFamilyTarget_of W₂ hvis₂ hstages ⟨A, CE, h33⟩ ⟨Cper, h34, h34k⟩ h35
      hglue hδ
      (addressLeaf_of_densityLeaf_branch hadm hq.companion hq.address)
  have h47 : CommonCoordinateTarget W₂.toRCData :=
    commonCoordinateTarget_of_inputs (commonCoordinateInputs_of_G hq.common_coordinate)
  have hheight : HeightOneTarget W₂.toRCData :=
    heightOneTarget_of_inputsG _ hq.prim_regular h47
  exact rcSteps_of_targets _ hL₂ hG₂ hvis₂ hstages hone
    (companionTarget_of hL₂ hq.companion)
    ⟨Cper, h34k⟩ hfam (calibrationTarget_of_H P hadm.1 hq.calibration) h47 hheight
    (clearingTarget_of_G _ hheight hq.clearing_model) (BaseZeroAssembly.baseZeroTarget_of_leaves P
      (commonCoordinateInputs_of_G hq.common_coordinate)
      (primRegularityInputs_of_G _ hq.prim_regular) hq.base_zero)

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
