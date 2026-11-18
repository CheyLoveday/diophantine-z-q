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
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.ArtinUnconditional
import ZInQKernel.Contrib.CloudB3RC53.Hasse.Final
import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex3
import ZInQKernel.Contrib.OneProof.RC.Wiring.ClearingComplex4
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaLevel
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeaf2
import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Assembly
import ZInQKernel.Contrib.OneProof.RC.Wiring.BaseZeroText
import ZInQKernel.Contrib.OneProof.RC.Wiring.UniformSwitch
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineEq35Leaf
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate4
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeaf3
import ZInQKernel.Contrib.OneProof.RC.Wiring.StageData

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
   results (`rcSteps_of_leaves`): `lstar_ne_zero_iff` (RC11, the normalization carried by the odd
   instance), `genus_partner` (RC13), `visibility` (RC12's (O.8) from lane RC23's models at the odd
   instance's genus selection), `companion` (from the leaf and RC11), `gz_comparison` and (3.4) at
   the companions (batch 3's GenusOdd from `Prints` and `ArtinFactorization`, with RC11's `L_*` as a
   scaled central value), `final_family` (batch 3's `finalFamilyField_proof`, with (F.3) from RC13's
   `roughCompanion`, (3.3b) from batch 3's EvenUpper over RC11's (3.2) with the Boolean comparison
   from RC1, the auxiliary factor by the dictionary argument at the prepared types, (3.5) by RC16
   from the ELLIOT leaf `eq35` on batch 3's genuine switching data, the stages from the Appendix F
   stage construction (`StageData.lean`: the data specification `PreDataSpec` is PROVED from the
   fixed support and the stage link), and the address input from lane RC24's construction (budgeted
   density models) over genuine `G_ℚ`, Frobenius elements and characters, Chebotarev from the
   repository's density theorem, the odd source read on its own filter and the odd witness derived
   from `δ_o`), `calibration` (from the ELLIOT leaf `calibration`, with RC19's regulator relation
   and the free generators from `Prints`), `common_coordinate` (the ELLIOT leaf `common_coordinate`,
   through batch 3's natural support-triangle steps), `base_zero` (lane RC25's
   `BaseZeroAssembly.baseZeroTarget_of_leaves`, through RC0's `baseZeroTarget_of_inputs` and RC15's
   `baseZero_node_genuine` over RC20's `Λ_(t)`, the height formula by RC19, with (4.7) and
   `ũ₀ ∈ Λ[1/2]` at the base from `common_coordinate` and `prim_regular`, from the ELLIOT leaf
   `base_zero` on the text's named steps: lane RC30's inner limit and central comparison, the paired
   functional), `height_one` (RC16's descent from the ELLIOT leaf `prim_regular`, on batch 3's
   genuine switching data, and (4.7)), `clearing` (RC7's (5.9) and the repaired budget (5.7) from
   the leaf `clearing_model`, over batch 3's identification with lane RC26's genuine Selmer
   complexes); see "Conclusion-shaped leaves" below;
5. the skeleton's Branch 1 / fixed-field package (`rc_of_oddEmptyUnit`, `fixedFieldPackage_of_steps`),
   with the Kummer sequence in rank zero proved by batch 3 (`kummerCorankZero_proof`); Branch 1 reads
   the visibility step at `D = 1` only (tex 2584–2589), but `rcSteps_of_leaves` builds every step
   first, so a discharge supplies every leaf in both branches (the address leaf only in the
   remaining branch);
6. the blueprint's assembly with the missing-address node proved by lane RC1.

No field relies on batch 3's SelmerDuality statements (reviewed as GLUE), on batch 3's
`TraceModel`/`ConstituentModel` (which cannot be inhabited: `traceModel_false`), or on the
positivity versions of the budget (5.7).

**Which theorem carries the reduction.** Given `Prints`, the blueprint's `BranchPackageNode` is
equivalent to Theorem 5.3 (its coefficient data are existential and not tied to `ũ_x`). The
faithful reduction of Theorem 5.3 to Elliot's steps is `restrictedConverseGenuine_of_leaves` here
(and `RC/Assembly.lean`'s `restrictedConverseGenuine_of_steps'`): the step `RCSteps.clearing`,
discharged here from lane RC7, ties `C.u x j = [tʲ] ũ_x`. Claims about the reduction cite these.

**The interface data are chosen by the discharge.** `RCLeaves.data` is an arbitrary function: the
interface data (`WData`: the support, the filters, `L_*`, `j_gen`, `j_rc`, the stages and their
coefficients, `k`, `u_{prim,x}`, `ũ_x`, `Partitionable`) are existentially chosen by whoever
discharges `RCLeaves`, and only the leaves constrain them; the odd instance's genus selection and
RC11's normalization pin part of them to genuine objects. The clearing link identifies the
coefficients with the chosen `uTilde`; it does not by itself identify that function with the
genuine manuscript objects. Instantiating the data with the genuine objects is an obligation of
each leaf's discharge.

**Conclusion-shaped leaves.** The following leaves are Elliot's steps themselves, or close to them
(kind ELLIOT): their interface structures are existential witnesses that do not, or only partly,
constrain the genuine objects, so the PROVED statements about those structures concern the abstract
witnesses:
* `PreLeaves.odd_staged`: the point side is genuine, but its theta side and comparison argument
  exist for every `λ` with `a_θ ≡ c₀ λ (mod 2^{M_θ})`, so together they are (O.7) itself; its stage
  part is the Appendix F construction, with (O.2) at the witness PROVED from
  `WitnessSpecialization`;
* `PostLeaves.address`: `KSplitSeed` is equivalent to the conclusion of the seed lemma, and
  `EvenReading` is (F.1)'s conclusion for the chosen reading `Rev`;
* `PostLeaves.base_zero`: for a torsion specified point its core is equivalent to the conclusion of
  Lemma `ex:arith-base-zero`;
* `PostLeaves.calibration`: the good models and Edixhoven's print are tied to the genuine twists;
  the local-block Kummer model is equivalent to the pre-Milne valuation formula, and the Milne,
  period, moving-prime and Kummer-model data are existential witnesses;
* `PostLeaves.common_coordinate`: equivalent to (4.7) together with `ε_x = 1` where no graph prime
  is unused; its coefficient ring is an existential ring `R` with `χ : R →+* ℚ₂[[t]]`, not `𝒪[G]`
  (no `t`-preserving ring map `𝒪[G] → ℚ₂[[t]]` exists, and `η_x` may have a pole, tex 4153–4155,
  4318–4320);
* `PreLeaves.eq35` and `PostLeaves.prim_regular`: the configuration families are existential and
  only required to be some genuine Galois Selmer data with `t = X`; with one genuine complex of the
  homotopy type of `[k --0--> k]` at each `𝔭` (true, not formalized), they are equivalent to
  their targets (`regularityInputsG_iff_of_unitFibre`); over the address's own genuine complexes no
  switch step can be formed (`C¹_cont` is infinite-dimensional), so the address's family witnesses
  the regularity part only when `s(𝔭) = 1`;
* `PostLeaves.clearing_model`: its family clause is vacuous, and batch 3's `Identification2G` is an
  abstract family identification with a finite unramified-support comparison (its new blocks in
  degrees two and three); it does not model the full-condition singular-quotient triangle (5.6) of
  tex 5234–5238, 5398–5403.

**Departures** (besides those in the fields' docstrings: the narrowing of the seeds in
`aux_factor`, the existential level in `even_upper`, the scope of `prim_regular` at `x = 0`):
* scope: the post leaves are demanded in both branches, the address leaf excepted (`RCLeaves.post`);
* `RCData.FinalFamilyAt` omits the clause "a terminal of every nonzero activation" (tex 2243–2245,
  10561–10562), so it also admits families with `h_x = 1` at some `x ≠ 0` (where `FinalFamilyAt`
  forces `AnalyticRank E 1`); the text's families satisfy the omitted clause, so no leaf is
  falsified, but the leaves are asked of more families than the text constructs;
* the companion's primes lie in the fixed support before `δ_o` (`CompanionLeaf`); the address leaf
  reads the odd source on its own filter (lane RC24's intrinsic odd filter), so the fresh prime of
  `k` no longer vetoes the odd readings (fixed);
* closed: the coefficient dictionary's input (O.9) is consumed in the manuscript's form
  `a_p ≡ p + 1 (mod 4)` at every good prime (tex 9585, 9593–9594), proved for the actual curves
  (batch 3's `apModFour_curve_typeData`) and passed to the dictionary's weaker `ApEven` by
  `apEven_of_apModFour` (`AddressGenuine.LabelData.apEven₁`, `apEven₂`).
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
`addressLeaf_of_densityLeaf`; the odd witness of the stabilized tables is derived from the attained
odd minimum `δ_o ∈ depthSet`, tex 2590–2593, 10190–10199, 10501–10505, 10547; used only where the
staged package is asked for, `¬ W.OddEmptyUnit`). -/
theorem addressLeaf_of_densityLeaf_branch {ℓ : ℕ} {W : WData ℓ} (hℓ : Adm ℓ)
    (hcomp : CompanionLeaf W) (hdata : PreDataSpec W) (hprep : PreparedSpec W)
    (hδ : W.δo ∈ W.depthSet)
    (h : ¬ W.OddEmptyUnit → ZInQ.Manuscript.RC.AddressGenuine.AddressDensityLeaf W) :
    AddressLeaf W :=
  ZInQ.Manuscript.RC.AddressGenuine.addressLeaf_of_densityLeaf hℓ hcomp hdata hprep hδ h

/-! ## The leaves -/

/-- **The leaves that do not involve `δ_o`** (at an admissible `ℓ` with Selmer corank one and a
genus partner `h_*`), each with tex lines, kind and owner. -/
structure PreLeaves {ℓ : ℕ} (W : WData ℓ) : Prop where
  /-- The fixed support and the prepared filter (`StageSupport`: the support consists of primes and
  contains `2, 3`, the primes of `ℓ` and the primes of `h_*`; the prepared filter uses intrinsic unit tests and only prime exclusions at the enlarged
  support, `preparedSeparated`) (definitions; tex
  1974–1975, 2404–2410, 2460–2461, App F 8227–8228, 8246–8258; owner RC0). It replaces the former leaves
  `data_spec : PreDataSpec W` and `prepared_spec : PreparedSpec W`, both now PROVED: the data
  specification from it and the stage link of `odd_staged` (`PreLeaves.data_spec`, by the stage
  construction's `preDataSpec_preparedStages`), and `PreparedSpec` from it alone
  (`PreLeaves.prepared_spec`). -/
  stage_support : StageSupport W
  /-- The specification of the data behind the partitionable auxiliary factor (`AuxFactorInputs`:
  the type data, the conductor on the support, the even sources per total type with RC2's
  coefficient rules and vanishing off their filter, a unit seed at every prepared total type, and
  the meaning of `Partitionable` on the filter of negative squarefree parameters prime to the
  support, a forward implication only; definition + ELLIOT; tex 2016–2185, 2296–2297, 2343–2401,
  App G 10055–10150; owners RC0, RC2, batch 3 AuxFactor / CoefficientDictionary). DEPARTURE: the seeds
  are asked only at the prepared types (the text prepares them "for every total type", tex
  2360–2361, 10131–10132, which is false at negative types of root number `−1`; the prepared types
  include every type that occurs, tex 10139). The auxiliary factor itself is PROVED from it (the
  dictionary argument at the prepared types, `auxFactor_of_inputs`). -/
  aux_factor : AuxFactorInputs W
  /-- The remaining inputs of the even upper bound (3.3b) (`EvenUpperRC11Inputs`): (3.3a) at the units
  of the normalized even symbol, lane RC11's (3.2) (`EvenScalar32`), and the realized cubes of units
  at the partitionable parameters (ELLIOT; Proposition `ex:sec7-even-upper`, tex 2295–2341, (3.3b)
  at 2333–2336, App G 10079–10129; owners RC11, batch 3 EvenUpper, RC2). The missing address on the
  cubes is PROVED (batch 3's Boolean comparison from lane RC1), at the single precision the consumer
  uses (`EvenUpperInputsAt`). NOTE: the level `N₀` of the binary families is existential (the text's
  is the level of `E_ℓ`, tex 1836–1837, 1864–1869); with `N₀ = 0` the families are constant, so the
  cube clause then holds only at bases that are already units; not needed for soundness. -/
  even_upper : EvenUpperRC11Inputs W
  /-- The odd side's genuine objects with the constructed stages (`OddStagedInstance`, in
  `StageData.lean`): GenusOdd's objects of (3.4) — lane RC11's normalization of `L_*` (GLUE
  Birch–Manin; tex 1825–1830, 7175–7177), the newform data of `E`, `L_*(h_*)` over the lattice's
  `Ω⁻` a nonzero rational (GLUE Manin–Drinfeld, tex 2404), the Heegner selections and the
  identification of the interface data (definitions), the genus partner's squares at the level and
  the final `k`'s conditions (ELLIOT; tex 2404–2416, 2595–2603) — and, at the same genus selection,
  lane RC23's visibility models: the multiplier killing native torsion (ELLIOT + PRINT Silverman AEC
  VII.3.1), the stage maps (interface data), the odd sign of admissible parameters (GLUE: the twist
  root-number formula), the theta side and the comparison argument of (O.7) (ELLIOT + PRINT
  Cornut–Jetchev; tex 9101–9445); owners RC11, batch 3 GenusOdd, RC13, RC23. Then the fixed witness
  with the stages of the Appendix F construction (tex 2460–2536, 8225–8405): `D_w` in the prepared
  filter with its selected genus datum (definitions), the outputs of the detector construction (a
  Galois-fixed point of `E^{(D_w)}`, a division tower, the auxiliary field, the detecting element,
  the fixed row with value `2^{a+1}` at its square, an actual detecting sequence; ELLIOT,
  Proposition `ex:app-detector`, PROVED by the construction's `exists_detector_stages` from a
  nontorsion rational point, PRINT Serre and GLUE no CM, `StageDataNonVacuity`),
  the stage fields of the data being the construction at that sequence (`StagesFrom`, definitions;
  owner RC0), and the specialization identity `WitnessSpecialization` (ELLIOT + GLUE, tex
  8392–8398; the open input; owner: the Appendix F stage construction, `RC/Stages/Witness.lean`).
  PROVED from it: (O.2) at the witness (`OddStagedInstance.witnessValuation`, by the construction's
  `witnessValuation_withStages`; formerly the field `OddInstance.hO2` of this leaf), hence
  `OddInstance` (`PreLeaves.odd`), (3.4) (`gz34Target_of_genusOdd`), (O.8)'s inputs
  (`visibilityInputs_of_oddInstance`) and the fixed witness (`witnessLeaf_of_oddInstance`).
  Conclusion-shaped part: the theta side and the comparison argument exist for every `λ` with
  `a_θ ≡ c₀ λ (mod 2^{M_θ})`, so together they are (O.7) itself; the point side `λ = lamOf` is
  genuine. Caveat: the one field `ev` (the stage maps) is read at every admissible parameter, by
  `lamOf` in the comparison argument, and at the witness by `WitnessSpecialization`; both requirements permit stage maps that vanish away from `D_w` when matching
  witness-supported coefficients and theta models are supplied. The fields do not identify
  `ev` with reduction at the constructed primes. -/
  odd_staged : Nonempty (OddStagedInstance W)
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
  (`regular_of_genuineSwitchData`), and RC16's (3.5) over RC20's genuine valuation. Caveat: the
  configuration family is existential and only required to be some genuine Galois Selmer data with
  `t = X`. With one genuine complex of the homotopy type of `[k --0--> k]` at each `𝔭` (true, not
  formalized), its regularity part is equivalent to `uprim h k' ∈ Λ[1/2]` at the companion pairs,
  Elliot's regularity assertion (ELLIOT). Over the actual genuine complexes no switch step can be
  formed (`fG`: `C¹_cont` is infinite-dimensional), so the actual family witnesses the regularity
  part only when `s(𝔭) = 1`. UNCLEAR/DEPARTURE: batch 3's `GenuineSwitchData.primitive` requires the
  actual class to be primitive, which the text does not supply. DEPARTURE: one model family with one
  size function `nOf` is fixed for all ring instances before `A`, stronger than the text's per-`A`
  bound (tex 4936–4940, 4453–4463). -/
  eq35 : Eq35InputsGenuineGG W

/-- **The data specification from the leaves** (PROVED: the fixed support and the stage link of the
staged odd instance, by the stage construction's `preDataSpec_preparedStages`; formerly the leaf
`PreLeaves.data_spec`). -/
theorem PreLeaves.data_spec {ℓ : ℕ} {W : WData ℓ} (hp : PreLeaves W) : PreDataSpec W :=
  let ⟨I⟩ := hp.odd_staged
  (I.preDataSpec hp.stage_support).1

/-- **The prepared filter is positive, squarefree, `≡ 1 (mod 8)` and prime to the support**
(PROVED from the fixed support, `StageSupport.preparedSpec`; formerly the leaf
`PreLeaves.prepared_spec`; tex 2344–2346, 2404–2410, App G 10059–10062). -/
theorem PreLeaves.prepared_spec {ℓ : ℕ} {W : WData ℓ} (hp : PreLeaves W) : PreparedSpec W :=
  hp.stage_support.preparedSpec

/-- **The odd instance from the leaves** (PROVED: (O.2) at the witness from the stage construction
and `WitnessSpecialization`, `OddStagedInstance.toOddInstance`; formerly the leaf
`PreLeaves.odd`). -/
theorem PreLeaves.odd {ℓ : ℕ} {W : WData ℓ} (hp : PreLeaves W) : Nonempty (OddInstance W) :=
  let ⟨I⟩ := hp.odd_staged
  ⟨I.toOddInstance⟩

/-- **The leaves at the chosen `h_*` and `δ_o`**, each with tex lines, kind and owner. -/
structure PostLeaves {ℓ : ℕ} (W : WData ℓ) : Prop where
  /-- The final companion `k` (`CompanionLeaf`; tex 2595–2603, 2720–2721; owner RC2 / RC11 / RC13):
  PRINT-derived (`exists_companion`, from Hoffstein–Luo, BFH, BCDT and `w = −1`, gives every
  conjunct but the support one) + definition (its primes in the support after `k` is fixed;
  DEPARTURE, see the module docstring). The skeleton itself uses only `k < 0` and `L_*(k) ≠ 0`
  (`fixedFieldPackage_of_steps`). -/
  companion : CompanionLeaf W
  /-- In the remaining branch (`¬ W.OddEmptyUnit`, the scope of the address construction: tex
  2588–2593, 10268–10270, 10501–10505; the odd-empty-unit branch needs no address), the inputs of
  the address construction at `δ_o` over the genuine Galois objects (lane RC24's
  `AddressDensityLeaf`): the label data with the intrinsic odd filter (the odd source's own filter,
  agreeing with the stage support away from `W.S`; tex 2027–2029, 2603, 9481–9483, 10594–10596), a
  fresh prime of `k`, budgeted density models of the odd stage source on a set of stages of the
  ultrafilter and of the transported even source at every budget (GLUE trace identities; ELLIOT
  readings, tex 9671–9745, 9905–9918; GLUE Kummer, openness and unramifiedness of `N_U`, tex
  9663–9669, 9745–9750), the odd and prepared filters, the even filter, the K-split seed (given
  `Adm ℓ`, `FreshPrime` and `k` odd squarefree, equivalent to a nonempty K-split unit of the even
  reading: the conclusion of Lemma `ex:sec7-ksplit-seed`, kept in the text's conditional form, tex
  2636–2641) and the even reading ((F.1)'s conclusion for the chosen reading; ELLIOT; App G
  10079–10861, App F 9447–9976; owners RC24, RC2, RC12, RC11, RC3, batch 3). The odd witness is
  not an input: it is derived from the attained minimum `δ_o` (`addressLeaf_of_densityLeaf_branch`).
  Everything else of the address package is PROVED over genuine `G_ℚ`, Frobenius elements and
  characters, Chebotarev by the repository's density theorem. -/
  address : ¬ W.OddEmptyUnit → ZInQ.Manuscript.RC.AddressGenuine.AddressDensityLeaf W
  /-- The inputs of (4.6) at every address (`CalibrationInputsH`): the two-primary Ш and torsion
  orders (ELLIOT + PRINT Kolyvagin), the component groups at `p ∣ k` through good models up to
  isomorphism and Edixhoven's print in its model-free form (PRINT Edixhoven Thm 5.3, Rem. 5.4.1, as
  GLUE), the pullback and comparison data, Cassels–Milne isogeny invariance at the genuine canonical
  regulators (PRINT Milne ADT I.7.3 + GLUE), the moving prime in the output form of RC17's moving
  character, and the triangular Kummer model whose quotient block is the direct sum of the local
  blocks at the moving and active places, up to changes of basis with central unit determinants
  (ELLIOT; tex 3987–4141; owners RC15, RC9, RC19, RC4/RC17, batch 3 Calibration). PROVED from them:
  the isogeny and regulator data (RC19's `regulator_inputs_sumDiff`, with `alpha = I`, `beta = J`
  the cardinalities of the actual cokernels of `diffMap`, `sumMap` on the torsion-free quotients:
  `CalibrationModelR.nonempty_model_index`), the free generators (from `Prints`), the component
  fields, the moving-prime fields, the quotient length `2v₂N + 4ω` and `hvprim` (batch 3's
  Calibration). Conclusion-shaped in part: the local-block Kummer model is equivalent to the
  pre-Milne valuation formula, and the Milne, period, moving-prime and Kummer-model data are
  existential parameters not tied to the genuine `𝒜`, Néron models or cochain complexes. Scope
  departure: this field is also requested in Branch 1; the manuscript constructs these objects only
  in the remaining branch (see `RC/Skeleton/Steps.lean`). -/
  calibration : CalibrationInputsH W.toRCData
  /-- The inputs of (4.7) at every address, tied to the family and the address
  (`CommonCoordinateInputsG`): an existential coefficient ring `R` with `χ : R →+* ℚ₂[[t]]` (it is
  not `𝒪[G]`: no `t`-preserving ring map `𝒪[G] → ℚ₂[[t]]` exists, and `η_x` may have a pole, tex
  4153–4155, 4318–4320), with
  `x(g_q) = (−1)^{λ_q(x)}` at the family's graph primes (definition), the Euler-factor identity and
  the invertibility of `e_q` (ELLIOT, the Frobenius model at `q`), the Frobenius matrices of
  determinant `p` at the unused primes `λ_p(x) = 0`, and at each relaxation step the support
  triangle in the original integral bases with functionals from retained Selmer data
  (`NaturalStep`; ELLIOT + GLUE; tex 4142–4328; owners RC15, RC4, batch 3 CommonCoordinate). PROVED
  from them: `x(g_q) = ±1`, the unused primes, `λ_R ∘ i = e_q λ_P`, the multi-prime (4.7) and
  `ε_q ∈ Λ^×` (batch 3's `commonCoordinateInputs_of_natural`). Conclusion-shaped: equivalent to
  (4.7) together with `ε_x = 1` where no graph prime is unused; the ring, the matrices and the
  retained Selmer data of each relaxation step are existential and not tied to the address's Selmer
  complexes. Scope departure: this field is also requested in Branch 1 (see
  `RC/Skeleton/Steps.lean`). -/
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
  Caveat: the configuration family is existential and only required to be some genuine Galois Selmer
  data with `t = X`. With one genuine complex of the homotopy type of `[k --0--> k]` at each `𝔭`
  (true, not formalized), the leaf is equivalent to `∀ F x, InLamHalf (D.uPrim F x)`, i.e. Elliot's
  regularity assertion (ELLIOT). Over the address's own genuine complexes no switch step can be
  formed (`fG`: `C¹_cont` is infinite-dimensional), so the address's family witnesses the leaf only
  when `s(𝔭) = 1`. UNCLEAR/DEPARTURE: batch 3's `GenuineSwitchData.primitive` requires the actual
  class to be primitive, which the text does not supply. DEPARTURE (scope at `x = 0`): the text
  proves the base clause only at full Selmer corank one for `E/K` (tex 4922–4923, 5196–5199,
  4350–4351); the leaf asserts it at the base of every final family without that hypothesis. For the
  chosen `k` it holds (tex 2598–2599, 2616–2626); in Branch 1 the leaf asserts it of free data.
  Caveat on the discharge: the configuration families must NOT be taken over the finite-level actual
  coefficient modules `M_i = (T₂E ⊗ A_i)(χ_hΨ_i)` (tex 2780–2830): over the residue fields `k(𝔭)`
  these give only zero fibres, so a leaf tied to them is vacuous (lane RC28's
  `regularityInputsActual_iff`: `RegularityInputsActual u ↔ u = 0`). The actual fibres must come
  from the `Λ`-adic module (`RC/LambdaCoef`, in progress). -/
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
  RC26, batch 3 ClearingComplex / CoordLink / RankCounts / PairedFunctional)
  (`Identification2G.support_qis` derives the support quasi-isomorphism from the PRINT
  `NekovarProp788ii`; the deduction does not use it). PROVED from
  them: the cancellation factor `κ = det B`, the transported functional `μ = λ ∘ incl`, E1a, E1b
  for the Knudsen–Mumford coordinate, the Smith model, the generic patterns, the entry poles, the
  budget (5.7), and (5.9) by lane RC7 over RC20's genuine `𝒪`, with the exponent `a = 0`. The
  field `K` is existential (not pinned to the text's field; the conversion does not use it).
  Caveat: the family clause is vacuous, and `Identification2G` is an abstract family identification
  with a finite unramified-support comparison (its new blocks in degrees two and three); it does
  not model the full-condition singular-quotient triangle (5.6) of tex 5234–5238, 5398–5403. Scope
  departure: this field is also requested in Branch 1 (see `RC/Skeleton/Steps.lean`). -/
  clearing_model : ClearingInputsG W.toRCData
  /-- **Lemma `ex:arith-base-zero` at the base, on the text's named steps**
  (`BaseZeroLeafInputsText`; ELLIOT, tex 4330–4376; owners RC15, RC19, RC25, RC30, batch 3
  HeegnerCohomology, RankCounts, BaseZeroLam), with the height formula (Cai–Shu–Tian Thm 1.1 from
  `Prints`, lane RC19), (4.7) at the base, `ũ₀ ∈ Λ[1/2]` and the package's datum PROVED (lane
  RC25's `baseZeroTarget_of_leaves`, from `common_coordinate` and `prim_regular`; tex 4369–4373,
  5703–5706). Inputs:
  * the conductor-one Heegner data in the form `HeegnerDataSqrt` (PRINT/GLUE: BCDT,
    uniformization, Eichler–Shimura, CM theory, Galois descent; tex 2836–2838, 2915–2932), with
    `K = ℚ(√k)` split at `2` (definition, tex 2599, 2720) in place of the factorization
    `L(E/K,s) = L(E,s)L(E^{(k)},s)`, which is PROVED from `RCLeaves.artin` (lane RC27's
    `lFactorizationConductorOne_of_artin`; tex 4345–4346, 5736);
  * the two-term model of the primitive complex at the base and its retained cycle (ELLIOT +
    GLUE; tex 4341–4369);
  * the central comparison: the central degree-one cohomology is
    `V₂ Sel_{2^∞}(E/ℚ) × V₂ Sel_{2^∞}(E^{(k)}/ℚ)` (`CentralSelmerComparison`; ELLIOT + GLUE; tex
    4350–4352, 3952–3962, 5305–5311), from which `rank ρ(Dm) = m` is PROVED with the lemma's
    hypothesis `SelmerCorankOneOverK` (lane RC30's `hcentral_of_selmer`);
  * the pairing with its Leibniz identity (GLUE), the chain map `ψ` and the cocycle `c z` of
    Proposition `ex:arith-paired-functional`: the functional is `PD(·, ψ(c z))` (definition, tex
    3752–3754) and its closedness is PROVED (tex 3860–3863; the RC53 group's `baseLam_closed`);
  * the coordinate statement for the row of that functional (Definition `ex:arith-coordinate`,
    tex 3877–3892);
  * the retained inner-limit data of (4.5) at the base (`InnerLimit45Base`; tex 3912–3921,
    3952–3968; the stage boundaries ELLIOT, the inner limit PROVED, the comparison definitions),
    from which the limit statement `hlim` is PROVED (lane RC30's `toBoundary45Base`);
  * `hprimId` (definition).
  Conclusion-shaped: as abstract inputs these are equivalent to the fields they replace (an
  `InnerLimit45Base` exists iff `z̄ = L κ(P)` with `L ≠ 0`, lane RC30's
  `nonempty_innerLimit45Base_iff`; the central comparison exists iff the central kernel has the
  Selmer dimension; a closed functional is a paired functional for a degenerate pairing); the gain
  is that `hcentral`, `hlim` and `hlam` are now proofs from the steps of the text. For a torsion `P`
  the core is equivalent to "`u_{prim,0} ∈ Λ_(t)` and `u_{prim,0}(0) = 0`", the lemma's conclusion
  (tex 4346–4348, 4362–4369). -/
  base_zero : BaseZeroLeafInputsText W.toRCData

/-- **Every remaining hypothesis of Theorem 5.3 beyond the blueprint's `Prints`.** -/
structure RCLeaves where
  /-- Hoffstein–Luo over newforms (PRINT, Math. Res. Lett. 4 (1997), §1, Theorem, pp. 435–436, as
  stated by lane RC8; tex 1984–1991, App G 9995–9999, 10016–10027, 10049–10053). -/
  hlPrint : PrintsAnalytic.HoffsteinLuoTheorem
  /-- The twisted functional equation over newforms, for `(D, N) = 1` (GLUE, textbook: Shimura,
  Atkin–Li; recalled as display (1) of Hoffstein–Luo, Math. Res. Lett. 4 (1997), p. 435, and by
  Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990), p. 543; lane RC8). The manuscript uses it
  without citation at tex 2346, 8586–8588, 10025–10026 and 10044–10047. -/
  twistedFE : PrintsAnalytic.TwistedFunctionalEquation
  /-- Modularity in newform form: every elliptic curve over `ℚ` has a weight-two newform with the
  same `L`-function (PRINT: BCDT Thm A, author manuscript p. 1, with Introduction condition (2),
  p. 3; GLUE: Atkin–Lehner/Carayol, the eigenform of level `N(E)` is the newform; tex 1779–1784;
  lane RC8). -/
  modularNewform : PrintsAnalytic.ModularNewform
  /-- The interface data, given the genus partner `h_*`: chosen by whoever discharges `RCLeaves`
  and constrained only by the leaves (see the module docstring). -/
  data : ∀ ℓ : ℕ, ℤ → WData ℓ
  /-- The leaves not involving `δ_o`, at every genus partner. -/
  pre : ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) → ∀ h : ℤ, IsGenusPartner ℓ h →
    PreLeaves ((data ℓ h).withHstar h)
  /-- The leaves at the chosen `h_*` and the attained odd minimum `δ_o`. DEPARTURE (scope):
  demanded in both branches, the address leaf excepted. The text constructs `k`, the family and the
  coordinates only in the remaining branch (tex 2589–2593; (5.6)–(5.9) are stated "in the branch
  where the odd empty configuration is not a unit", 5209–5211, 5228–5229). A discharge chooses the
  companion of tex 2595–2600 in Branch 1 as well; that choice does not use the branch hypothesis. -/
  post : ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) → ∀ h : ℤ, IsGenusPartner ℓ h →
    ∀ δ : ℤ, IsLeast (data ℓ h).depthSet δ → PostLeaves ((data ℓ h).withChoices h δ)

/-! ## The steps from the leaves -/

/-- Absolute convergence of `L(E, s)` on `Re s > 3/2` (PROVED, no print and no field of `RCLeaves`:
batch 3's `hasseConvergence_proved`, from Hasse's bound, Silverman AEC, second edition, Theorem
V.1.1, proved through the Frobenius isogeny; used uncited at tex 1590 and 6323). -/
theorem RCLeaves.hasse (_L : RCLeaves) : PrintsAnalytic.HasseConvergence :=
  ZInQ.Contrib.CloudB3RC53.Hasse.hasseConvergence_proved

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

/-- The Artin factorization of the ring-class `L`-functions (PROVED from the `modularNewform` print
alone; batch 3's `artinFactorization_unconditional`: Hasse's bound is proved, and the factorization's
own hypothesis splits every level prime in `K`, so the inert primes are good and the proved good
case of the inert clause applies; tex 2411–2440). (3.4) thus rests on `modularNewform` alone, with
no local GLUE. -/
theorem RCLeaves.artin (L : RCLeaves) : ZInQ.Contrib.CloudB3RC53.GenusOdd.ArtinFactorization :=
  ZInQ.Contrib.CloudB3RC53.Hasse.artinFactorization_unconditional L.modularNewform

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
      (addressLeaf_of_densityLeaf_branch hadm hq.companion
        ⟨hp.data_spec.support_prime, hp.data_spec.support_base, hp.data_spec.stages_hyper,
          hp.data_spec.stages_index, hp.data_spec.admissible_split, hp.data_spec.prepared_one⟩
        hp.prepared_spec hδ.1 hq.address)
  have h47 : CommonCoordinateTarget W₂.toRCData :=
    commonCoordinateTarget_of_inputs (commonCoordinateInputs_of_G hq.common_coordinate)
  have hheight : HeightOneTarget W₂.toRCData :=
    heightOneTarget_of_inputsG _ hq.prim_regular h47
  exact rcSteps_of_targets _ hL₂ hG₂ hvis₂ hstages hone
    (companionTarget_of hL₂ hq.companion)
    ⟨Cper, h34k⟩ hfam (calibrationTarget_of_H P hadm.1 hq.calibration) h47 hheight
    (clearingTarget_of_G _ hheight hq.clearing_model) (BaseZeroAssembly.baseZeroTarget_of_leaves P
      (commonCoordinateInputs_of_G hq.common_coordinate)
      (primRegularityInputs_of_G _ hq.prim_regular)
      (baseZeroLeafInputs_of_text L.artin hq.base_zero))

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
