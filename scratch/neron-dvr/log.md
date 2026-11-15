# neron-dvr results log

Base: 3782dac8e (wip/leaf-fold18 head; newest generation sixContactMin_of_open25, TailZ31).
Field `neronSchemeModelExistsDVR` lives in `OpenResearchLeaves19` (TailZ29 L41).

## Statements
- `GapNeron.NeronSchemeModelExistsDVRNF`: the field `ReductSplit.NeronSchemeModelExistsDVR` (TailZ7 L238) with
  `[NumberField K]` added after `[Field K]`; otherwise verbatim.
- `GapNeron.neronSchemeModelExistsDVRNF_of_field`: `fun K _ _ O _ A => h K O A`.
- `GapNeron.neronSchemeModelExistsNF (hN1 : NeronSchemeExtensionExists)`: no `hB` needed —
  `GapBLR.neronLocalizesDVR_proved : ReductGlue.NeronLocalizesDVR` (BLRLocalizes.lean L848) has no hypotheses.

## Compile outcomes
- 2026-11-15 03:4x scratch/neron-dvr/Draft.lean: `neronSchemeModelExistsNF` compiles, axioms
  [propext, Classical.choice, Quot.sound] (VERIFIED). Proof: N1 →(neronModelExists_of_extension, L := K) group model
  over 𝓞_K → `GapBLR.neronLocalizesDVR_proved` → `ReductGlue.toO 𝒩 O` Néron over O → compose gen with
  `bcSelfIso A : (A.baseChange K).X ≅ A.X`.
- Pitfall (VERIFIED): with `bcSelfIso` a plain `def` (eqToIso inside), the bijectivity step hits a kernel
  deterministic timeout; `noncomputable irreducible_def bcSelfIso` fixes it. `CToPrinted.bijective_comp_iso`
  needs both Hom types in one category, so a two-category variant `bijective_comp_iso'` was added.

## Consumers of the field (live chain at base)
- Field passing only: TailZ29 L105, TailZ28 L108, TailZ27 L109, TailZ26 L115, TailZ25 L119 (down to OpenResearchLeaves14).
- TailZ23 L766 `ss1_ss3_of14` → `ReductB.ss1_ss3_of_cp` (uses hN only through `hasSemistableReduction_of` at number
  fields L, F O, L₀) — NF suffices (VERIFIED by reading TailZ23 L441-589).
- TailZ23 L780-781 `researchLeaves9_of_open14.r6 := raynaudCriterion_leaves … r.neronSchemeModelExistsDVR …`
  (TailZ14 L243): conclusion `PkgI2.RaynaudCriterion` over EVERY field (Objects.lean L1436).
- TailZ23 L803 `neronSchemeModelExistsDVR := r.neronSchemeModelExistsDVR` into `OpenResearchLeaves9`, read at
  TailZ9 L100-101 `r8 := grothendieckMonodromy_final' … r.neronSchemeModelExistsDVR …` (TailZ7 L1496): conclusion
  `PkgI2.GrothendieckMonodromy` over EVERY field (Objects.lean L1416).
