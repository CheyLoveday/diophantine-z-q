# reduct-b results log

- RBBase.lean = scratch/reduct-glue/ReductGlue.lean minus `#print axioms` lines (Base = kernel TailZ7, Body = kernel
  TailZ14 modulo imports/header, VERIFIED by diff 11-14 17:55).
- t.sh: compiles a test file against /tmp/rblib/RBBase.olean (built by `lake env lean -R scratch/reduct-b
  scratch/reduct-b/RBBase.lean -o /tmp/rblib/RBBase.olean`, 50 s, 7.6 GB).
- K1 (11-14 18:20) VERIFIED compiled: `ReductB.semistableReductionDVR_of_raynaud (hR : RaynaudSemistable)
  (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme) : SemistableReductionDVR`,
  axioms [propext, Classical.choice, Quot.sound]. New lemmas: `mem_of_isSeparable_of_fixed_inter`,
  `exists_rational_of_fixed_etale_inter` (Galois descent to an intermediate field F ⊆ K̄ for points of étale
  K-schemes), `fixedTorsionRational_inter`, `exists_three_le_isUnit` (3 or 4 is a unit in a local ring, 4-3=1).
  The AlgebraicClosure K' vs K̄ transfer: κ' := IsAlgClosed.lift : K̄ →ₐ[K'] (K')‾ (a K'-embedding, so
  κ'∘val = ofId), needs explicit `Module.IsTorsionFree K' _` instances (else typeclass timeout).
- K1.lean renamed Body.lean (namespace ReductB, imports RBBase).
- Route B (11-14 18:45) VERIFIED compiled, standard axioms:
  `strictHenselizationNeron_of_pair : StrictHenselizationPair → StrictHenselizationNeron` (instance K'=K, O'=O,
  `comap_algebraMap_self`); `raynaudSemistable_of_SH_pair : RaynaudSemistableSH → StrictHenselizationPair →
  MulEtale → RaynaudSemistable`; `semistablePersistsDVR_of_SH_pair : SemistablePersistsSH → Pair →
  SemistablePersistsDVR`; `semistableReductionDVR_of_SH_pair` (K1 ∘ Route B); `three_fields_of_printed`.
- Route B-CP VERIFIED compiled: defs `RaynaudSemistableSHcp`, `SemistablePersistsSHcp` ([CharZero K]
  [PerfectField κ(O)] on the SH forms), `RaynaudSemistableCP`, `SemistablePersistsDVRcp`, `SemistablePersistsDVRnf`;
  `cp_of_general` (the cp SH leaves are specializations of the DVR forms); `raynaudSemistableCP_of_SH`,
  `semistablePersistsDVRcp_of_SH` (CharZero E from injectivity, PerfectField κ(P) by
  `Algebra.IsAlgebraic.perfectField` from IsSHNeronExt's algebraic residue extension);
  `perfectField_residue_nf` (κ(O) finite for a DVR of a number field: 𝓞/𝔭 finite, `resIso`);
  `persistsNF_of_cp`; `semistablePersists_of_leaves_nf` (SS3 from the nf form, reduct-split's proof retyped).
- FINDING: uses of the three fields (grep of ZInQKernel, VERIFIED): raynaudSemistable → TailZ15 r6 :=
  raynaudCriterion_leaves (PkgI2.RaynaudCriterion: ALL fields K); semistableReductionDVR → TailZ9 r8 :=
  grothendieckMonodromy_final' (PkgI2.GrothendieckMonodromy: ALL fields) and TailZ15 SS1 (number fields);
  semistablePersistsDVR → TailZ15 SS1, SS3 (number fields only). So the cp forms cannot fill raynaudSemistable
  or semistableReductionDVR without restricting r6/r8 (used in TailF/H/I/K, LF4T5); they can fill
  semistablePersistsDVR's two uses.
