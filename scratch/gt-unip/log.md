# gt-unip results log

Base ef2f6915 (leaf-fold18, top TailZ29). Build tree copied from ~/dzq-lf18 (74549021, same ZInQKernel except
TailZ29/ElkiesX6Star/Main), then `lake build +Main +Discharges +Contrib.OneProof.StrictHenselizationPair`:
12932 jobs, EXIT 0 (VERIFIED, scratch/gt-unip/build1.log).

## Consumer analysis (VERIFIED, read in source)
- Field `semistableUnipotent : ReductSplit.SemistableUnipotent` (TailZ7 L253): already forward direction only,
  (σ-1)²=0 one σ at a time (= echelon clause at σ=τ), over every DVR O of every field K, every algebraic closure Ω.
- r6 = `ReductGlue.raynaudCriterion_leaves` (TailZ14 L243) → `raynaudCriterion_final` → `raynaudCriterion_of_leaves`
  (TailZ7 L395): applies hU at Ω = AlgebraicClosure K, w ⊆ K̄ over O, B = ObjBridge.ofGrp A, hypothesis
  `hasSemistableReduction_of hN O B hss` (geometric semistability), σ inertia, all t. Forward only, σ=τ only.
- r8 = `grothendieckMonodromy_final'` (TailZ9): applies hU at K' ⊆ K̄, Ω = AlgebraicClosure K; inert (unipotent-b
  deps check).
- So no consumer needs less than the field in a way that removes an axis; the field is discharged as stated.

## Statements (ZInQKernel/Contrib/OneProof/UnipotentForward.lean)
- LEAF `UnipotentForward.SGA7_IX_3_5_ForwardGeom`: SH DVR, Ω sep closure, geometric semistability →
  (σ-1)*(σ-1)=0 for σ inertia. Reading risk on k(s) (only imperfect k(s)).
- LEAF `UnipotentForward.SGA7_IX_3_5_Forward`: same with both Res and Geom hypotheses (consequence of either reading).
- GLUE `UnipotentForward.SemiAbelianDescendsSepClosed` (unipotent-b's), proved for perfect k(s).
- PROVED `strictHenselizationInside_of_neron : NeronBaseChangeStrictHenselization → StrictHenselizationInside`.
- PROVED `semistableUnipotent_of_forwardGeom (hP) (hE : MulEtale) (hN : NBCSH) : ReductSplit.SemistableUnipotent`.
- PROVED `semistableUnipotent_of_forward (hP) (hD) (hE) (hN) : ReductSplit.SemistableUnipotent`.

## Compile outcomes
- 01:4x `lake env lean ZInQKernel/Contrib/OneProof/UnipotentForward.lean`: no errors, no warnings, 10 s (VERIFIED).
