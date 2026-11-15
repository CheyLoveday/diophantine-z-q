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
