# pb-fix2 results log

## 2026-11-16 01:00 start
- Base e479bc562 (wip/pb-fix). Build tree copied from ~/dzq-wt/nv-local (c137bf8c7; differs from base only in
  ZInQKernel/Contrib/OneProof/{PanBerger*,SGRDirect*}.lean): .lake/build and lean/.lake/build.
- Plan:
  * Berger: K_0 as printed = W(k_K)[1/p] = FractionRing (WittVector p k_K), k_K = residue field of
    O_K = {x ∈ K : ‖x‖ ≤ 1}; predicates on the underlying space V (tensor form (B ⊗ V)^{G_K}).
  * Pan: leaf stated for one GaloisRep with all hypotheses on it, printed (pst, HT distinct weights on V,
    geometric Frobenius in the conclusion); glue applies it to the contragredient ρ^∨ (GaloisRep), with
    de Rham/HT transfers by the trace-pairing isomorphism V' ≅ V^* (pure linear algebra).
