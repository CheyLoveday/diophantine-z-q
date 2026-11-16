# javanpeykar-dict log

Target: bundle field `javanpeykarBound : ZInQ.HeightSplit.JavanpeykarBound` (ZInQKernel/OneProof/H/TailY.lean:522; bundle HDec.HSyn.OpenResearchLeaves26), base 2880fef1.
Verbatim statement: scratch/javanpeykar-dict/Statement.lean.txt.

## Setup
- 11-16 05:05 .lake/build was empty; copied ~/dzq-wt/dict-galois/.lake/build and lean/.lake/build (TailZ41-era build; modules changed since are rebuilt by lake).

## Findings
- 05:15 VERIFIED (compiled, scratch/javanpeykar-dict/JavanpeykarDict.lean §1): `isStableFaltingsHeight_of_iso`: IsStableFaltingsHeight J x → IsStableFaltingsHeight J' x for an isomorphism e : J.X ≅ J'.X with IsMonHom e.hom (transport of group models / metrized models through e_L; height, Néron property, semistability preserved).
- 05:18 VERIFIED (compiled, standard axioms; scratch/javanpeykar-dict/JavanpeykarDict.lean, Axioms-output.txt):
  - §2 `abVarIso_picZero_of_isJacobian` (copied from isj1-dict R16IsJ1Dict.lean): kernel Jacobian ≅ every tensor-compatible Pic⁰ representative (ofVendored V).
  - §3 `dim_eq_genusK`: IsJacobian X P₀ J aj → J.dim = arithmeticGenus_K(X) (vendored Pic⁰ smooth of genus dimension + vendored topologicalKrullDim_eq_of_smoothOfRelativeDimension + homeomorphism invariance); `genusBar_eq`: genus of X_{K̄} = genus of X (vendored arithmeticGenus_pullback).
  - §4 new leaf `JavanpeykarPrinted` (X₀/K, X = X₀ ×_K K̄, Jac = Pic⁰ representative V over K, g = h¹(X_{K̄}, O), Belyi function t ∈ K̄(X_{K̄}) over K̄, d = [K̄(X):K̄(t)], published stable height of V); glue `BelyiBaseChange` (K-rational Belyi function → Belyi function of X_{K̄}, same degree; not proved); `javanpeykarBound_of_printed : JavanpeykarPrinted → BelyiBaseChange → JavanpeykarBound`.
- VERIFIED: `lake build +ZInQKernel.Contrib.OneProof.JavanpeykarDict +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` OK (13699 jobs); `#discharges` (scratch/javanpeykar-dict/Discharges-output.txt): DISCHARGES [OpenResearchLeaves26.javanpeykarBound] by JavanpeykarDict.javanpeykarBound_of_printed, still assumes [JavanpeykarPrinted, BelyiBaseChange], standard axioms.
- Next (stretch): prove BelyiBaseChange from a printed Stichtenoth leaf (constant field extensions unramified) + Lean glue (function field of X_L = K(X) ⊗_K L via Mathlib isIso_pushoutSection_of_isAffineOpen; degree; Belyi transfer).
