# neron-sh-proof results log

Base: 0caafe66. Target: `GapSHPair.NeronBaseChangeStrictHenselization` (field `neronBaseChangeStrictHenselization`,
statement in ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean:1527, bundle field TailZ29/TailZ33).

## Plan (route)
- Prove the stronger chain Prop `ReductGlue.NeronBaseChangeUnramifiedDVR` (TailZ14:1502); the field follows by
  `GapSHPair.neronBaseChangeStrictHenselization_of_unramified`.
- (A) algebra: O ⊆ O₁ unramified, K₁/K separable algebraic, separable residue ⇒ every finite subset of O₁ lies in
  an O-subalgebra of O₁ étale over O (integral closure D of O in L = K(S), étale locus at 𝔫 = 𝔪₁ ∩ D).
- (B) geometry: for R → R₁ an ind-smooth algebra (directed union of smooth subalgebras) with
  Spec K₁ = Spec R₁ ×_R Spec K, a Néron model over R base-changes to a Néron model over R₁ (BLRLocalizes pattern).

## Build setup
- copied .lake/build and lean/.lake/build from ~/dzq-wt/poincare-proof (same base 0caafe66).

## Part A (VERIFIED, compiled: scratch/neron-sh-proof/PartA.lean, Mathlib only)
- `NeronSH.exists_etale_subalgebra`: O DVR with fraction field K, O' a valuation subring of K', K'/K separable,
  O → O' local, every irreducible of O irreducible in O', κ(O')/κ(O) separable ⇒ every finite s ⊆ O' lies in an
  O-subalgebra B ⊆ O' with `Algebra.Etale O B`. Proof: D = integral closure of O in L = K(s) (finite, Dedekind,
  flat); 𝔫 = 𝔪' ∩ D; D_𝔫 DVR, unramified over O (Mathlib `FormallyUnramified.of_map_maximalIdeal`), étale at 𝔫
  (`IsEtaleAt.of_isUnramifiedAt_of_flat`), D[1/f] étale; each x ∈ s is c/t with t ∉ 𝔫 (valuation-ring argument in
  D_𝔫); B = image of D[1/(f∏t)]. Strict henselianity is NOT used.
