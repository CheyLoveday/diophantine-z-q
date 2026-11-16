# persists-dvr results log

Base: wip/r6-nf 0bc2446d.

## Consumers of `semistablePersistsSHcp` at the base (VERIFIED, grep)
- Only reader: `HDec.HSyn.ss1_ss3_of14NF` (ZInQKernel/OneProof/H/TailZ26.lean L200-205), term
  `GapNeron.ss1_ss3_of_cpNF r.semistablePersistsSHcp r.strictHenselizationPair (semistableReductionDVR_of14 r t) ...`.
- All other occurrences are bundle declarations / copies (TailZ23 L693, TailZ25-29, TailZ33-34).
- `r.sga3_VIB_3_10`, `r.sga7_IX_3_3` are fields of `OpenResearchLeaves14` (TailZ23 L660, L662);
  `t.geomConnOfRationalPoint` of `OpenTextbookLeaves10` (used at TailZ23 L786).

## Plan (refined from triage2)
- No field change of `κ̄` needed: `ReductGlue.isSemistable_bcDVR_iff` (TailZ14 L1299) moves semistability of `𝒩` to
  `bcDVR hO 𝒩` given algebraic residue extension; prove that for finite K'/K (scaling argument).
- Core lemma over O': `U ⊆ (𝒩 ×_O O')_{κ̄'}` semi-abelian lands in `(W ×_O O')_{κ̄'}` (range = preimage of `idCompSet`),
  then compose with `j_{κ̄'}`; same `U, B, π, e`. No torus transport, no GeomConn for the fibre step.

## Build notes
- Copied build tree is stale (oleans 11-15 05:46, before r6-nf; NeronDVR.olean missing): first build rebuilds.
