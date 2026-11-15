# gap-triage — summary

Read-only triage of the 59 bundle fields and 6 top statements of `ZInQ.OneProof.frozenTarget` (base e38375b3; w63
read with `git show`). Report: `docs/research/gap-triage.md` (ranked attack list first). One row per statement:
`scratch/gap-triage/triage.tsv` (65 base rows + 7 w63 rows). Results log: `scratch/gap-triage/log.md`. Probes
(all exit 0, standard axioms): `GlueProbe.lean`, `MCRQuotNV.lean`, `VerifyProbe.lean`, `ClosureProbe.lean`.

**Findings (VERIFIED):**
- `bdRInvariants` is used only syntactically: its `t23` goes only into `G9Glue`'s argument `_hT23`, which no proof uses.
- On w63, `raynaudKernelBound` gives only the half of R20 that `transfer_core` never uses.
- Under the glue field, `CoverModelOfHeckeN` (Lemma NV) is not needed. `ModelYIrreducible` = the chain's
  `HeckeIrreducible`, proved from `deligneComponentsY3Printed`. mcr-quot's composite without it compiles
  (`final10`).
- `P1SchemeQ` has every piece in CloudW07 (`#check`ed).
- Igusa ψ₄, χ₁₀ are used only at `M4`, `M6`.
- t5-glue's tip (`RingClassLattice`) is not merged in the base or w63.

**Ranked attack list** (base each on w63; each result a scratch theorem):
1. Semantic prune of `bdRInvariants` + `raynaudKernelBound` (T1, −2).
2. `ThetaModularityM46` for ψ₄, χ₁₀ (T1–T2, −2).
3. `P1SchemeQ` from CloudW07, plus the NV-free mcr-quot composite (T1; check cove-85 first).
4. `egaIV_8_10_5_openImm` (T1, −1).
5. `qmCentralizerCMC` by the lattice (T2, −1).
6. `GammaStarCocompactArea` (drops `shimizuCovolumeO1`; T2, −1).
7. `RingClassLattice` (hS → 2 printed leaves; T2).
8. `neronSchemeModelExistsDVR` from N1 + BLR (T1–T2; reading call on r6).
9. `yuThm11` as `YuB6Alg` (T2).
10. `blr_1_2_4.mp` (T2).
11. `milneIsogenyQuasiInverse` in characteristic 0 (T2).
12. `CMStabObj` (T2, glue).

Owner decisions with no agent:
- GZ swap to `FHNonvanishingCd` / `GrossZagierHeegnerCd` (compiled in the tree).
- `dsThm966` (Pan reading).
- `r1r2`'s unused `R1pi0Props` (and maybe `R1recProps`), for x6-fold.

**Tier counts** (65 base statements, cheapest route):

| T1 | T2 | T3 | T4 | done/superseded in w63 |
|---|---|---|---|---|
| 8 | 17 | 10 | 25 | 5 |

The T1 count includes three owner decisions and the glue's parts. Status: free 32, in flight 20, done 5, under
review 4, blocked 2, queued 2.

**Unchecked:**
- Every proof route and success odds (SPECULATIVE).
- Agent-only consumer traces (marked S in the tsv).
- The upstream issue numbers (no mapping in the tree).
- The R1recProps clause scan.
- Whether A10's spread-out argument avoids the "if" direction.
