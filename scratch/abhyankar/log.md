# abhyankar results log

Target: `SGRDirect.NVLocal.TameBranchNormal` (ZInQKernel/Contrib/OneProof/SGRDirectNVLocal.lean:627, from wip/nv-local 2e4ff83d).

## 2026-11-16
- 00:40 merged origin/wip/nv-local (clean, merge commit dc7718298). `lake build ZInQKernel.Contrib.OneProof.SGRDirectNVLocal` OK (VERIFIED).
- Available proved inputs (VERIFIED by #check from a scratch importing SGRDirectNVLocal, with `open HDec`):
  `TPurity3.purityGlobalDim2'` (purity, 2-dim regular local base), `TsKummer.unramBaseChange` (base change of
  unramified extensions of DVRs), `HDec.HSyn.t2_proved : PkgI2.AbhyankarDVR` (Abhyankar's lemma for DVRs, proved).
- Mathlib 4.35: `Algebra.HasGoingDown` instance for integral, torsion-free over integrally closed (VERIFIED, IntegralClosure/GoingDown.lean:49);
  `Ideal.ramificationIdx` is the length of `S_q/(q∩R)S_q` (VERIFIED, RamificationInertia/Ramification.lean:53);
  `Algebra.trace_eq_sum_embeddings` (VERIFIED).
- Assessment: statement plausibly TRUE (toric description of tame covers along a normal crossings divisor; SPECULATIVE until compiled).
