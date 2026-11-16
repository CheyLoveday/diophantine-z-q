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
- 01:40 Defs.lean (named Props: BranchConcl, TBNLocal, KummerBase, KummerUnram, EtaleBranch, BranchDescent) builds.
  Assembly.lean: `exists_kummer_field` (Ω = L(a^{1/N}, b^{1/N}) in an algebraic closure, separable, [Ω:L] prime to primes > N)
  and `tbnLocal_of_pieces : KummerBase → KummerUnram → EtaleBranch → BranchDescent → TBNLocal` COMPILED (no sorry),
  using `TPurity3.purityGlobalDim2'`.
- 02:15 `etaleBranch : EtaleBranch` COMPILED (EtaleBranch.lean): C = S'_𝔓' has maximal ideal (t,u)C
  (`Algebra.FormallyUnramified.map_maximalIdeal`), C/tC has principal maximal ideal, ū not nilpotent ⇒ DVR
  (`principal_local_structure`, adapted copy of `CurveGlueCI.isDomain_of_dim_one`).
- 03:00 `branchDescent : BranchDescent` COMPILED (Descent.lean): uniqueness by going down; normality by the
  colon ideal I' = (bS' + J) : a, prime avoidance over the finitely many primes over Q (minimal primes of QS'),
  and Tr_{Ω/L} as Reynolds operator (`trace_eq_sum_embeddings` into AlgebraicClosure L; J ↦ Q).
- 03:20 `kummerBase : KummerBase` COMPILED (KummerBase.lean).
- 04:00 `tameBranchNormal_of_local : TBNLocal → TameBranchNormal` COMPILED (Transport.lean).
- 04:05 contributor file ZInQKernel/Contrib/OneProof/Abhyankar.lean: `tameBranchNormal_of_kummerUnram : KummerUnram → TameBranchNormal`,
  `nvLocalInertia_of_kummerUnram` COMPILED. Only `KummerUnram` (step 2) remains open.
- 06:15 `kummerUnram_of_branch : KummerUnramBranch → KummerUnram` COMPILED (KummerUnram.lean, with helpers in
  KummerUnramBasic.lean: `height_under_eq_one`, `dvr_atPrime`, `unramifiedAt_of_local`; KummerUnramTame.lean:
  `tame_at` (e | N via Galois `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`, residue separability),
  `unram_of_baseChange` (from `TsKummer.unramBaseChange`)). Generic height-one primes done; the (f)/(g) case is the
  new named glue `KummerUnramBranch` (T2 at A_(f)). Contributor file: `tameBranchNormal_of_branch` COMPILED.
- 07:10 `branch_e` COMPILED (KummerBranch.lean): primes of the integral closure of A₁ = A[t₁, g] in Ω₁ = L(t₁) over (t₁)
  have index 1 over A₁ (T2 = `HDec.HSyn.t2_proved` at A_(f), adapted from `TsKummer.abhyankar_core`; freeness from
  `TPurity3.normalFreeDim2`).
