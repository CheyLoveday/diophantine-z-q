# nv-local results log

Task: prove `SGRDirect.NVLocalInertia` (ZInQKernel/Contrib/OneProof/SGRDirectNV.lean), base 56478c75.

## 2026-11-15 23:10 setup
- Build tree copied from ~/dzq-wt/sgr-direct (.lake/build, lean/.lake/build; same commit). Import of
  SGRDirectNV: 4 min cold, 7 s cached. VERIFIED.

## Analysis (paper; SPECULATIVE until compiled)
- NVLocalInertia is TRUE as stated (tame local structure at the closed point m=(p, dX-a): local tame pi_1 of
  the strict henselization minus V(p(X-b)) is Zhat'(1)^2; I_q, I_Q both inside the abelian I_P, I_P/I_Q =
  inertia of the residue field kappa(Q) at P). STANDARD (SGA 1 XIII 5.3, UNVERIFIED number).
- Full Lean proof needs Abhyankar's lemma in dimension 2 (Kummer base change by (X-b)^{1/N}, p^{1/N}, zeta_N,
  a new regular local base O[r]_{(w,r)}, purity, T2 at both divisors, base change of unramifiedness) -- not
  reachable by the deadline.
- Plan: reduce NVLocalInertia to one smaller GLUE Prop `BranchRegular` (purely local geometry of the
  normalization at the closed point, no Galois action, no arithmetic of residue fields):
  for every maximal ideal P of C = integralClosure Z[X] E over m_b there is exactly one prime Q of
  B = integralClosure Q[X] E over X-b with Q cap C <= P (unibranch), and every element of B/Q integral over Z
  is c1/c2 with c1, c2 in C, c2 notin P (the branch is normal at P).
  Then: tau in I_q fixes P, hence Q (unibranch); tau acts on kappa(Q) inside the inertia group of the prime
  P' = {c1/c2 : c1 in P} of O_kappa (normality); kappa(Q) unramified at p => tau trivial on kappa(Q)
  (|I(P'|P'_0)| = e(P'|P'_0) for the fixed field of tau, tower e(P'|p)=1).

## 2026-11-16 00:00 compiled (scratch/nv-local/Core.lean, `lake env lean`, standard axioms) VERIFIED
- `SGRDirect.NVLocal.eq_one_of_inertia_of_unram`: K number field, P prime of O_K with e(P|Z)=1, sigma in
  Aut(K) with sigma x - x in P for all x in O_K  =>  sigma = 1 (fixed field of <sigma>, card_inertia =
  ramificationIdxIn, ramificationIdx_tower).
- `primeOf`, `primeOf_isPrime`, `mem_primeOf_of_mem`, `inertia_primeOf`, `eq_one_of_primeOf`: the prime
  {y : y*psi(d2) = psi(d1), d1 in P, d2 notin P} of O_L for psi : C -> L with ker psi <= P and O_L inside the
  localization; an automorphism compatible with an action congruent to id mod P lies in its inertia.
- `zqIncl`, `galB`, `galC_mem` (plumbing).
- `BranchRegular` (def, GLUE) and `nvLocalInertia_of_branchRegular : BranchRegular -> NVLocalInertia`.
  `#print axioms`: [propext, Classical.choice, Quot.sound].

## 2026-11-15 23:25 Contrib file VERIFIED
- ZInQKernel/Contrib/OneProof/SGRDirectNVLocal.lean (imports SGRDirectElkies): the Core.lean content plus
  `heckeVertWitness_of_branchRegular` (HeckeVertWitness from r1r2, t5, qmAutCard, serreRigidity3,
  alFixedPoints, elkiesX6StarPrinted, BranchRegular). `lake build +ZInQKernel.Contrib.OneProof.SGRDirectNVLocal`
  OK (12 s).
- scratch/nv-local/Discharges.lean -> Discharges-output.txt: "#discharges: 63 open hypotheses, 1904 theorems
  checked, 7 discharge one" (none from this file, as expected: HeckeVertWitness is not an open field); all six
  listed theorems: [propext, Classical.choice, Quot.sound].
- scratch/nv-local/autofold.json (no fold; bypass as sgr-direct with branchRegular in place of nvLocalInertia).
