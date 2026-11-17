# htnew-print results log

Base: c0f3d085 (main; `git merge origin/main`: already up to date, 2026-11-16 22:50 PST).

## Inputs read
- ht-exists (7088f9ed): KatoHTExists (existence form, semisimple witness, geometric Frobenius, HT {0,k-1}),
  flag "pending reading" (3 reading points: filtration jumps / sign convention, Frobenius normalization,
  semisimplicity via Ribet). VERIFIED read (docs/research/ht-exists.md on the branch).
- ht-bypass (16db7d60): one consumer (G12Weight, l = 5, k >= 3). VERIFIED read.
- htnew-det: determinant route circular. VERIFIED read.
- newform-dict (e9683dac): IsNewform <-> Tau Ceti Newform, proved. VERIFIED read.
- On main: TateTwistInvariants and AxSenTate are PROVED (ZInQKernel/Contrib/OneProof/TateTwistInvariants.lean,
  AxSenTate.lean: ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof, axSenTate_proof). VERIFIED (read).
- CONTRIBUTING.md l.38-41: a new printed leaf counts published (flag unread); a leaf whose print may say
  something weaker is flagged pending reading and counts GLUE. VERIFIED read.

## Plan
New leaf robust to every ht-exists reading point: (i) normalization disjunction (arith Frob & HT {0,1-k}) or
(geom Frob & HT {0,k-1}); (ii) no semisimplicity (semisimplification preserves HT weights: proved in Lean);
(iii) trace-only Frobenius clause; (iv) printed newform (Tau Ceti Newform, via newform-dict).
- 23:35 EigenformHTPrinted.lean §1-§6a (HTDual copy; diagonal reps semisimple, invariant line, conjGR, diagGR) compiles (lake env lean, 17 s). VERIFIED.
- 00:05 §6b sum_finrank_Ysp_le, finrank_Ysp_le_diag (dim Y_i(rho) <= dim Y_i(diag) for upper triangular rho) compile. VERIFIED.
