# deg-det results log

Base: wip/charpoly-ell 0d75311f + merge origin/main 0caafe66 (STATUS.md only). Build dir copied (reflink) from ~/dzq-wt/gaga-serre.

## Findings (before Lean)

- F1 (VERIFIED, read): consumers of `charPolyIndepOfEllAlgClosed`: `t7_of_algClosed5` (TailN/TailO) -> `PkgI3.CharPolyIndepOfEll`
  -> `G0AssembleMod.linkedTateData_of_local` (TailC:10262, abelian variety over a number field L'), and
  `R16Split.r16_of_printed` (TailZ35). All consumers are in characteristic 0. The field itself quantifies over every
  algebraically closed k (char p included), and the statement may not be changed.
- F2 (VERIFIED, math; same as charpoly-ell §4): counting ker(psi) on l-power torsion gives only |det T_l psi|_l = |deg psi|_l.
  An l-independent integer invariant with polynomial structure is needed: Mumford's proof uses that deg is a homogeneous
  polynomial function of degree 2g on End(X) (theorem of the cube + Riemann-Roch). No open field or leaf of the tree supplies
  it (checked: homFreeFiniteAlgClosed, mumfordTorsionAlgClosed, milneIsogenyQuasiInverse, weilPairingMumford, phiAmpleIsogeny,
  picZeroAbVar, uniformizationLeafAll, gagaMorphism). The analytic route (uniformizationLeafAll + gagaMorphism, open fields)
  covers only k = C (plus a Lefschetz transfer, absent) and not char p.
- F3: so the target (-1, no new leaf) is not reachable; plan: prove the algebra of Mumford's argument in Lean and isolate the
  two inputs: (P1) deg homogeneous polynomial function (LEAF), (L) |deg psi|_l = |det V_l psi|_l for isogenies (GLUE,
  = separable-degree/kernel count P3 + l-adic elementary divisors P4).

## Lean (scratch/deg-det/Algebra.lean, Mathlib only)

- 13:20 VERIFIED compiled: `DegDet.eq_Rs_of_mul` (multiplicative φ with φ(c)=c^n, φ(X-r)=(-1)^n P(r) is F ↦ ∏_{P(a)=0} F(a)),
  `DegDet.det_aeval_eq_Rs` (det F(M) = ∏_{χ_M(a)=0} F(a)), `DegDet.mult_eq_of_norm_Rs` and
  `DegDet.eq_of_norm_RsZ` (comparison lemma: monic P, Q over ℚ_ℓ with |∏_{P(a)=0}F(a)| = |∏_{Q(b)=0}F(b)| in
  PadicAlgCl ℓ for every F ∈ ℤ[X] with nonzero left side are equal).
