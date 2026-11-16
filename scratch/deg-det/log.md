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
- 14:05 VERIFIED compiled (817 lines, axioms [propext, Classical.choice, Quot.sound]):
  `DegDet.Nt_mul` (generic multiplicativity: a polynomial function N on ℤ[X]/(R), multiplicative on pairs with nonzero
  values and N(1)=1, is multiplicative on S[X]/(R) for every ℚ-algebra S; Combinatorial Nullstellensatz on ℕ-points),
  `DegDet.P0_monic` (N(t − X) is monic of degree n for N homogeneous of degree n),
  `DegDet.det_eq_deg_abstract`: E ring, φ ∈ E with R(φ)=0 (R ∈ ℤ[X] monic), deg : E → ℕ homogeneous polynomial of
  degree n on ℤ[φ] (coordinates Σ x_i φ^i, i < deg R), deg 1 = 1, deg multiplicative on pairs with nonzero degree,
  ρ : E →+* M_I(ℚ_ℓ) with |det ρ ψ|_ℓ = |deg ψ|_ℓ when deg ψ ≠ 0  ⇒  det ρ(φ) = deg φ.
- 14:35 VERIFIED compiled (`lake build ZInQKernel.Contrib.OneProof.DegEqDetTate`, axioms standard; scratch/deg-det/CheckAxioms.lean):
  ZInQKernel/Contrib/OneProof/DegEqDetTate/Algebra.lean (copy of scratch Algebra.lean, namespace ZInQ.Contrib.OneProof.DegDet) and
  ZInQKernel/Contrib/OneProof/DegEqDetTate.lean:
  `DegDet.degEnd_mul_of_isIsogeny` (deg(ψχ) = deg ψ deg χ for isogenies; generic point preserved by surjective maps,
  tower law of stalk fields), `DegDet.degEqDetTate_of_degHomogPoly : DegHomogPoly → DegLadicIsogeny →
  HomFreeFiniteAlgClosed → CharPolyEll.DegEqDetTate`, `DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly`.
  New Props: `DegHomogPoly` (LEAF, printed form, Mumford §19 deg homogeneous polynomial of degree 2g, locator UNVERIFIED),
  `DegLadicIsogeny` (GLUE, |det V_ℓ ψ|_ℓ = |deg ψ|_ℓ for isogenies).
