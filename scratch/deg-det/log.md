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

- VERIFIED compiled: `DegDet.eq_Rs_of_mul` (multiplicative φ with φ(c)=c^n, φ(X-r)=(-1)^n P(r) is F ↦ ∏_{P(a)=0} F(a)),
  `DegDet.det_aeval_eq_Rs` (det F(M) = ∏_{χ_M(a)=0} F(a)), `DegDet.mult_eq_of_norm_Rs` and
  `DegDet.eq_of_norm_RsZ` (comparison lemma: monic P, Q over ℚ_ℓ with |∏_{P(a)=0}F(a)| = |∏_{Q(b)=0}F(b)| in
  PadicAlgCl ℓ for every F ∈ ℤ[X] with nonzero left side are equal).
- VERIFIED compiled (817 lines, axioms [propext, Classical.choice, Quot.sound]):
  `DegDet.Nt_mul` (generic multiplicativity: a polynomial function N on ℤ[X]/(R), multiplicative on pairs with nonzero
  values and N(1)=1, is multiplicative on S[X]/(R) for every ℚ-algebra S; Combinatorial Nullstellensatz on ℕ-points),
  `DegDet.P0_monic` (N(t − X) is monic of degree n for N homogeneous of degree n),
  `DegDet.det_eq_deg_abstract`: E ring, φ ∈ E with R(φ)=0 (R ∈ ℤ[X] monic), deg : E → ℕ homogeneous polynomial of
  degree n on ℤ[φ] (coordinates Σ x_i φ^i, i < deg R), deg 1 = 1, deg multiplicative on pairs with nonzero degree,
  ρ : E →+* M_I(ℚ_ℓ) with |det ρ ψ|_ℓ = |deg ψ|_ℓ when deg ψ ≠ 0  ⇒  det ρ(φ) = deg φ.
- VERIFIED compiled (`lake build ZInQKernel.Contrib.OneProof.DegEqDetTate`, axioms standard; scratch/deg-det/CheckAxioms.lean):
  ZInQKernel/Contrib/OneProof/DegEqDetTate/Algebra.lean (copy of scratch Algebra.lean, namespace ZInQ.Contrib.OneProof.DegDet) and
  ZInQKernel/Contrib/OneProof/DegEqDetTate.lean:
  `DegDet.degEnd_mul_of_isIsogeny` (deg(ψχ) = deg ψ deg χ for isogenies; generic point preserved by surjective maps,
  tower law of stalk fields), `DegDet.degEqDetTate_of_degHomogPoly : DegHomogPoly → DegLadicIsogeny →
  HomFreeFiniteAlgClosed → CharPolyEll.DegEqDetTate`, `DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly`.
  New Props: `DegHomogPoly` (LEAF, printed form, Mumford §19 deg homogeneous polynomial of degree 2g, locator UNVERIFIED),
  `DegLadicIsogeny` (GLUE, |det V_ℓ ψ|_ℓ = |deg ψ|_ℓ for isogenies).
- VERIFIED: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.DegEqDetTate` OK
  (13701 jobs, all but the new modules replayed; frozenTarget standard axioms). `#discharges` (scratch/deg-det/Discharges.lean,
  output Discharges-output.txt): DISCHARGES [OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed] by
  DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly, still assumes [DegHomogPoly, DegLadicIsogeny, HomFreeFiniteAlgClosed],
  axioms standard.
- VERIFIED: autofold dry run (scratch/deg-det/autofold.json): `strict count: 34/11 on 45 -> 34/12 on 46; strictest 34/11 -> 34/12`
  (refused without --allow-rise). With --allow-rise --dry-run the module (scratch/deg-det/FoldDryRun.lean, line 1 stripped) compiles:
  'HDec.HSyn.sixContactMin_of_open36' standard axioms.
- VERIFIED compiled (scratch/deg-det/TateIndex.lean, copied to ZInQKernel/Contrib/OneProof/DegEqDetTate/TateIndex.lean):
  `TateIndex.norm_det_eq_inv_card` (|det F|_ℓ = [T : F T]⁻¹ for injective F on a free finite ℤ_ℓ-module; Smith normal form),
  `TateIndex.card_quot_range_pow`, `TateIndex.exists_tate_lift_n`, `TateIndex.exists_eq_pow_smul`,
  `TateIndex.map_injective_of_finite_ker`, `TateIndex.norm_det_map_eq`: for M with #M[ℓ^n] = ℓ^(nr) and φ : M →+ M with
  FINITE KERNEL (surjectivity NOT needed — found while proving), ‖det T_ℓ φ‖ = ‖#ker φ‖ in ℤ_ℓ.
- VERIFIED compiled (lake build ZInQKernel.Contrib.OneProof.DegEqDetTate; CheckAxioms standard axioms):
  new LEAF `SepDegKernel` (Mumford §4/§7: for an isogeny ψ, ker ψ(k̄) finite and deg ψ = #ker ψ(k̄) · (ringExpChar k)^e),
  `degLadicIsogeny_of_sepDegKernel : SepDegKernel → MumfordTorsionAlgClosed → DegLadicIsogeny`,
  `degEqDetTate_of_printed`, `charPolyIndepOfEllAlgClosed_of_printed : DegHomogPoly → SepDegKernel →
  MumfordTorsionAlgClosed → HomFreeFiniteAlgClosed → CharPolyIndepOfEllAlgClosed` (no glue left).
- VERIFIED: autofold spec updated to the printed route (scratch/deg-det/autofold.json):
  `strict count: 34/11 on 45 -> 35/11 on 46; strictest 34/11 -> 35/11` (no GLUE rise, accepted without --allow-rise);
  dry-run module scratch/deg-det/FoldDryRun.lean compiles ('HDec.HSyn.sixContactMin_of_open36' standard axioms).
  #discharges (Discharges-output.txt): DISCHARGES [OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed] by
  DegDet.charPolyIndepOfEllAlgClosed_of_printed, still assumes [DegHomogPoly, SepDegKernel, AvSplit.MumfordTorsionAlgClosed,
  HomFreeFiniteAlgClosed], axioms standard. (Also the earlier charPolyIndepOfEllAlgClosed_of_degHomogPoly line.)
- VERIFIED compiled (scratch/deg-det/KerDvd.lean → ZInQKernel/Contrib/OneProof/DegEqDetTate/KerDvd.lean):
  `KerDvd.kerDvdDeg : degEnd ψ ≠ 0 → Finite (ptMap ψ).ker ∧ Nat.card (ptMap ψ).ker ∣ degEnd ψ` (translations τ_P by
  kernel points over k̄ ≅ k, their action σ on the function field characterized by Spec(σ f) ≫ ι = ι ≫ f, fixing ψ^*K(A),
  faithful by ext_of_isDominant_of_isSeparated; Artin IntermediateField.finrank_fixedField_eq_card + tower law).
  This REPLACES the leaf SepDegKernel.
- VERIFIED compiled: Algebra.lean one-sided `eq_of_norm_RsZ_le` (monic P,Q, deg P = deg Q, |RsP F| ≤ |RsQ F| ⇒ P = Q) and
  `det_eq_deg_abstract_le`.
- VERIFIED compiled (lake build ZInQKernel.Contrib.OneProof.DegEqDetTate; files restructured: DegEqDetTate/Reduction.lean = old
  top file, DegEqDetTate/KerDvd.lean, new top DegEqDetTate.lean): `DegDet.degEqDetTate_of_degHomogPoly_mumford :
  DegHomogPoly → MumfordTorsionAlgClosed → HomFreeFiniteAlgClosed → DegEqDetTate` and
  `DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford` (same hypotheses → CharPolyIndepOfEllAlgClosed),
  helper lemmas card_tb_of_mumford, norm_det_V_eq_card_ker, card_basis_V (rank V_ℓ = 2g), norm_deg_le_norm_det.
  Axioms standard (scratch/deg-det/CheckAxioms.lean). ONE new leaf (DegHomogPoly), no glue.
- VERIFIED: autofold spec now discharges via charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford with ONE leaf degHomogPoly:
  dry run `strict count: 34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11`; FoldDryRun.lean compiles
  (sixContactMin_of_open36 standard axioms). `lake build +Main +Discharges +DegEqDetTate` OK (13704 jobs). #discharges:
  DISCHARGES [OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed] by DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford,
  still assumes [DegHomogPoly, AvSplit.MumfordTorsionAlgClosed, HomFreeFiniteAlgClosed], axioms standard.
