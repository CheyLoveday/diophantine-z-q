# deg-det (2026-11-16, base wip/charpoly-ell 0d75311f + origin/main 0caafe66)

**Verdict.** charpoly-ell's leaf `DegEqDetTate` (Mumford §19 Thm 4, deg ψ = det T_ℓ ψ) is **proved in Lean** from ONE new
printed leaf and two open fields of the same bundle, no glue:
`ZInQ.Contrib.OneProof.DegDet.degEqDetTate_of_degHomogPoly_mumford (hP : DegHomogPoly)
(hM : AvSplit.MumfordTorsionAlgClosed) (hH : HomFreeFiniteAlgClosed) : CharPolyEll.DegEqDetTate`, and
`charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford` discharges the field `charPolyIndepOfEllAlgClosed`.
`DegHomogPoly` = "deg is a homogeneous polynomial function of degree 2g on End(A)" (Mumford §19, printed form,
locator UNVERIFIED). Target "−1, no new leaf" NOT met: count 34/11 → 34/11 (net 0, same as charpoly-ell's fold), because
polynomiality (theorem of the cube + Riemann–Roch) is a genuine input no open field supplies (l-adic data alone cannot
give l-independence). Recommended: fold this spec instead of charpoly-ell's (same count, leaf = Thm 4's one deep input).

**Compiles** (standard axioms; `lake build ZInQKernel.Contrib.OneProof.DegEqDetTate`; #discharges; autofold dry-run
module compiles): `ZInQKernel/Contrib/OneProof/DegEqDetTate.lean` + `DegEqDetTate/Algebra.lean` (Mathlib-only algebra of
Mumford's proof: Nullstellensatz extension, det F(M) = ∏F(roots), l-adic comparison lemma), `TateIndex.lean`
(|det T_ℓ φ|_ℓ = |#ker φ|_ℓ for any φ with finite kernel, Smith normal form over ℤ_ℓ), `KerDvd.lean` (#ker ψ(k̄) | deg ψ:
translations act faithfully on K(A) over ψ*K(A), Artin), `Reduction.lean` (deg multiplicative; superseded routes via
DegLadicIsogeny / SepDegKernel). Spec: scratch/deg-det/autofold.json.

**Remains.** `DegHomogPoly` (crowdsourcing target: cube, χ(f*L) = deg f·χ(L), Riemann–Roch on abelian varieties);
locator to be read. If homfree-proof's fold lands first, take homFreeFiniteAlgClosed from its theorem in the proof
expression. Report: docs/research/deg-det.md.

Scratch checks (scratch/deg-det/Algebra.lean, TateIndex.lean, KerDvd.lean, CheckAxioms.lean, Discharges.lean, FoldDryRun.lean)
all compile; log in scratch/deg-det/log.md.
