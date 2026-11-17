# degpoly-proof (2026-11-16, base wip/deg-det ecf7da39 + origin/main + origin/wip/homfree-proof)

**Verdict.** deg-det's leaf `DegHomogPoly` is **proved over every algebraically closed field with a ring hom to ℂ**
(`DegPolyC.degHomogPolyC`, from the open fields `uniformizationLeafAll` + `mumfordTorsionAlgClosed` and deg-det's KerDvd):
`deg ψ = det_ℤ(M_ψ on the period lattice Λ)` for every ψ ∈ End(A) (kernel points over any field ↔ fibre ψ⁻¹(e₀);
deg ψ ≤ #fibre via the embeddings of K(A) in char 0; #ker ψ(ℂ) = [Λ : M_ψΛ] = det > 0; det ≠ 0 ⇒ isogeny by
Cayley–Hamilton), hence Mumford §19 Thm 4 over these fields too (`degEqDetTateC`). The field
`charPolyIndepOfEllAlgClosed` has an even shorter proof there (charpoly V_ℓ(φ) = charpoly_ℤ(φ|Λ), `CharPolyLattice`).
**"−1, no new leaf" is out of reach (finding):** T7 is applied in CHARACTERISTIC p (`common_trace` at FrobTraceLink's
reduction mod p), so no narrowing to ℂ-embeddable fields can remove the field. Result: two count-neutral discharges
(34/11 → 34/11), each replacing the field by a strictly weaker published leaf (∀-specialization to fields with no
embedding into ℂ): `CharPolyIndepOfEllAlgClosedNoEmb` (recommended, scratch/degpoly-proof/autofold.json) or
`DegHomogPolyNoEmb` (autofold-degpoly.json; also needs homFreeFiniteAlgClosed).

**Compiles** (standard axioms; #discharges shows both discharges; both autofold dry-run modules compile):
`ZInQKernel/Contrib/OneProof/CharPolyLattice.lean` (main-only imports) and `ZInQKernel/Contrib/OneProof/DegHomogPolyC.lean`
(imports deg-det's DegEqDetTate). Scratch: KerFibre/LatticeDet/LatticeRing/CharPolyC, CheckAxioms, Discharges, Closure.

**Remains.** The characteristic-p case (Mumford §19 Thm 4 / polynomiality of deg in char p: cube + Riemann–Roch).
autofold-after-degdet.json (discharging deg-det's future field degHomogPoly) is unchecked. Report: docs/research/degpoly-proof.md.
