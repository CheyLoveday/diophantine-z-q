# charpoly-p (2026-11-17, interim; base main 0fcc7e36 + origin/wip/degpoly-proof 0a9e6698)

**Verdict.** `charPolyIndepOfEllAlgClosed` is not proved in characteristic p. New Lean (standard axioms):
`ZInQ.Contrib.OneProof.CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb' (HR : DegPolyC.DegHomogPolyNoEmb)`
discharges the field from the polynomiality of deg alone. The finiteness of End(A) (Mumford §19 Thm 3) is not
needed: bounded-degree polynomials in φ replace ℤ[X]/(R), and P₀ ∈ ℤ[X] comes from deg(φ^m − q) ∈ ℤ (q-adic
growth). The swap is count-neutral (15/16 → 15/16), and the leaf is exactly the lead's first milestone.

**Survey.** The vendored AnthropicFLT (CloudB3W16Torsion) proves the theorem of the cube, a Snapper-type χ(M⊗L^n)
polynomiality, the leading coefficient of χ(f^*L^m) = deg f·χ(L^m), deg[n] = n^{2g}, and a symmetric L with c_g > 0.
CW07 adds coherent cohomology. Missing: M1, χ(ψ^*L) = 0 for non-isogenies ψ (from Mumford §16 RR), plus large glue
(degEnd ↔ endDegree, cube ⇒ quadratic in Pic, joint polynomiality, framework transport).

**Compiles.** `ZInQKernel/Contrib/OneProof/CharPolyCharP.lean` and `CharPolyCharP/Algebra.lean`; #discharges
recorded; autofold dry run compiles; `scratch/charpoly-p/M1Statement.lean`. Report: docs/research/charpoly-p.md.
