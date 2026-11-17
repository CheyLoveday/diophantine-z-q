# charpoly-p (2026-11-17, final; base main 0fcc7e36 + origin/wip/degpoly-proof 0a9e6698)

**Verdict.** `charPolyIndepOfEllAlgClosed` is not proved in characteristic p. Main result, compiled with standard
axioms and confirmed by #discharges:
`ZInQ.Contrib.OneProof.CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb' (HR : DegPolyC.DegHomogPolyNoEmb)`.
- The field follows from the polynomiality of deg alone. Mumford §19 Thm 3 (End(A) finite over ℤ) is not needed:
  bounded-degree polynomials in φ replace ℤ[X]/(R), and P₀ ∈ ℤ[X] comes from deg(φ^m − q) ∈ ℤ for all m (q-adic
  growth of a non-integral root).
- Fields that embed into ℂ use degpoly-proof (`uniformizationLeafAll_proof`, `mumfordTorsionAlgClosed_proof`).
- Autofold spec `scratch/charpoly-p/autofold.json`: field out, leaf `degHomogPolyNoEmb` in (published, flag
  unread). Count-neutral (15/16 → 15/16); the dry-run module compiles. The leaf is the lead's first milestone, and
  step 2 (finiteness) is gone.

**Survey.**
- In the tree: the vendored AnthropicFLT (CloudB3W16Torsion) proves the theorem of the cube, one-variable Snapper
  χ(M⊗L^n), the leading coefficient of χ(f^*L^m) = deg f·χ(L^m), deg[n] = n^{2g} and a symmetric L with c_g > 0.
  CW07 adds coherent cohomology.
- Missing: M1, χ(ψ^*L) = 0 for a non-isogeny ψ (a consequence of Mumford §16 RR). Also missing is large glue:
  degEnd ↔ endDegree, CW07 χ ↔ Čech χ, the cube ⇒ quadratic in Pic, and joint polynomiality.

**Also compiled.**
- `CharPolyCharP/ChiDecomp.lean`: DegPolyAt A from four χ-statements over genuine tree defs (`EulerPullbackDegAt`,
  `ChiPullbackPolyAt`, `ExistsChiNeZeroAt`, `DegMulNDimAt`), and `charPolyIndepOfEllAlgClosed_of_chi`. This is a
  crowdsourcing map, not a fold.
- `scratch/charpoly-p/M1Statement.lean`.

**Files.**
- `ZInQKernel/Contrib/OneProof/CharPolyCharP.lean`, `CharPolyCharP/{Algebra,ChiDecomp}.lean`. The fold also needs
  the charpoly-ell, deg-det and degpoly-proof files, carried here unchanged by the merge.
- Report: docs/research/charpoly-p.md. Log: scratch/charpoly-p/log.md.

**Remains.**
- M1, or Mumford §16 RR, for the char-p polynomiality.
- Bridges G1–G6 (report §3).
- Integrator: fold autofold.json on main, bringing the merged dependency files along.
