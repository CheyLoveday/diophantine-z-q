# genus-route (fleet summary)

**Verdict: `t34`'s two uses are closed with no literature leaf (VERIFIED, compiled, standard axioms).**
Both consumers (TailD.lean:236 `dim_J1_le t.t34`, :250 `javanpeykarJ1 … t.t34`) need only
`DimJ1Le : dim J₁(N) ≤ N²`. That bound is a Lean theorem with no hypothesis: `GenusRoute.dimJ1Le`
(`scratch/genus-route/Closed.lean`), `HDec.HSyn.t34Le : DimJ1Le5` on the OneProof copies (`Fold.lean`). So
`GenusX1Field` (no Lean form) is unnecessary, and `X0Transitive` is not used on this route.

Ingredients:
- dimjac-glue's `DimJacobianEqGenus` (copied verbatim from `wip/dimjac-glue` 24435c82, compiled here);
- new `constantFieldIsQ_of_curve`: ℚ is algebraically closed in K(X) for a smooth proper geometrically
  connected integral curve X/ℚ (normality + sheaf gluing + base change to ℚ̄); this replaced X0Transitive;
- new elementary genus bound `g(K_N) ≤ [K_N : ℚ(j)]` (`genusLeDegree`), with no Riemann–Roch or
  Riemann–Hurwitz: holomorphic differentials are `h·dj` with `h` in an explicit space that injects into
  `OF/j·OF ≅ ℚ^d`; its local input `LocalDerivation` (d/dπ preserves 𝒪_P) is proved too (`localDerivation`:
  bounded derivative + Zariski residue field + iteration; twist j ↦ 1/j at ∞);
- kernel `ZInQ.RLeaf.belyiX1` (`[K_N : ℚ(j)] ≤ N²`).

What compiles (`lake env lean scratch/genus-route/<f>.lean`, all `#print axioms` standard):
ConstField (constant field), GenusRoute (+ curve-split's RH route without X0Transitive), GenusElem
(+ genus bound from LocalDerivation), LocalDer (+ LocalDerivation proved), Closed (+ dimjac-glue ⇒
`dimJ1Le`), Fold (+ `import OneProof.H.TailM`: `t34Le`, `dim_J1_le_of5`, `G0Split.javanpeykarJ1_of_le`, and
TailD's `glueOutputs_of_leaves3` refolded as `glueOutputs_of_leaves3_t34Le`, compiled, no `t.t34`).
Fold needs `lake build ZInQKernel.Hypotheses.JHeight` once (upstream `lean/` package).

What remains: the fold itself (delete `genusX1Field`/`dimJacobianEqGenus` fields and `t34_of_split5`, use
`t34Le` at TailD:236/:250). Not checked: whether X0Transitive's separate T40 use can go too.
Report: docs/research/genus-route.md; log: scratch/genus-route/log.md.
