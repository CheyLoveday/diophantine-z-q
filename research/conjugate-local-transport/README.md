# Local conjugation from the actual twisted representation

The common local transport factor is now derived from the coefficient twist
and H12, rather than supplied as a normalization assumption. The new theorem
works over a commutative ring and descends to Mathlib's actual first group
cohomology, with original and conjugate coefficient systems kept distinct.

For the actual transporter $d=\varphi\tau^{-1}$, the same integral unit
$u=\alpha(d)^{-1}$ works for both classes:

$$
\operatorname{loc}(c_\tau z)=(u f(z),-u s(z)).
$$

The source application also supplies the common tame quotient and explains
how retaining the unit **and its inverse** in the manuscript's fixed inner
diagram preserves an integral unit. This limit argument uses the source's
actual contractions and bounded finite models; it is not formalized in Lean.
The full arithmetic determinant compatibility remains open.

**Start here:**

| Reader | Route |
| --- | --- |
| Mathematical review | [Derivation](DERIVATION.md), [source application and remaining obligations](APPLICATION.md) |
| Formal review | [Ring theorem](../../lean/Research/DerivativeSwitch/ConjugateLocalTransport.lean), [actual H¹ maps](../../lean/Research/DerivativeSwitch/ConjugateLocalH1.lean), [specification](SPEC.md) |
| Assurance review | [Non-author review](REVIEW.md), [native result](evidence/native/RESULT.json), [source bindings](evidence/source-bindings.json), [preservation receipt](evidence/preservation.json) |
| Prior work | [Separate arithmetic bridge](../arithmetic-boundary-cup/README.md), [frozen scalar-ratio packet](../scalar-ratio/README.md) |

This is a separate follow-up on `codex/derivative-switch-boundary-v13`.
The foundation's frozen 39-target packet and its Open Math receipts are
unchanged. The six-checker result for that packet does **not** cover the new
modules. The new files passed local Lean 4.35 compilation with kernel checking
enabled and a transitive axiom audit; the only allowed axioms are `propext`,
`Quot.sound`, and `Classical.choice`. This is development verification, without
paranoid mode or independent external kernel replay.

The remaining arithmetic work is to instantiate the global boundary–cup
adjunction and orthogonal inverse on the actual retained objects, identify
the common-strict matrices and stored functional rows, and verify the
determinant comparisons and localization occurrence. The new result reduces
that work by removing one normalization input; it does not supply the others.

Reproduce the new-module check from the repository root, using a fresh output
directory and the unchanged pinned Lean project:

```sh
python -B research/conjugate-local-transport/verify_native.py lean/.checks/conjugate-local-fresh
```

If the pinned Mathlib import closure is absent, use its cache client from
`lean/`:

```sh
MATHLIB_CACHE_DIR="$PWD/.lake/mathlib-cache" lake exe cache get --cache-from=master Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
```

This uses official master-cache artifacts for the pinned dependency revision;
it does not rebuild all imported proofs. The source application, review and
manifest record that trust boundary. Canonical V13 and the earlier manuscript
addendum are unchanged. This packet is a research record, not a new edition or
an assertion of mathematical acceptance of the main theorem.
