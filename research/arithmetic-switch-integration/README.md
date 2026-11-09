# Arithmetic switch: three source-interface advances

The boundary–cup correction, orthogonal comparison and determinant-coordinate
bridge now have explicit proofs and separate-agent reviews under their stated
source premises. Two new Lean modules check the cochain and homotopy deductions.
The actual retained arithmetic constructions and universal descent remain
separate obligations. This is a local research packet; it does not amend V13
or the frozen 39-target packet.

Start with the [combined proof sketch and lemmas](DERIVATION.md), then read
the [specification](SPEC.md) and [verification record](VERIFICATION.md).

| Interface | Concrete result | Proof and review |
| --- | --- | --- |
| Actual boundary–cup evaluation | The local-condition representative differs from global localization by a specified cup coboundary; the shared compact-support trace kills it. | [Proof](../actual-boundary-cup/DERIVATION.md), [nonauthor review](../orthogonal-comparison/BOUNDARY_REVIEW.md) |
| Orthogonal partner localization | The actual cone comparison fixes the global component; its homotopy inverse preserves global and derivative local cohomology. Actual strict H² supplies the rank-two matrices and pulled-back functional rows. | [Proof](../orthogonal-comparison/DERIVATION.md), [nonauthor review](../orthogonal-comparison/REVIEW.md) |
| Integral determinant coordinate | Both actual coordinates are the corresponding matrix coordinates multiplied by the SAME possibly nonunit strict factor (c^{-1}), with explicit unit changes of retained bases. | [Proof](../strict-determinant-bridge/DERIVATION.md), [nonauthor integration review](../actual-boundary-cup/DETERMINANT_INTEGRATION_REVIEW.md) |

The source-relative calculation gives (q_S=-q_F). In compatible cofactor
frames this yields (u_S=\det(J)u_F); arbitrary retained integral determinant
bases introduce only integral units. This removes an independently chosen
finite/singular normalizing scalar from the stated construction. It does not
permit arbitrary rescaling of one functional.

The new formal sources are
[ActualBoundaryCup.lean](../../lean/Research/DerivativeSwitch/ActualBoundaryCup.lean)
and [OrthogonalComparison.lean](../../lean/Research/DerivativeSwitch/OrthogonalComparison.lean).
Their 14 selected proof roots compile with Lean 4.35 and pass a transitive
axiom audit. They do not formalize global Galois Selmer complexes, the global
compact-support trace or a determinant functor. The determinant bridge is an
ordinary mathematical proof using the actual triangles and integral bases.

Exact checks cover 256 nontrivial cochain corrections, 6,400 degreewise cone
cases, 4,680 homotopy congruence cases, 180 determinant models and 1,836
combined rational models. Their bad controls expose omitted closedness, bad
traces/signs, independent functional rescaling, discarded torsion and invalid
localization/descent inferences. These are finite diagnostics, not arithmetic
instances or universal proofs.

Reproduce the focused checks from the repository root:

```sh
python -B research/arithmetic-switch-integration/run_checks.py /tmp/zq-actual-checks
python -B research/arithmetic-switch-integration/verify_native.py /tmp/zq-actual-native
```

Use new output directories. The native command uses existing pinned Mathlib
import caches; it does not provision dependencies or run paranoid/external
checkers. Retained results are in [evidence](evidence/). Original local `.olean`
outputs remain at the paths recorded by the commands; their hashes are retained.

The remaining application work is to establish or independently validate the
actual global cup/trace and comparison tuple through the inner limit, every
localization-specific inverse, the nonzero local trace used in rank inference,
and integral universal group-ring descent. A scalar field comparison alone
does not establish universal descent. The restricted converse and full
Diophantine theorem are not certified here. Reviews are internal model reviews.

All existing tracked source bytes were checked against `fb29fe2`: 3,083 files
preserved, including all 216 frozen packet/source files. New work is local and
uncommitted; no push or PR update was made for this packet.
