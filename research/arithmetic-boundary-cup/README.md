# Arithmetic boundary–cup bridge

The actual paired-functional construction gives opposite normalizers,
$c_F=-\kappa u$ and $c_S=\kappa u$, with one shared transport unit $u$.
They are related by the integral unit $-1$. The ordinary separate-triangle
argument then preserves the actual determinant-tensor valuation, relative
to V13's retained arithmetic and duality inputs.

The new Lean module proves the bridge **relative to an explicit retained-duality
interface**. It derives the normalized identities from the raw cup and actual
partner construction, then reuses the frozen integral-unit theorem. It does
not construct arithmetic Selmer complexes, Poitou–Tate duality or determinant
functors in Lean.

**Start here:**

| Reader | Route |
| --- | --- |
| Mathematical review | [Source application and insertion scope](APPLICATION.md); [reviewed ordinary derivation](DERIVATION.md) and its [prior review](REVIEW.md) |
| Manuscript integration | [LaTeX insertion source](manuscript-insertion.tex), the editable addendum authority; [generated insertion patch](proposed-v13.patch) |
| Formal review | [Lean bridge](../../lean/Research/DerivativeSwitch/ArithmeticBridge.lean), [specification](FORMAL_SPEC.md), [verification](VERIFICATION.md) |
| Contribution review | [Three focused read-only reviews](focused-reviews/README.md), [PR structure](PR.md) |

The insertion expands the determinant paragraph in
`ex:limits-derivative-switch`. It is incorporated as a versioned addendum
with a checked application patch; canonical V13 is unchanged. The earlier
`DERIVATION.md`, `REVIEW.md` and component investigations are frozen research
records, not independently editable publication copies.

Local Lean 4.35 compilation and transitive axiom auditing passed for nine new
declarations. The [native evidence](evidence/native/RESULT.json) binds the
sources, toolchain, dependencies and compiled artifacts. The 675-case finite
checker remains supplementary sign evidence, including double-J, omitted-tame
sign and nonunit-rescaling controls; it is not arithmetic verification.

The six-, 21- and 39-target packets remain frozen historical stages. Their
arithmetic-open statuses describe those exact packets. This later conditional
bridge is separate, and Open Math's current run does not cover it. The
[preservation receipt](evidence/preservation.json) confirms all 63/65/99 input
entries and the original generated 39-project manifest are unchanged.

Run the scoped local checks from the repository root:

```sh
python -B research/arithmetic-boundary-cup/verify_native.py lean/.checks/arithmetic-bridge-fresh
python -B research/arithmetic-boundary-cup/check_local_signs.py
python -B research/arithmetic-boundary-cup/prepare_insertion.py /tmp/arithmetic-insertion.patch
git apply --check /tmp/arithmetic-insertion.patch
```

The output directory for native verification must be new. These commands do
not run cloud/paranoid checking or apply the manuscript patch. Canonical
manuscript incorporation and formal realization of the actual arithmetic
objects remain pending.
