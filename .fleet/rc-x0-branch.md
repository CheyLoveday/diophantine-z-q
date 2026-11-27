# Normalized branch comparison at every level

`X0Branch.model (N : ℕ) [NeZero N] : PreparedParam.X0Model N` is
constructed. `exists_stabilizer_germ_match` proves that equal valuative
complex points above one j-fiber give equal punctured second-coordinate
germs after a reparametrization that fixes the center. The inherited
sheet classification then gives `complexPoint_eq_iff` for Γ₀(N).

The comparison uses an affine étale coordinate on the smooth normalized
curve. The inherited section theorem makes its pullback holomorphic on
both branches. The unramified diagonal distinguishes the regular section
evaluations, and local open mapping gives overlap at actual points on
the normalization. This works also at i and ρ without inferring equality
from a coincident plane value at the center. Provenance (c), tex 2836–2838
and 2915–2919.

All four files in `ZInQKernel/Contrib/OneProof/RC/X0Branch/` compile
serially. All 31 axiom checks report only `propext`, `Classical.choice`
and `Quot.sound`. No new print or assumed input. There is no remaining
input for `X0Model`; the fixed-scale parametrization, modular function
field comparison, and CM point descent are downstream.

Report: `docs/research/rc-x0-branch.md`. Results:
`scratch/rc-x0-branch/log.md`.

Final implementation and report SHA: `398868586602e0f9d0c4401269e5f9a388f3f4e9`.
The final handoff SHA is returned by
`git log -1 --format=%H -- .fleet/rc-x0-branch.md`; a commit cannot
contain its own SHA.
