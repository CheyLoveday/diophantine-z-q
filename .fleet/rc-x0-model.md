# Rational model of X₀(N)

Scoped stop: the smooth proper rational model with the prescribed function
field, its formal q-cusp, and the valuative chart on the upper half-plane
are proved. Every regular section evaluates on this chart by a single
meromorphic continuation, holomorphic wherever the section is regular.
The Laurent expansions of `j(τ)` and `j(Nτ)` are proved.

Two inputs remain for `X0Model N`: the normalized-branch comparison that
identifies chart fibres with Γ₀(N)-orbits, including collisions of plane
coordinates (tex 2915–2919), and convergence with the prescribed Laurent
coefficients for arbitrary rational expressions near the q-cusp (the
section comparison for tex 2837–2838 and 2915–2919).

Citation discrepancy: the pinned manuscript does not cite Shimura 1971
directly. Its citation at 770–771 and 11053–11057 points to the 1973
paper for a different step. The other branch reports a possible typo in
that paper's p. 526 sentence on conjugates (secondary reading UNVERIFIED;
unused here). No new print was introduced.

The six modules under `ZInQKernel/Contrib/OneProof/RC/X0Model/` and the
unchanged `ZInQKernel/Contrib/OneProof/ShimuraPointDictGerms.lean` compile.
See `docs/research/rc-x0-model.md` and `scratch/rc-x0-model/log.md`.
All axiom checks passed with only `propext`, `Classical.choice`, and
`Quot.sound`.

Final implementation and report SHA: `b82a6e2249f6e81ffce9176c04b4c59cb78c9adb`.
The branch tip is the following handoff-only commit. Its SHA is given by
`git log -1 --format=%H -- .fleet/rc-x0-model.md`; the file cannot contain
the hash of the commit that contains it.
