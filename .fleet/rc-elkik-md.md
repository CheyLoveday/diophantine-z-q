# Manin–Drinfeld and the genus partner’s central value

Final implementation, report, and results log SHA: `13950c1967c6a396f01775f704f47e6dd99785ff`.
This handoff is the last commit; its SHA is given by `git log -1 --format=%H -- .fleet/rc-elkik-md.md`.

Elkik’s finiteness statement does not by itself cover `hElkikMD`. Lean proves the common
cusp denominator, the twisted Birch identity (including the quadratic Fourier calculation
up to sign), and the rational coordinate in the exact `omegaMinus Lat` convention.
`GenusPartner` supplies the nonzero central value. The final conditional theorem uses the
same form and lattice as the base assembly and gives its nonzero rational witness.

The remaining geometric statement is that the image of `[c(a/|hstar|)] − [∞]` under the
fixed `α q_f` followed by uniformization is the class of the associated modular symbol
times a common nonzero rational scalar. It is needed only for the cusps with nonzero
quadratic weight. The actual Jacobian and cusp classes still need to be realized in Lean;
the assembly keeps its `hElkikMD` hypothesis. The Elkik locator, Astérisque 183, p. 59,
Theorem, remains UNVERIFIED against the page (GLUE, unread). No other print was added.

All five new files passed `lake env lean` sequentially. All 20 theorem audits list only
`propext`, `Classical.choice`, and `Quot.sound`. See `docs/research/rc-elkik-md.md` for the
exact remaining proposition, provenance, and manuscript checks.
