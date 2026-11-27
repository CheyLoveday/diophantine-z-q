# Adelic and supersingular geometry join

`PMAdelic.geometry` builds `PM.Geometry` on the proved level order
from the named Jetchev–Kane comparison on double cosets and ELLIOT's
modular special-fibre statements. The join supplies all adelic fields,
moves the three operator comparisons to ideal classes, and proves that
every line indexing gives the same Hecke multiset with multiplicities.

Citation scope error (tex 8468–8474): audit A052 records Jetchev–Kane at
`N > 1`, prime to the detecting prime, with general prime powers allowed.
The citation does not supply the manuscript's level-one case.

For the Heegner comparison, the existing oriented torsor bijection does
not identify the reductions of the actual enhanced CM conjugates. The
remaining input is their reduction to the reference classes and
commutation with the specialized quotient at the same place (tex
9265–9291). The witness stage map is pinned only at its selected datum.
The evaluated entries still need the reduction and detector agreement
described in the report.

`Comparison.lean` and `Geometry.lean` both passed
`lake env lean --threads=1`. All 14 axiom checks list only
`propext`, `Classical.choice` and `Quot.sound`.
See [the report](../docs/research/pm-adelic-join.md) for statements,
tex lines and the scoped stop.

Final checked implementation and report:
`34cf11198db9cf21a1e4c2567e5f7efd58df6210`. The final branch commit
adds only this handoff; its SHA is given by
`git log -1 --format=%H -- .fleet/pm-adelic-join.md`.
