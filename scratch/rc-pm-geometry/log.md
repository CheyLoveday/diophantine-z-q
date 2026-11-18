# rc-pm-geometry results

- Base: `b10b5bf71ddb0ab17f2dbd7c31b573b068402178`; merged `6e25b8c2efe22d4676d825c501b18734138deab8` with no conflicts.
- `Geometry`: formal divisor centering; based cusp zero; good Hecke line sum; affine Atkin–Lehner; equivariant point specialization; uniformizer comparison; constructed PM record.
- `Evaluation`: split twist row transport; reduced elliptic equation; prime-to-residue-characteristic torsion equivalence and arithmetic Frobenius compatibility; fixed finite row and square action; `ofTateRow` at the selected place and stage.
- `Heegner`: point comparison, lift congruence, and `lamOf` congruence for the selected datum, using actual ring class reduction.
- `Theta`: both existing stage constructors with the same geometry and detector.
- Known source scope: prior audit reports Jetchev–Kane assumes `N > 1`; no squarefree restriction.
- Compiled with `lake env lean --threads=1`: `Geometry.lean` (8 audits), `Evaluation.lean` (12), `Theta.lean` (2), `Heegner.lean` (5).
- Axioms for each audit: `propext`, `Classical.choice`, `Quot.sound`.
- Heegner ring class instance: explicit `Classical.decEq` matches the instance in the existing `StageKummer` interface.
- Resource incident: a queue transition briefly overlapped two Lean processes; old queue stopped, final checks run sequentially under a lock.
