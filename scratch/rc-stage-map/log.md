# Stage map results

- Base: `40d619ca811e6d8e760c49ac7e273cf5be8b2272`.
- Support: `stageTest q θ D` and `(hstar/p) = -1` imply `(discr K/p) = -1` for every datum of `D`. The existing conductor-one reduction gives residue cardinality `p²`.
- `actualEvaluations`: at every supported entry, restriction of the chosen absolute place, then the same `reducedRead`. Equal to the existing stage map at the chosen witness entry.
- `actualEvaluationsOn_spec`, `witnessValuation_actualForStages`: witness specialization and (O.2) on the total evaluation.
- `lamOf_admissible`: integer lift on the selected scaled genus point. No simple-zero premise; `selG D = some t` required. Base only guarantees selection at prepared simple zeros.
- Cache: the worktree lacked the stage artifacts; reused the witness overlay and the cached project libraries. Built missing imports serially with `lake env lean -j1`.
- Final `lake env lean -j1`, serial: `Actual.lean` passed (8 theorem audits); `Consumers.lean` passed (4 theorem audits). No warnings. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No source changes outside `RC/StageMap/`. No new printed-form leaf.
