# rc-stage-ident checks

| Check | Result |
| --- | --- |
| Initial merge | Merged stage-map commit into the stage-val base; no conflict. |
| Detector | Fixed row on finite torsion, same residue Kummer map as `actualEvaluations`, transported to skeleton precision. |
| Full filter | `sourceFilter_eq` matches the actual Fourier exclusions and moving Legendre test with the intrinsic label predicate; `rodd_atStage` matches the valuation. |
| Coverage | `pmLocal_base_support`, `bad_mem_support`, `support_dvd_type`. The support equality uses fixed coefficient primes and the selected moving prime. |
| Budget | `reading_budget`: operator cutoff `B - 1`, truncation `2`. |
| `Detector.lean` | `lake env lean -j1` passed; 8 audits, only `propext`, `Classical.choice`, `Quot.sound`. |
| `Filter.lean` | `lake env lean -j1` passed; 10 audits, only `propext`, `Classical.choice`, `Quot.sound`. |
