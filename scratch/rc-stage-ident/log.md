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
| Selected parameters | `level_eq`, `detectorAt_lam`, `pmStage_parameters`, `pmStage_weight`. Detector identity uses `actualForStages`; extraction and support refer directly to the local fields. |
| Consumer | `inputs_of_selected`: selected parameter and filter identities together with `X.Inputs` via `inputs_of_pm`. |
| `Apply.lean` | `lake env lean -j1` passed; 5 audits, only `propext`, `Classical.choice`, `Quot.sound`. |
| Resource checks | Before each Lean invocation: `uptime` and `free -g`; load at most 120 and available memory at least 20 GB. One Lean job at a time. |
| Remaining | Selected valid stage, `PMLocal`, adelic and supersingular geometry, (O.7), exact sieve, App G depth, and (O.12) model inputs. |
