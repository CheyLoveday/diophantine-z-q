# Companion unit results

- Base: 2891c386b07f8540d57c24a17b893b364ee1f75c.
- Old source: negative sign, classes at 2N, initial exclusions from pre-companion support, torsion and hstar.
- App E requires a retained nonzero reference. hstar cannot serve once its primes are excluded. Existing BFH clause (ii) supplies a reference with a specified splitting set.
- AuxInputs is on a sibling ref; the assigned base has App E and KSplitOldUnit.
- Initial five direct imports built successfully via serial `lake build` from byte-identical cached dependencies and new local artifacts.
- Provider first elaboration: signed casts needed explicit integer coercions; bad-model support proof used an ambiguous apply order; discriminant lemma requires a field in `Type`. Corrections applied.
- Exact level bridge: existing newform divisibility theorem plus functional-equation level uniqueness.
- Selection inputs: base root number −1, existing App E inputs and (E.9), prime supports fixed before k, hstar. Reference from BFH clause (ii).
- `Selection.leaf_and_oldUnit`: `W.kfin = A.k`, `W.S = finalSupport ℓ Sold T hstar A.k`, same hstar and Lstar, hstar ≠ 0 → `CompanionLeaf W ∧ CompanionOldUnit A.old W.kfin`.
- `Selection.fresh_ramification`: degree-two K with square root of A.k → `discr K = A.k ∧ ∃ p ∈ ramifiedPrimes K, p ∉ Sold ∧ p ∉ T`.
- Sixth direct import `GenusOdd.LevelGood`: serial `lake build` passed.
- `Provider.lean`: `lake env lean -j1` passed with no diagnostics.
- `Axioms.lean`: ten declarations audited; each returned exactly `[propext, Classical.choice, Quot.sound]`.
