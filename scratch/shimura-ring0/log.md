# Results

- Base: `46e2f501ef4da5def7d6eecee151170828b060e8`.
- Inherited counterexample: `ξ 0 := 1` gives `(1, 0)` in the old ring, so `PrintQuotient` forces `ν = 0`; error verdict committed before the repair.
- `printRing`: closure of `(ξ (n + 1), ak f (n + 1))`; `print_annihilator_eq` reinserts only the zero pair under `HeckeRelations.zero`.
- `printRing_update_zero`: arbitrary update at index zero leaves the ring unchanged.
- `printRing_eq_closure_of_zero`: normalization at zero gives equality with the all-index closure.
- `kills_print_of_printedClauses`: clause (ii) implies that `ν` kills the saturated annihilator, by subring closure and positive integer cancellation.
- Scope check: `XiAction` pins every positive operator uniquely. Saturation preserves the scheme theoretic image family. No further unchecked generator found.
- `ShimuraThm1Printed`: coefficient field finiteness, a triple satisfying (i)–(iii), and uniqueness up to an isomorphism over ℚ.
- `ShimuraQuotientByC`: every printed triple satisfies `PrintQuotient`; p. 526, GLUE, provenance (c); assumed as an argument.
- `asPrinted_of_split` and `printed_of_asPrinted`: combine the split inputs and forget the quotient conjunct, respectively.
- `shimuraThm1Af_of_split`: the two split inputs, `ShimuraHeckeRelations`, and `SameDimSurjectiveFinite` give `R16Thm1b.ShimuraThm1Af`.
- `shimuraThm1Af_of_split_closed`: the two split inputs alone give the same row.
- Source comparison against the base: exact conjunct deletion; construction binders unchanged through `XiAction`; fixed propositions unchanged; only docstrings changed in `SameDimFinite.lean` and `ShimuraOrbits.lean`.
- Draft build: redundant `funext` after `congr 2` in `printRing_update_zero` produced `No goals to be solved`; removed the redundant tactics.
- PASS: serial offline Lake build (12,977 jobs) for `ShimuraSteps`, `ShimuraHeckeJ`, `ShimuraPointDict`, `SameDimFinite`, `ShimuraOrbits`, `ShimuraHeckeClosed`, `ShimuraRing0`, `BShFamily`, and `OneProof.Discharges`.
- PASS: `Axioms-output.txt`, all seven new theorems plus `shimuraThm1Af_of_printed` and `BShFamily.bShStandardModel_proof`: only `propext`, `Classical.choice`, `Quot.sound`.
- PASS: `Discharges-output.txt`, the only assumptions of `shimuraThm1Af_of_split_closed` are `ShimuraThm1Printed` and `ShimuraQuotientByC`.
