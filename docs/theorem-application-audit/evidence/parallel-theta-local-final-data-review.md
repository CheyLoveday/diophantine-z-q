# Final staged dependency-data review

Accepted for the requested dependency-preservation scope. No corrective data edit is required.

I inspected `parallel-009/finalize_staging_data.py`, `staging/rebind-final.json` and `staging/dependency-clarifications.json`. The old `rebind-reviewed-result.json` was not used. The reviewed final TeX SHA256 is `f880d559e9a76281573e4d5110852f347bc422af3f2daf0b483fbb7f01c62fb3`; it matches the staged TeX bytes. This hash comparison establishes version identity, not mathematical correctness.

## Retained data

- All 82 application IDs are present exactly once. Each carries the explicit review-scope limitation that acceptance does not certify every upstream lemma or the main theorem.
- A075's `dependency_phases` equals the complete proposed phase list, not an abbreviated list of IDs. It retains construction F, transport T, duality D and budget B; direct sources; internal premises and their locations; excluded dependencies; and the output boundary of each phase. The phase graph is ordered and acyclic: F precedes T, D consumes F/T, and B consumes F/T/D. In particular F does not depend on A038 or A045, while B does.
- All 12 proposed per-application clarifications occur unchanged in the corresponding final app's `dependency_clarifications`. This includes A037's construction-only dependence, A038's repaired local input, A040's finite-Sha restriction, A041's norm/lift/unit-factor premises, A044's separate arithmetic hypotheses, A045's distinction between A082 and the real-place argument, A080's independence from global exact-annihilator claims, and A081's local versus global Kato distinction.
- A075-T retains the amended elementary-ultrafilter subclaim rather than acquiring a blanket dependency on A076's arithmetic realizability. Its conditional application boundary is preserved.
- The other per-ID refinements for A011/A064, A013 and A027 remain intact. All five coverage-addition records also occur under their target IDs.
- The standalone `dependency-clarifications.json` is structurally identical to the reviewed proposal. It preserves all four supersession notes, the complete coverage list, the statement that this pass demonstrated no new failed internal premise, and the qualification that internal arithmetic premises are not proved merely by application acceptance.

The script correctly reads these notes as an overlay. Phase data is attached explicitly to A075. Lists with target IDs are attached to those applications. Lists without target IDs, especially supersession notes, are preserved in the standalone companion rather than silently discarded.

## Publication boundary

Retain the companion file in the published audit and link it from the dependency documentation. Supersession notes are not individually attached to every affected application by this script; they reside in that companion. Likewise, any human-readable inventory generator must retain or link `dependency_phases` and `dependency_clarifications`. A rendering that shows only the accepted status and empty open-items field would omit the qualifications that make these decisions honest.

The premise locators inside these notes intentionally use baseline line numbers and say so. They should remain labelled as historical baseline locators; the rebinding script must not silently present them as final TeX line numbers. The applications' actual manuscript anchors are separately rebound.

No broad `upstream_dependencies` or `retained_internal_premises` field in the nine critical records contradicts the refined overlay. Their internal prerequisites remain stated in the explicit clarification objects, review text and linked evidence. The data does not claim that A075 and the duality applications mutually discharge whole records.

This review confirms preservation and consistency of the dependency overlay. It is not a second verification of every source file, the citation-role mapping, or the manuscript's full proof.
