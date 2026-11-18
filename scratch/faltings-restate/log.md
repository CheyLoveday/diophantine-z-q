# Results log

- **VERIFIED (source):** The base is `be73b91c5`; `TailZ87` carries the height field as a GLUE consequence. The published invariance applies to a semiabelian scheme and its base change (Faltings 1983 §3 p. 354 and p. 351 Bem. b), pages read by the reading desk).
- **VERIFIED (Lean):** `IsSemiabelianModel` checks connected special fibres and `HasSemiAbelianIdCompTorus` on `resFibre`; the generic fibre is already abelian. `faltingsHeightBaseChange` follows from H4a alone, which is stated for every group model.
- **VERIFIED (Lean):** `SemistableNeronIdentification` is SS2 with the target Néron model also assumed semistable. SS2 and the printed Corollary 3.3 imply this restricted comparison.
- **VERIFIED (Lean):** `faltingsSemistableHeightBC_of_leaves`: the restricted comparison, `silverbergZarhinThm35`, and `neronSchemeExtensionDedekind` give the old field. The larger model lies over the compositum of the image of the intermediate field and the Raynaud field. Height minimality gives both inequalities.
- **VERIFIED (Lean):** Both contribution files compile. Lemma 1 in its DVR instance gives the identity-component comparison when both models are semistable. The global comparison uses localization at the primes left by spreading out; the old field follows from this comparison, Raynaud’s criterion and Néron existence. No additional leaf or Néron persistence is used.
- **VERIFIED (Lean):** `Axioms.lean` reports only `propext`, `Classical.choice`, and `Quot.sound` for all 14 new theorems, including the private helpers.
- **VERIFIED (dry run):** The autofold spec uses the Lemma 1 leaf and the two existing fields. The H count is 5/24 → 6/23 on 29, for strict and strictest. No fold was applied.
