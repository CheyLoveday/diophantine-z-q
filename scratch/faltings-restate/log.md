# Results log

- **VERIFIED (source):** The base is `be73b91c5`; `TailZ87` carries the height field as a GLUE consequence. The published invariance applies to a semiabelian scheme and its base change (Faltings 1983 §3 p. 354 and p. 351 Bem. b), pages read by the reading desk).
- **VERIFIED (Lean):** `IsSemiabelianModel` checks connected special fibres and `HasSemiAbelianIdCompTorus` on `resFibre`; the generic fibre is already abelian. `faltingsHeightBaseChange` follows from H4a alone, which is stated for every group model.
- **VERIFIED (Lean):** `SemistableNeronIdentification` is SS2 with the target Néron model also assumed semistable. SS2 and the printed Corollary 3.3 imply this restricted comparison.
