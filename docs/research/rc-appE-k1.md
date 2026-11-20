# Appendix E at the fixed curve: (K1) and (E.1)

Scoped stop: the existing Appendix E antecedent does not supply retained Kato classes at every level needed by (K1) and (E.1). It also does not identify the classes it supplies with genuine continuous cohomology. The finite specialization algebra is separate from those comparisons.

## Known issues

- **Range mismatch (verified in the Lean interface):** the existential `Sig ⊇ Sbad` is chosen before the family. `es_euler` only applies with both levels in `KatoXi 2 Sig`, so it excludes any family for which an odd prime of `F) lies in `Sig`. In particular, a common odd conductor prime dividing the fixed level obstructs this application. The condition on local squareclasses only forces ramification at that prime to be common; it does not forbid it. The Σ of tex 6993 is for the twisted variable `m`; applying the existing narrow relation to `D*m` would be a range error. Tex 7089 instead cites Proposition 8.12; its required wider range is not part of the current interface.
- **Smoothing mismatch (verified in the Lean interface):** the single nonzero `s` is not tagged by `c,d_s` and does not identify the elements used at `F) with those of (K5). The family-dependent exact scalar of (K6) and one lattice constant fixed before all families are not supplied.
