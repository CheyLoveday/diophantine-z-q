# Results log

- Base: `7b5e84d80db4189e5a11e47279ef0ed789399344`.
- `transportedNormalization`: `Lstar' h = C.Lstar (h * k)`; periods swap and divide by the square root of the absolute value of `k`.
- `exists_evenSupport`: finite support extension by 2 and every level prime; `level_sign_unique` on the nonzero continuation.
- `genuineEvenSource_of_prints`: `EvenPhaseData` at sign +1 and reference index 1; (E.11) on exactly `S0Filter S 1`.
- `genuineEvenSource_of_companion`: reference nonvanishing from `CompanionLeaf`; central value alignment from `LstarNormalized`.
- `genuineEvenSource_for_labels`: support includes `Sold`, the companion primes and the primes of `m₂`.
- `freshPrime_of_support`: prime divisor of `k` outside `m₁`; `LabelData` lacks the support inclusion and `CompanionLeaf` omits the avoidance from `exists_companion`.
- `omegaN_prod_primes`, `revGen_eq_one`: prime product count `U.card`; a unit has nonzero rational coefficient of valuation `U.card`.
- `lstar_eq_of_revGen`, `evenReading_of_genuineEven`: (F.1) equality at depth zero, constant `padicValRat 2 (W.Lstar W.kfin)`.
- `evenFilter_of_genuineEven`: square modulo `m₂` by the Appendix E Hensel and CRT lemma.
- `addressDensityLeaf_of_genuineEven`: variant implies the existing leaf under the Branch 2 companion.
- Verification: `Normalization.lean`, `Source.lean`, `Leaf.lean`, `DensityLeaf.lean` passed serial `lake env lean -j1` without warnings.
- `Axioms.lean`: passed; 15 audit entries, each lists exactly `propext`, `Classical.choice`, `Quot.sound`.
