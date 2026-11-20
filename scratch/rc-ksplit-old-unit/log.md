# Results log

- Base: `66fe8821b465fc3afc80f40b42acfe1192ec9794`.
- Old source: original curve, sign `-1`, reference `D₀`, denominator `C.Lstar (-(D₀ : ℤ))`; fixed minimum on `S0Filter S₀ D₀` with initial coprimality sieve `B`.
- `CompanionLeaf` / `CompanionTarget`: local properties and nonvanishing/rank zero; no unit at the fixed old depth. The old source cannot use the final `W.S` containing all primes dividing `W.kfin`.
- `AuxInputs`: read at `origin/wip/rc-aux-inputs`, absent from the assigned base. Its fixed type filter agrees with the original App E filter on the same pre-companion support; its source fields project directly at `B = ∅`.
- `mul_old_filter`: coprime multiplication preserves old squareclasses, dyadic residue and squarefreeness.
- `coprime_of_new_support`: excluding the prime factors of the old multiplier ensures coprimality.
- `Alignment.lean`: direct compile passed.
- `AxiomsAlignment.lean`: both checks report `[propext, Classical.choice, Quot.sound]`.
- `Source.lean`: `lake env lean -j1` passed; original App E phase, initial coprimality sieve, (E.11), and fixed minimum. Signed avoidance implies unsigned sieve membership. The existing reading detects nonzero coefficients attaining the minimum; some negative index attains it.
- `Comparison.lean`: `lake env lean -j1` passed; `old_transport_inputs` proves four inputs and `C.Lstar k ≠ 0` with the common old reference and support inclusions.
- `AxiomsComparison.lean`: all six checks report `[propext, Classical.choice, Quot.sound]`.
