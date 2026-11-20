# Results

- Setup: the three requested commits merged in order; all clean.
- Shared map: actual conductor-one reduction, selected residue Kummer map, and original detector row through inverse torsion specialization. Zero extension off the moving split support.
- Place: exact witness embedding at the witness; choose a single identification with the algebraic numbers in ℂ extending it and use the datum's given complex embedding elsewhere. Contract the detector's absolute prime. The contractions to the datum's quadratic field and to ℤ are the detector's restrictions.
- Witness: full homomorphism equality at the chosen row; no claim of equality with the witness-only map at other entries.
- Selector wiring: update the selected rows and the derived jgen; retain the old index at all prepared simple zeros.
- Reference row: the two pointwise CM inputs and the Artin/orbit data yield DatumAt.reduce using the constructed detector, place, reduction and shared family.
- `Actual.lean`, `Wiring.lean`, `Selector.lean`: passed `lake env lean` in the serial artifact overlay.
- `ev_eq_comp`: exact additive-map equality on the integral model; `evActual_witness`: witness pin on the transported model; `Setup.hev` and `Setup.toOddStagedInstance`: accepted by existing wiring.
- `selected_of_admissible` and `extendedIndex_at_simpleZero`: selector totality at admissible pairs, conditional on the selector lane's algebraic value, and agreement of the recomputed index on prepared simple zeros.
- `Transport.lean`: passed `lake env lean`. Normalizing the implicit additive instances across the curve presentation lets the existing integral equality supply the exact transported homomorphism equality.
- `Reference.lean`: passed `lake env lean`; `hev_at` and `reference_reduction` discharge the agreement and `DatumAt.reduce` from the two CM equations and the orbit inputs.
- Final assembly run initially held: precheck load 138.74 exceeded the devserver limit of 120; 161 GB available. Lean was not started for that file.
- `Assemble.lean`: passed `lake env lean`. Construct the comparison core at the actual theta norm, then transport only the norm index along `StageAt.m_eq`.
- Scratch axiom audit: 29 core declarations plus 2 assembly declarations. All returned exactly `[propext, Classical.choice, Quot.sound]`.
