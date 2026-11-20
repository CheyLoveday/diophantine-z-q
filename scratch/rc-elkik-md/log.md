# Manin–Drinfeld reduction results

- Base: `5152f326a7716248d0fd8dd905f70ddca6c05ad0`.
- Print: `ManinDrinfeld N cuspClass := Finite (AddSubgroup.closure (Set.range cuspClass))` for `J₀(N)(ℚ̄)` and `cuspClass r = [c(r)] − [∞]`. Astérisque 183, p. 59, Theorem (tex 2940, 11158–11160): UNVERIFIED against the page, GLUE (unread).
- `cuspidalImage_annihilator`: one positive integer kills every cusp image. `cuspSymbols_clear_denominator`: the same integer clears the period denominator on the set where the cusp comparison holds.
- `jacobiCharacter_isPrimitive`: odd squarefree modulus. `jacobiCharacter_fourier`: for `M ≡ 3 mod 4`, the Gauss sum is `ε i√M`, `ε = ±1`.
- `quadraticCuspSum_eq_twisted_value`: finite translates and the central Mellin integral give `Σ_a χ_d(a) s_f(a/|d|) = ε i√|d| Lval (qtwist E d)` after supplying the computed Fourier weights and twist coefficients. `genusPartner_twisted_coeff` supplies the coefficients from the existing dictionary.
- `imaginaryLattice_generator`: a nonzero imaginary lattice element is an integer multiple of `i * omegaMinus Lat`, with `omegaMinus Lat > 0`. `GenusPartner` supplies nonvanishing of `Lval` in the preceding sum.
- `curveNewform_eq_assemblyForm`: identical functions on the upper half-plane at the least level, from the existing modularity input and the assembly coefficients.
- `hElkikMD_of_assemblyForm`: `∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat d`; proof witness `n/(m κ)`.
- Residual: realize the printed cusp classes and prove `φ(cuspClass(a/|d|)) = [κ s_f(a/|d|)]` in `ℂ/Lat` at the fixed nonzero rational `κ`, on `a < |d|` with `χ_d(a) ≠ 0`. The assembly's hypothesis remains.
- Sequential `lake env lean` (load and available memory checked before each run): `Prints`, `Periods`, `Birch`, `QuadraticFourier`, `Reduction` passed. Axiom audit counts `1, 4, 6, 4, 5`; all lists `[propext, Classical.choice, Quot.sound]`. Transitive import check passed.
