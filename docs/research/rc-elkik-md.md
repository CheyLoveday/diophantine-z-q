# Manin–Drinfeld and the genus partner’s central value

**Scoped stop.** Elkik’s printed result does not on its own cover `hElkikMD`. The Lean reduction
gives the exact nonzero rational witness for `GenusOdd.Lstar (Ecurve ℓ) Lat hstar` from the finite
cuspidal subgroup and one geometric comparison: at each cusp that occurs with a nonzero weight
in the quadratic sum, the image of its divisor class in `ℂ/Lat` is the class of the modular symbol
times the same nonzero rational pullback scalar. Lean proves the common denominator, the twisted
Birch formula, the normalization by `omegaMinus Lat`, and the nonvanishing from `GenusPartner`.
The actual geometric comparison is still missing. The assembly and its `hElkikMD` input stay in
place.

The base is `5152f326a7716248d0fd8dd905f70ddca6c05ad0`. At the manuscript’s fixed `E = Ecurve ℓ`,
write `N = newformLevel E`, `d = hstar`, `M = |d|` and `χ(a) = χ_d(a)`. Write
`s_f(r) = -2πi ∫_r^{i∞} f(z) dz`, so the orientation is from infinity to `r`. Then the sum used
below is `S = Σ_{0 ≤ a < M} χ(a) s_f(a/M)`. Fourier inversion suffices to prove that the Gauss sum
is `± i√M`; no choice of its sign is required. The common denominator `m` from the finite group
gives `m κ S ∈ Lat`. After removing the sign, the imaginary coefficient of this lattice element
is `m κ √M L(E^(d), 1)`. It is nonzero by the partner choice. Discreteness of the lattice on the
imaginary axis yields an integer `n` times `omegaMinus Lat`, and the witness is `n/(m κ)`.

## Lean statements and consumers

All files are under `ZInQKernel/Contrib/OneProof/RC/ElkikMD/`. The statements below suppress
ambient types when they are already fixed above.

| Statement | Consumer |
| --- | --- |
| `cuspidalImage_annihilator`: `Finite (closure (range cuspClass)) → ∃ m : ℕ, 0 < m ∧ ∀ r, m • φ (cuspClass r) = 0`, for an additive homomorphism `φ`. | Tex 2941–2942; supplies the denominator for `cuspSymbols_clear_denominator`. |
| `cuspSymbols_clear_denominator`: with Elkik’s finite subgroup and `φ(cuspClass r) = [κ s_f(r)]` on a set `S₀` of rational cusps, there is one `m > 0` such that `m κ s_f(r) ∈ Lat` for all `r ∈ S₀`. | Supplies the rational period step in `hElkikMD_of_cuspidalSubgroup`. |
| `lval_eq_ofReal_re`: `(Re (Lval E) : ℂ) = Lval E`. | Ensures the central-value numerator, after the factor `i`, lies on the imaginary line. |
| `imaginaryLattice_generator`: if `x : ℝ` is nonzero and `x i ∈ Lat`, then `0 < omegaMinus Lat` and `∃ n : ℤ, x = n * omegaMinus Lat`. | Gives the denominator convention in `Defs.lean` and the nonzero imaginary period required by `companion_of_rough`. |
| `hElkikMD_of_cuspidalSubgroup`: `GenusPartner E d`, the finite subgroup, the cusp comparison on the support of `χ`, and `S = ε √M Lval (qtwist E d) i` with `ε = ±1` imply the named nonzero rationality proposition. | The conditional lattice part of `hElkikMD_of_maninDrinfeld`; supplies both the rationality used by `Artin34`/`ArtinEndpoints` and the stronger witness used by assembly. |
| `jacobiCharacter_intCast`: `jacobiCharacter M (a : ℤ) = (jacobiSym a M : ℂ)`. | Connects the finite Fourier transform to the coefficient dictionary and the genus character. |
| `jacobiCharacter_isPrimitive`: the character is primitive for odd squarefree `M > 0`. | Supplies the finite Fourier transform formula via the existing Dirichlet character lemma. |
| `jacobiCharacter_fourier`: for squarefree `M ≡ 3 mod 4`, there is `ε = ±1` with `M⁻¹ DFT χ(a) = χ(a)/(ε i√M)` for every residue `a`. | Discharges the Fourier input to the analytic Birch identity. |
| `quadraticCuspSum_eq_twisted_value`: if the Fourier weights for a cusp-form twist are `χ(a)/τ`, `τ ≠ 0`, and its positive-index coefficients agree with those of `qtwist E d`, then `S = τ Lval (qtwist E d)` given an entire continuation of that curve’s series. | Discharges the Birch input of `hElkikMD_of_cuspidalSubgroup`. The continuation is already part of the partner’s analytic rank zero. |
| `chiD_eq_kronecker_pos`: for `d ≡ 1 mod 4` and `n ≠ 0`, `chiD d n = kronecker d n`. | Extends the existing prime calculation to the domain of the coefficient dictionary. |
| `genusPartner_twisted_coeff`: if `f` is the curve’s newform, `jacobiCharacter d.natAbs n * a_n(f) = a_n(qtwist E d)` for `n > 0` and `GenusPartner E d`. | Discharges the coefficient comparison in the Birch identity using the existing twist dictionary, including at bad primes. |
| `hElkikMD_of_maninDrinfeld`: for the actual `Ecurve ℓ`, its newform and `GenusPartner E d`, Elkik’s finite group and the rational-scale cusp comparison imply `∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = GenusOdd.Lstar (Ecurve ℓ) Lat d`. | Exactly `Gz34Instance.hElkikMD` at `d = W.hstar`; projection drops `q ≠ 0` for the rationality-only consumers. |
| `curveNewform_eq_assemblyForm`: the existing `ModularNewform` input and the assembly’s coefficient-matching `Γ₀(N)` cusp form give a matching `Newform N 2` with the same function on the upper half-plane. | Transfers the cusp comparison from the exact assembly form to the newform used for the coefficient dictionary. |
| `hElkikMD_of_assemblyForm`: with `ModularNewform`, the given coefficient-matching `Γ₀(N)` form, the chosen partner, Elkik’s finite group and the same cusp comparison for the given form, the witness is `∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = GenusOdd.Lstar (Ecurve ℓ) Lat d`. | Directly gives the named input for the existing `Lat` and form, again at `d = W.hstar`. |

Private lemmas: `jacobi_congr` identifies Jacobi values for equal classes modulo `M`.
`translation_det` and `translation_slash` say that the translation matrix has positive determinant
and slashing translates the integrand. `cuspSymbol_eq_integral` identifies the symbol with
`2π ∫₀^∞ f(r+it) dt`; `integrable_translate` gives absolute convergence; `l_one_eq_symbol` proves
`L(g, 1) = s_g(0)` for a weight-two cusp form on `Γ₁(L)`. These are intermediate steps for the
Fourier and analytic Birch theorems, not direct assumptions of an instance or endpoint.

The Birch calculation, its Gauss-sum sign argument, and their connection to the imaginary
lattice generator are on-the-spot proofs (c). No citation is used as a leaf for these steps.

## Exact remaining inputs

| Input | Manuscript lines | Owner and size |
| --- | --- | --- |
| Realize `J = J₀(N)(ℚ̄)` and `cuspClass(r) = [c(r)] − [∞]` for rational cusp representatives, then supply `ManinDrinfeld N cuspClass`. | 2937–2942, 11158–11160 | The named Elkik print, GLUE (unread) pending the lead’s source check. The geometry of the actual classes and their maps is missing theory, large. The parameter in `Prints.lean` is a placeholder for the actual group of points and class map; it is not an arbitrary group for which the theorem claims finiteness. |
| For `φ : J →+ ℂ/Lat` induced by `α q_f` and elliptic uniformization, exhibit `κ : ℚ`, `κ ≠ 0`, with `φ(cuspClass(a/M)) = [κ s_f(a/M)]` for every `a < M` with `χ_d(a) ≠ 0`. | 1781–1787, 1825–1828, 2836–2838, 2937–2946, 7137–7139, 7175–7177 | ELLIOT input / missing theory, large for the actual comparison; the finite restriction shown is the exact remaining statement. It amounts to comparing the pullback of the differential and its cusp integrals under the fixed parametrization. It follows from the usual uniformization and differential pullback calculation; the restricted comparison is an on-the-spot step (c), not stated in the cited Elkik result. |
| The fixed curve, positive level, modularity, given form and genus partner: `[(Ecurve ℓ).IsElliptic]`, `[NeZero (newformLevel (Ecurve ℓ))]`, `PrintsAnalytic.ModularNewform`, assembly `hf`, and `GenusPartner E d`. | 1012–1013, 1092–1093, 1765–1767, 1779–1787, 2404–2410, 8250–8254 | Existing curve, BCDT modularity input, and nonvanishing. `Gz34Instance.genusPartner_of_support` gives `GenusPartner` once the base support contains `2N`. `curveNewform_eq_assemblyForm` proves that the newform has the given function at the fixed level, so no additional form comparison is needed. |

The new proposition `ManinDrinfeld` asserts only finiteness of the subgroup generated by cusp
classes; it contains no cusp integrals, differential, elliptic periods, twist, or `L`-value. The
new geometric hypothesis `hAJ` compares two images of individual cusp classes, without reference
to a twist central value or its rationality. It can be stated with no `L`-function theory; even
combined with finiteness it does not make an assertion about `Lval` until the separate twist proof
is applied. The intermediate hypotheses in `Birch.lean` concern the discrete transform, the
Dirichlet coefficients, and existence of continuation. The `hBirch` hypothesis of the lattice
theorem equates unnormalized *complex* values without asserting a rational coordinate; the final
reduction supplies it by theorem. There are no new hypothesis structures.

This lane would discharge only the named central-value input of the base assembly. The independent
inputs remain as listed in [the base report](rc-gz34-instance.md#exact-remaining-inputs): in
particular the normalization of the whole `W.Lstar` is a separate RC11 input, the algebraic CM
values belong to the parametrization work, and the stage support and final companion stay in their
respective lanes.

All five new modules passed `lake env lean` sequentially. The 20 `#print axioms` audits
list only `propext`, `Classical.choice`, and `Quot.sound`. The transitive import check found
neither `ZInQKernel.OneProof.Main` nor TYZ. No existing Lean files were changed.

## Known issues

- Elkik’s page was not available for direct inspection. The exact wording and hypotheses at
  Astérisque 183, p. 59, Theorem are **UNVERIFIED** here. The manuscript gives the finite-group
  specialization to `Γ₀(N)`; the existing `RC/PrintsArith/Heegner.lean` gives a prior transcript
  in torsion form for a congruence subgroup and states that the scan was read for that lane. The
  specialization and the inference from torsion to finiteness for the finitely many cusp classes
  should be checked against the page. The lead decides any upgrade from GLUE to LEAF.
- The existing `PrintsArith.ManinDrinfeld` is an analytic reformulation that already needs
  Abel–Jacobi. It is not used to assume the remaining comparison here. The attribution of
  rationality to Manin–Drinfeld in `GenusOdd/Defs.lean` omits the comparison and the quadratic
  twist calculation. This is a gap in the formal attribution; no error was found in the
  manuscript’s use of the finite group for the cusp corrections.
- `IsParamScale` gives invariance for a complex scalar, and the existing `NewformPeriodsRational`
  proposition requests a rational period scale. Neither gives the actual cusp images in `ℂ/Lat`.
  `RC53Assist/NewformPeriods/RationalParametrization.lean` does prove rationality of a pullback
  scalar from a rational Laurent expansion and the differential identity; it does not realize
  those data for the fixed `α q_f` or identify its values at these cusps.
- RC11’s `CentralNormalization.anchor` begins with rational numbers relative to its own positive
  period `Ωm`. It neither supplies the comparison with the actual `omegaMinus Lat` nor proves
  existence of that normalization by itself. It was not used to infer `hElkikMD`.

## Manuscript check

- 1779–1787, 2836–2838 — unverified for the actual geometry in Lean: the comparison of the two presentations of the newform is proved; the rational-scale comparison between the cusp images and the periods of `Lat` is missing.
- 1825–1828, 7175–7180 — gap filled: the proof takes the least positive generator of the imaginary sublattice of this `PeriodPair`; no comparison with an arbitrary RC11 period is used.
- 2404–2410, 8250–8254 — OK: the partner is a negative odd fundamental discriminant prime to the level, and its existing analytic rank zero proves `Lval ≠ 0` without invoking rationality.
- 2937–2946, 11158–11160 — unverified against the printed page: the cited finiteness supplies a single cusp annihilator as stated. **It does not cover `hElkikMD`** without the geometric comparison and the separately proved twist calculation.
- 7118–7139, 7188–7192 — gap filled for the central value only: the quadratic character and Gauss sum calculations and the Mellin identity give the weighted cusp sum in the sign convention above. This does not verify the separate Euler-system comparison in Appendix E.
- 2438–2439, 10172–10178 — unverified as an unconditional lattice rationality input: the needed nonzero rational witness is the conclusion of `hElkikMD_of_maninDrinfeld`, conditional on the geometric comparison and the print.
