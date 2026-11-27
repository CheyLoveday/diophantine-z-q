# Fixed-scale parametrization on the constructed modular curve

For the actual curve `Ecurve ℓ`, `ParamJoin.algebraicParametrizationAtScale` gives the dominant rational morphism on `X0Branch.model (newformLevel (Ecurve ℓ))`, at the supplied scale and with equality to `phiAn` at every upper-half-plane point. The prepared selector, the Stage Kummer selector holes, and the rough-companion form of (3.4) now use this model. The (3.4) wrapper supplies **both** `halgG` and `halgR`; its native-index equalities still refer to the existing, distinct selectors. The additional geometric input for these CM evaluations is `CMFieldOfDefinition` on the constructed model. Rationality of the already fixed scale is still an input. No new print, axiom or assumption structure was added.

The interface wiring is on-the-spot, provenance (c). For the companion let `K = Qsqrt k` and `c = h.natAbs`. On an integral basis `(1, ω)` of the quadratic field, take the second coordinate modulo `c`. This is onto `ℤ/cℤ` with kernel `ℤ + c 𝓞 K`; the order has index `c` and discriminant `k * c²`. The companion and prepared local tests give coprimality of that discriminant with the level. The CM field input can therefore be used at the exact `companionForm` and `conductorOrder` in `RingParamValue`. The proof neither changes the conductor-one selector nor identifies its point with the companion point.

## Statements and exact inputs

The names are in `ZInQ.Manuscript.RC.ParamJoin`. In this report `E := Ecurve ℓ`, `N_E := newformLevel E`, `X := X0Branch.model N_E`, and `hpos := (Gz34Instance.curve_form P hℓ).1` for the (3.4) assembly only. The following tables list all theorem binders (including data and typeclasses); bound variables in the conclusions are not additional setup hypotheses.

| Declaration | Statement and consumer |
| --- | --- |
| `AtScale.algebraicParametrizationAtScale` | `AlgebraicParametrizationAtScale E X f Lat κ`: a dominant map over ℚ with the stated projective point equality on the whole interior chart. Instantiates `ModFnClassify.algebraicParametrizationAtScale`. |
| `AtScale.prepared_values` | `∀ h (hp : Prepared E W.hstar h), StageSelector.PreparedParamValue E I.f I.Lat I.κ (StageKummer.positiveLevel s) I.hgp hp`. Instantiates `ModFnClassify.prepared_values`. |
| `AtScale.missing_values` | `StageKummer.MissingParamValues s`: the same value at each admissible `D ≠ s.Dw` with `I.selG D = none`, for the prepared proof obtained from `s`. Instantiates `ModFnClassify.missing_values` for the existing selector extension. |
| `RingValues.conductorOrder_discr` (private) | For a quadratic number field `K` and `c ≠ 0`, `(conductorOrder K c).discr = NumberField.discr K * (c : ℤ)^2`. Checks the order discriminant for the companion CM evaluation. |
| `RingValues.ring_values` | For `s : ℤ`, `∀ h k (hp : Prepared E s h) (hk : Companion E Lat s h k), Gz34Instance.RingParamValue E f Lat κ hpos hp hk`. Applies `PreparedParam.value_of_cmFieldOfDefinition` to the exact companion form; supplies `halgR`. |
| `Assembly.genus_values` | `∀ h (hp : Prepared E W.hstar h), StageSelector.PreparedParamValue E f Lat κ hpos (Gz34Instance.genusPartner_of_support hpartner hlevel0) hp`. Instantiates `PreparedParam.genusParamValues`; supplies `halgG`. |
| `Assembly.gz34CompAt` | `Gz34CompAt W 0`: for every prepared simple zero `h` and rough companion `k`, there is `ε : ℤ` with `abs ε ≤ 2` and `2 * W.jrc h k - 2 * W.jgen h = padicValRat 2 (W.Lstar (h * k)) - padicValRat 2 (W.Lstar W.hstar) + ε`. Calls the existing rough assembly `Gz34Instance.gz34CompAt_of_paramValues` with the two families just proved. |
| `Cusps.algebraicParametrizationAtScale_and_cuspLimits` | The same `AlgebraicParametrizationAtScale E X f Lat κ`, together with a nonzero `c : ℚ` casting to `κ`; `torusValue Lat f κ` tends to zero at infinity, and along every `σ` taking infinity to `r : ℚ` tends to `QuotientAddGroup.mk' Lat.lattice.toAddSubgroup ((c : ℂ) * cuspSymbol f r)`. Instantiates the analytic cusp comparison in `ParamAtScale` at the very same scale as the algebraic map. |

`X` is constructed in every statement. No theorem takes a new structure or Prop as a hypothesis. The inherited `CMFieldOfDefinition X` asserts descent only of the *source* CM point: for the given imaginary quadratic field, order, negative discriminant coprime to the level and primitive Heegner form, the prescribed complex point is the image of an `H`-point under some embedding of the ring class field `H`. Its statement has no elliptic curve, parametrization, elliptic value, or comparison of indices (tex 2839–2844, 2915–2917). The scale witness describes one scalar, and supplies no map or value (tex 1785–1787, 1825–1828).

| Theorem(s) | Exact remaining inputs | Tex and owner |
| --- | --- | --- |
| `algebraicParametrizationAtScale`, `algebraicParametrizationAtScale_and_cuspLimits` | `ℓ : ℕ`, `[E.IsElliptic]`, `[NeZero N_E]`, `f : CuspForm (Γ₀(N_E) : Subgroup (GL (Fin 2) ℝ)) 2`, `hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ)`, `Lat : PeriodPair`, `hLat : IsLatticeOf E Lat`. | 1765–1784, 1825–1828; existing actual-curve data. `curve_elliptic` and `curve_form` supply the first two curve properties for `0 < ℓ` with the existing modularity input; `curve_lattice` supplies existence. |
| Same | `κ : ℂ`, `hκ : IsParamScale N_E f Lat κ`, `hr : ∃ c : ℚ, (c : ℂ) = κ`. | 1785–1787, 1825–1828; ELLIOT fixed parametrization data. The geometric comparison to the chosen quotient differential is large. |
| `prepared_values`, `missing_values` | `ℓ : ℕ`, `W : WData ℓ`, `I : GenusOddInstance W`, `L : ℕ`, `s : StageKummer.Setup I L`. The level proof comes from `s`; the map uses `I.hE, I.f, I.hf, I.Lat, I.hLat, I.κ, I.hκ`, and the prepared family uses `I.hgp`. The missing family also uses `I.hprep`, `I.selG`, the witness and the stage filter of `s`. | 1765–1787, 1825–1828, 2404–2416, 2460–2493, 8211–8217, 9272–9285; existing genus wiring and Stage Kummer setup, owned by the sibling stage lane. |
| Same | `hr : ∃ c : ℚ, (c : ℂ) = I.κ`; `hCM : CMFieldOfDefinition X` with `NeZero N_E` obtained from `StageKummer.positiveLevel s`. | 1785–1787, 1825–1828: ELLIOT fixed scale; 2839–2844, 2915–2917, 8211–8217: CM field-of-definition sibling lane. |
| `conductorOrder_discr` | `K : Type`, `[Field K]`, `[NumberField K]`, `Module.finrank ℚ K = 2`, `c : ℕ`, `[NeZero c]`. | 2413–2414, 2841–2844; existing quadratic field and conductor data from the companion/prepared inputs. The index calculation here requires no further theory. |

The remaining (3.4) inputs are exactly the union of the rows below. `ring_values` uses the first four rows, with `s : ℤ` in place of `W`; `genus_values` uses the first five. Positivity of the level and ellipticity are derived within those two theorems and do not appear as independent assumptions of the assembly.

| Input | Manuscript lines | Owner and size |
| --- | --- | --- |
| `ℓ : ℕ`, `W : WData ℓ`, `hℓ : 0 < ℓ`, `P : Prints` | 1012–1013, 1092–1096, 1765–1784, 2428–2432 | Existing curve/interface data and shared prints. |
| `f : CuspForm (Γ₀(N_E) : Subgroup (GL (Fin 2) ℝ)) 2`, `hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ)`, `Lat : PeriodPair`, `hLat : IsLatticeOf E Lat` | 1779–1784, 1825–1828 | Existing actual-curve data, with existence from `curve_form` and `curve_lattice`. |
| `κ : ℂ`, `hκ : IsParamScale N_E f Lat κ`, `hr : ∃ c : ℚ, (c : ℂ) = κ` | 1785–1787, 1825–1828, 2430 | ELLIOT input; the comparison with the particular geometric quotient scale is large. |
| `hCM : CMFieldOfDefinition X` at the level instance from `hpos` | 2411–2416, 2839–2844, 2915–2917, 8211–8217 | CM field-of-definition sibling lane; the full descent is substantial. |
| `hpartner : IsGenusPartner ℓ W.hstar`; `hlevel0 : ∀ p : ℕ, p.Prime → p ∣ 2 * N_E → p ∈ S0 ℓ` | 2344–2351, 2404–2410 | Existing genus-partner/nonvanishing input; existing `curve_level_support` proves the level test given `ModularNewform`. |
| `hNC : IsNonCMLattice Lat` | 1765–1767, 2836–2838 | Missing theory, medium to large: identify non-CM of the given rational curve with the multiplier statement for the chosen lattice. |
| `N : Even.CentralNormalization E`, `hN : N.Lstar = W.Lstar` | 1825–1830, 7175–7177 | RC11 normalization; anchored rational values (large); use that same function in `W` (small). |
| `hElkikMD : ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar E Lat W.hstar` | 1826–1828, 2404, 2937–2941, 7175–7180 | ELLIOT input; existing Elkik–MD reduction leaves the geometric comparison described below. |
| `hS : SupportSpec W`, `hprepared : PreparedSpec W`, `hstarS : ∀ p ∈ W.hstar.natAbs.primeFactors, p ∈ W.S`, `hpreparedLoc : ∀ h, W.prepared h → ∀ p : ℕ, p.Prime → p ∣ 2 * N_E → SquareAt p h` | 1974–1979, 2344–2353, 2404–2410, 2460–2462 | Existing support and filter data, reviewer’s stage-support field. |
| `hjg : W.jgen = jgenOf E f Lat κ W.hstar (Gz34Instance.selectGenus hpos (Gz34Instance.genusPartner_of_support hpartner hlevel0) (genus_values P hℓ hf hLat hκ hr hCM hpartner hlevel0))` | 2411–2412, 2415–2416 | Existing integrator data choice (small): read the genus index from this selector. |
| `hjr : W.jrc = jrcOf E f Lat κ (Gz34Instance.selectRing hpos (ring_values P hℓ hf hLat hκ hr hCM (s := W.hstar)))` | 2413–2416 | Existing integrator data choice (small): read the ring-class index from its own selector. |
| `hArtin : ArtinFactorization`, `hRN : Nonvanishing.FromRC8.RootNumberExists` | 1779–1784, 2346, 2428–2432 | Existing shared leaves and analytic consequences. |

## Scale and the cusp specialization still needed

`IsParamScale` gives nonvanishing and inclusion of the scaled Eichler periods in `Lat`. The rational Fourier coefficients concern `f`, and `IsLatticeOf` identifies the two Weierstrass invariants of `Lat`. The tree does not derive `∃ c : ℚ, (c : ℂ) = κ` for the given `κ` from these data. The existing `curve_scale` uses `NewformPeriodsRational` to **choose** a rational scale; replacing the supplied scale by that choice would change the parametrization used by the selectors. The existing `exists_rat_eq_of_pullbackIsMultiple` proves rationality given a nonzero coefficient and a rational Laurent pullback differential identity. That result does not supply the identity for the given `κ`. The witness is ELLIOT input for this join; this is a statement about the current inputs and theorems, not a claim of logical independence. In the manuscript the choice is made by the ℚ-isogeny `α` and the based map `π(x) = (α q_f)([x] − [∞])` at 1785–1787; 1825–1828 fixes the periods by this same `π` and the integral lattice and keeps that normalization throughout. A sufficient missing geometric comparison for the rational witness is that the pullback of the rational invariant differential on `E` by this particular π has rational width-one expansion and equals `κ (2πi f(τ) dτ)` in the fixed uniformization; the normalized first coefficient then detects `κ`.

`Cusps` gives boundary values in `ℂ/Lat` of `τ ↦ [κ · eichlerPotential f τ]`. For the remaining `hAJ` of `ElkikMD.hElkikMD_of_assemblyForm`, let `d` be the genus partner, `r = (a : ℚ) / d.natAbs`, with `a < d.natAbs` and `chiD d a ≠ 0`. The exact missing comparison is `φ (cuspClass (r : OnePoint ℚ)) = QuotientAddGroup.mk' Lat.lattice.toAddSubgroup ((c : ℂ) * cuspSymbol f r)` for all those `a`, where `cuspClass r` realizes `[c(r)] − [c(∞)]` in the genuine `J₀(N_E)`, and `φ` realizes `α q_f` in the chosen torus. Geometrically, it suffices to identify the algebraic cusp points `c(r), c(∞)` on `X` as the source specializations of the matching charts, and show that their images, differenced with `c(∞)` as basepoint and sent through a compatible complex uniformization with the torus, are the analytic limits just computed, with the map identified with the Abel–Jacobi composite. The based specialization is thus also separate from the proof of the interior map. This is substantial Jacobian and cusp specialization theory; the equality above is the small statement needed at the weighted cusps. Once the actual cusp classes, the homomorphism, that comparison, and the existing Manin–Drinfeld and modular-newform inputs are supplied, the existing Elkik–MD theorem yields `hElkikMD` for (3.4).

## Known issues

- The inherited audit in `ZInQKernel/Contrib/OneProof/RC/PrintsAnalytic/Milne.lean` records a citation scope error: the pair cited at tex 1784 gives the modular map and Jacobian quotient to the elliptic curve, but the normalized newform is addressed in Milne’s Proposition 11.21, and the cited pair does not state the Hecke identity at tex 1788. Its audit also records two unused misprints in Conjecture 11.17 (the prime/coprime wording and conductor factor). These locators come from that audit. This join does not invoke the Hecke identity.
- The independent locator for the CM field-of-definition statement and the exact wording of the Elkik page are **UNVERIFIED** in this run. The existing CCL trace and Elkik interfaces were left unchanged. Here a conductor and its order discriminant have different roles: the latter is `k * |h|²` at the companion and `h * h_*` at conductor one.
- The prepared and ring values do not identify either chosen form with an independently fixed oriented reference family, and the report makes no claim about reduction of CM points, trace relations, or Hecke equivariance.

## Manuscript check

| Tex and step | Verdict |
| --- | --- |
| 1765–1767, 1779–1784: actual curve and normalized coefficients at its level. | OK — use the existing curve and coefficient data. |
| 1781–1784, 1788: locators for the newform and the Hecke identity. | Error — inherited citation scope issue recorded above. |
| 1785–1786, 2836–2838: rational modular morphism to the actual curve. | Gap filled — instantiate the interior comparison on the constructed model, with the manuscript’s fixed scale supplied (c). |
| 1787, 2838: image of the algebraic cusp at infinity. | Unverified — the analytic based limit is proved; algebraic specialization is separate. |
| 1825–1828: keep the normalization of the chosen parametrization. | OK — carry the same scalar and require its rational representative explicitly. |
| 1974–1979, 2344–2353, 2404–2410: prepared filter, local squares, and genus partner. | OK — existing hypotheses put the exact selector forms in scope. |
| 2411–2412, 8211–8217: conductor-one point at the prepared form. | Gap filled — evaluate the fixed rational map on the source CM point over its conductor-one field (c). |
| 2413–2416, 2841–2844: conductor-`|h|` companion point and native indices. | Gap filled — check the order discriminant and its coprimality, and evaluate at the separate companion form (c). |
| 2428–2439: two height applications at the same scale give (3.4). | OK — use the existing CST/Kolyvagin assembly and native indices, without another height argument. |
| 2460–2493, 9272–9285: same witness and prepared values for the stage inputs. | Gap filled — fill exactly the existing admissible nonwitness holes; the reference orbit comparison remains separate (c). |
| 2839–2844, 2915–2917: field of definition of the enhanced CM point. | Unverified — this remains the existing `CMFieldOfDefinition` input, whose primary source locator was not checked here. |
| 2937–2941: cusp correction in the image of the cuspidal subgroup. | Unverified — the analytic limits agree with the scaled symbols, but the actual cusp classes and their images under `α q_f` are not identified by the limit theorem. |
| 7175–7180: normalized central value in the chosen period convention. | Unverified — the existing normalization and the nonzero rational value for `h_*` remain inputs. |

## Validation

`AtScale.lean`, `RingValues.lean`, `Assembly.lean`, and `Cusps.lean` in `ZInQKernel/Contrib/OneProof/RC/ParamJoin/` passed serial `lake env lean -j1 -DautoImplicit=false`. Resource limits were checked before each invocation. The eight `#print axioms` outputs cover all eight theorems and report exactly `propext`, `Classical.choice`, and `Quot.sound`. The transitive repository imports do not include `ZInQKernel.OneProof.Main`. No existing Lean file was edited.
