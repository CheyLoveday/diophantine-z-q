# Equation (3.4) on the rough companions

The construction supplies the genus and ring-class selections for
`GenusOddInstance W`. For `h` in the prepared filter and `k'` a companion,
the ring-class datum uses `K = ℚ(√k')`, conductor `|h|`, the primitive
character `χ_h ∘ N`, and a primitive form of discriminant `k' |h|²`.
The remaining input for each point is the algebraic realization of the
value of the fixed parametrization at that form. The genus selection
reuses `StageSelector.datumOfPrepared`. Both coverage proofs are
independent of analytic rank.

`gz34CompAt_of_paramValues` gives the rough clause with `Cper = 0` without
requiring any final-companion input. `gz34Target_of_paramValues` applies
`Wiring.gz34Target_of_genusOdd` to the assembled instance, giving the
unchanged two-clause target. Both use the existing CST and Kolyvagin
route. No print was added. This does not supply (3.5), (F.3), or the
theta comparison.

All seven new Lean modules passed `lake env lean`. Every new theorem
has a `#print axioms` check; the only dependencies reported are
`propext`, `Classical.choice` and `Quot.sound`.

## Known issues

- The base interface combines the old fixed support and the later support
  enlarged by the primes of the final `k`. This is the documented
  order-of-choices departure in `RC/Wiring/CompanionLeaf.lean` and
  `RC/Skeleton/Steps.lean`: tex 2584–2603, 2609–2612, 2703–2704,
  10519–10521 use the old minimum before fixing `k`. The rough clause
  here does not use `k` or change a support or minimum. In the full
  target the five final-`k` fields are explicit, even though the
  manuscript only uses final `k` in Branch 2.
- The analytic `phiAn` is the existing CST dictionary, and the CST leaf
  starts with an algebraic point realizing its value. There is no
  canonical-model or CM-reciprocity existence conclusion in that leaf.
  Its header also records the unverified general Euler-factor dictionary
  at conductor primes and the exact height convention. This lane uses
  the existing split-case formula and `ArtinFactorization` interface and
  does not audit the external source or change either convention.
- The existing `Wiring.exists_genusPartner` uses the Hoffstein–Luo
  route with the BFH twist sign, while tex 8250–8254 chooses the
  partner using BFH clause (ii). This lane only uses the resulting
  `IsGenusPartner` predicates, so either choice can be supplied.
- `W.jgen` and `W.jrc` are total functions. The manuscript specifies
  their values where it uses them, not off the selection domain. For
  data under construction use the two selection readers as the
  definitions, in which case the equalities are reflexive, with zero
  at `none`. For fixed `W`, the equalities must be supplied; index
  invariance under arbitrary independent choices is not used here.
  A later witness or stage calculation must use the same chosen datum
  or prove compatibility with it. The base stage selector can still
  extend a supplied selector while retaining every existing entry.
- No new error was found in the manuscript steps used in this lane.
  External source statements were not independently reread. Source
  theorem numbers below are cited from the manuscript or repository,
  not from memory.

## Field audit

All Lean paths below are under `ZInQKernel/Contrib/OneProof/RC/` unless
qualified with a different root. The audit concerns the fields of
`Wiring.GenusOddInstance W` for the actual `Ecurve ℓ`.

| Fields | Supply and remaining status |
| --- | --- |
| `hE` | Yes for `0 < ℓ`: `PoleRC.curve_isElliptic`, through `curve_elliptic`. |
| `f`, `hf` | Yes from `Prints.bcdt`: `CloudB3RC53/ModularWeil/WeakWeil.lean` and `curve_form` use attainment of the positive least level and give every positive Fourier coefficient. The assembly accepts that choice so the value and index inputs can refer to it. |
| `Lat`, `hLat` | Yes: `ModularWeil.exists_isLatticeOf`, through `curve_lattice`, gives the lattice by complex uniformization with the required invariants. |
| `hNC` | Missing in the lattice formulation. `PrintsArith/Serre.lean` proves `j = 35152/9` and derives the distinct algebraic `HasNoCM` from `CMjInteger`; neither proves that all complex multipliers of the actual period lattice are integers. |
| `κ`, `hκ` | Conditional: `curve_scale` uses the existing `ModularWeil.NewformPeriodsRational`. `Contrib/RC53Assist/NewformPeriods/` breaks it into remaining translation steps. The assembly takes the actual chosen scale and its period inclusion, so both sums use the same `phiAn`. |
| `N`, `hN` | `Even/EvenSource.lean` supplies the RC11 normalization structure and anchor lemmas; the actual normalization and equality with the fixed interface `W.Lstar` are inputs. |
| `hElkikMD` | Named nonzero rationality of the single central value in the actual lattice convention. The RC11 anchor compares to its own period; no comparison with `omegaMinus Lat` is implicit. |
| `hgp` | `genusPartner_of_support` converts the existing `Wiring.IsGenusPartner` (chosen by `Wiring.exists_genusPartner`) using the support inclusion supplied by `curve_level_support` from `ModularNewform`. |
| `selG`, `hselG` | Constructed by `selectGenus` and `selectGenus_isSome` from the existing `PreparedParamValue` for each prepared parameter. |
| `selR`, `hselR` | Constructed by `datumOfCompanion`, `selectRing` and `selectRing_isSome` from `RingParamValue` for each prepared/companion pair. The arithmetic of the field, form and primitive character is proved. |
| `hprep` | `prepared_of_support` combines `PreparedSpec W`, the unit classes at `2N`, and avoidance of the partner through the support. `filterInputs_of_stageSupport` reads these from the existing `StageSupport`. |
| `hjg`, `hjr` | Definitional if the integrator chooses `W.jgen` and `W.jrc` from the selected data; explicit equalities for an existing `W`. |
| `hcomp` | `companion_of_rough` converts all the conditions of `W.IsRoughCompanion` using support and `hElkikMD` (which gives a nonzero imaginary period). |
| `hk0`, `hksq`, `hk4`, `hk2N`, `hkcop` | The final-companion inputs, already fields of `CompanionTarget` in Branch 2. The theorem with both clauses accepts them directly. |

## Declarations and consumers

The new declarations are in namespace `ZInQ.Manuscript.RC.Gz34Instance`.
Prefixes in the table name source files, not Lean namespaces.
Here `E` is the curve being parameterized, `s = h_*`, `N_E =
newformLevel E`, and `c = |h|` on a companion pair.

| Declaration | Statement and field supplied |
| --- | --- |
| `Forms.exists_ringHeegnerForm` | If `N > 0`, `d` is squarefree and a unit square at every prime of `2N`, and `N.Coprime c`, there are `B,C` with `IsHeegnerForm N (d*c²) N B C`. Supplies the form in `selR`. |
| `Forms.companion_formConditions` | `Prepared E s h` and `Companion E Lat s h k` imply `N_E.Coprime c` and `SquareAt p k` for every prime divisor of `2N_E`. Supplies form hypotheses. |
| `Forms.exists_companion_form` | With `N_E > 0`, the same two predicates give `∃ B C, IsHeegnerForm N_E (k*c²) N_E B C`. Supplies the form for `selR`. |
| `Character.norm_coprime_conductor` (private) | The absolute norm of any integral ideal prime to the conductor of a quadratic order `O_c` is coprime to `c`. Supplies the nonzero character value. |
| `Character.norm_character_trivial_on_principal` (private) | In an imaginary quadratic field a prime-to-conductor ideal with trivial Picard class has norm with Jacobi symbol one modulo `c`. Supplies descent. |
| `Character.exists_ringCharacter` | For an imaginary quadratic field and `d.natAbs = c ≠ 0`, there exists `χ : Pic O_c →* ℂˣ` with `IsQuadRingClassChar K c d χ`. Supplies `selR`'s quadratic norm character. |
| `Primitive.omitted_prime` (private) | A proper divisor `c'` of squarefree `c` omits some prime divisor of `c`. Supplies the conductor test. |
| `Primitive.ringClass_unramified_at` (private) | If `p ∤ discr K` and `p ∤ c'`, then `H_c'/ℚ` is unramified at `p`. Supplies the exclusion of the root from the smaller field. |
| `Primitive.no_square_root_at_omitted_prime` (private) | A field unramified at a prime of squarefree `h ≡ 1 (mod 4)` cannot contain a root of `h`. Supplies the same exclusion. |
| `Primitive.not_mem_of_no_root`, `exists_moves_of_not_mem`, `ringCharacter_ne_one_of_moves` (private) | If the smaller field has no root, the larger field’s root is outside it; an automorphism fixing the intersection moves that root; its character value is not one. Supply the primitivity witness. |
| `Primitive.ringCharacter_primitive` | When `h` is squarefree, `1 mod 4`, and prime to `discr K`, the norm character at `|h|` is primitive. Supplies `selR`'s primitivity. |
| `Selector.companion_nonsquare`, `conductor_ne_zero`, `conductor_coprime_disc` (private) | A companion is a rational nonsquare; preparation makes `|h| ≠ 0`; the companion is coprime to `h`. Supply the field and character hypotheses for `selR`. |
| `Selector.companionForm`, `datumOfCompanion` | Choose the proved form at level `N_E`; from `RingParamValue` and the proved field/form/character conditions construct `HeegnerDatum E f Lat κ k h.natAbs h`. Supplies `selR`'s entries. |
| `Selector.selectGenus`, `selectRing` | Choose the genus datum on `Prepared` and the ring-class datum on `Prepared × Companion`, respectively. Supply `selG` and `selR`. |
| `Selector.selectGenus_isSome`, `selectRing_isSome` | The corresponding predicates imply nonempty selections, with no rank-one hypothesis. Supply `hselG`, `hselR`. |
| `Curve.curve_elliptic`, `curve_form`, `curve_lattice`, `curve_scale` | Positive `ℓ` gives ellipticity and a uniformizing lattice; `Prints` gives positive level and `HasCuspFormAtLevel`; `NewformPeriodsRational` gives a compatible rational scale. Supply `hE,f,hf,Lat,hLat` and conditional `κ,hκ`. |
| `Curve.curve_level_support` | `Prints`, `ModularNewform` and positive `ℓ` put all primes of twice the actual level in `S0 ℓ`. Supplies the base support used by `hgp,hcomp`. |
| `Curve.squareAt_of_padic`, `coprime_of_avoids` (the latter private) | A local unit square over `ℚ_p` gives `SquareAt`; avoiding prime divisors of a nonzero integer gives coprimality. Supply filter and companion clauses. |
| `Curve.genusPartner_of_support`, `prepared_of_support`, `companion_of_rough` | Convert the actual `IsGenusPartner`, `PreparedSpec` with unit and avoidance data, and `IsRoughCompanion` with the level support and nonzero imaginary period. Supply `hgp,hprep,hcomp`. |
| `StageSupport.filterInputs_of_stageSupport` | For positive `ℓ`, the existing `StageSupport` and base level inclusion give `SupportSpec`, `PreparedSpec`, inclusion of the partner primes, and unit squares at `2N_E` for every prepared parameter. Supplies the support inputs to `hprep,hcomp`. |
| `Assembly.level_mem_support`, `omegaMinus_ne_zero_of_partner` (private) | Base level support and `SupportSpec` put all primes of `2N_E` in `W.S`; `hElkikMD` gives `omegaMinus Lat ≠ 0`. Supply parts of `hcomp`. |
| `Assembly.instanceOfParamValues` | Constructs `GenusOddInstance W` from the inputs below. |
| `Assembly.gz34CompAt_of_paramValues`, `gz34Target_of_paramValues` | From the corresponding instance inputs, `Prints`, `ArtinFactorization` and root numbers, give `Gz34CompAt W 0` and `Gz34Target W`. Only the second requires the final-`k` fields. |

For the ring class character, an ideal representing the identity has a
generator `a + c y` with `a ∈ ℤ`. Its absolute norm is a square modulo
`c`, since the quadratic field is imaginary and the norm modulo `c`
is `a²`. It is coprime to `c`, so its Jacobi symbol is one.
Multiplicativity and surjectivity of the ideal-to-Picard map then give
the character. The existing `exists_sqrt_mem_ringClassField` and
`genus_action` identify its action on `√h`. For any proper divisor
`c'` there is a prime dividing `h` but not `c'`. The base field and
the smaller ring class field are unramified there, whereas the
discriminant of `ℚ(√h)` is `h`. Thus the root does not belong to the
smaller field and the character is nontrivial on the subgroup fixing
the intersection. The case `h = 1` has no proper divisor and imposes
no primitivity test. These deductions are on-the-spot (c).

## Exact remaining inputs

| Inputs | Manuscript lines | Owner and minimum statement |
| --- | --- | --- |
| `P : Prints`, `hArtin : ArtinFactorization`, `hRN : Nonvanishing.FromRC8.RootNumberExists` | 1092–1093, 2346, 2428–2432; use at 10172–10178 | Existing shared leaves; the latter two are already supplied by `RCLeaves.artin` and `RCLeaves.rootNumberExists` through `ModularNewform` and Hasse convergence. No extra print. |
| `0 < ℓ`, and the choice of `f,hf,Lat,hLat` | 1012–1013, 1092, 1765–1767, 1825–1828, 2837–2838 | Actual curve data: admissibility supplies positivity; the choice exists by `curve_form` and `curve_lattice`. |
| `hNC : IsNonCMLattice Lat` | 1765–1767, 2837–2838 | Missing theory, medium to large: prove integrality of the lattice `j` for an extra multiplier and compare to the known rational `j(E_ℓ)`, or bridge the algebraic CM statement through analytic uniformization. The minimum is the multiplier assertion for the chosen `Lat`. |
| `κ` and `hκ : IsParamScale N_E f Lat κ` | 1092–1093, 1825–1828, 2430, 2837–2838 | ELLIOT parametrization input; missing theory, large. The minimum is a nonzero fixed scale with the Eichler periods in the chosen lattice. `curve_scale` gives existence given the prior `NewformPeriodsRational` glue. |
| `N : Even.CentralNormalization (Ecurve ℓ)`, `hN : N.Lstar = W.Lstar` | 1825–1830, 7175–7177 | RC11 input: choose the two periods and rational anchored values, then put that same function in `W`. Existence needs modular-symbol rationality (large); identification is a data choice (small). |
| `hElkikMD : ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = GenusOdd.Lstar (Ecurve ℓ) Lat W.hstar` | 1826–1828, 2404, 7175–7180 | ELLIOT input; missing Birch–Manin/Manin–Drinfeld period comparison, large. It concerns one nonzero value in the actual lattice convention; no new print. |
| `hpartner : IsGenusPartner ℓ W.hstar`, level support `hlevel0`, `hS : SupportSpec W`, `hprepared : PreparedSpec W`, `hstarS`, and `hpreparedLoc` | 1974–1979, 2344–2353, 2404–2410, 2460–2462 | Existing nonvanishing and stage-support inputs. `hlevel0` places primes of `2N_E` in `S0 ℓ`, `hstarS` places prime factors of `h_*` in `W.S`, and `hpreparedLoc` records the unit-square classes at `2N_E` for each prepared `h`. `curve_level_support` supplies `hlevel0` from the same `ModularNewform` as the shared leaves. `filterInputs_of_stageSupport` supplies the other filter inputs from the stage support (sibling field). |
| `halgG : ∀ h hp, StageSelector.PreparedParamValue E f Lat κ hN_E hgp hp` | 2411–2412, 8209–8217, 9272–9285, 9347–9350 | Missing theory, large: the algebraic realization over the conductor-one field at the already fixed form. |
| `halgR : ∀ h k hp hk, RingParamValue E f Lat κ hN_E hp hk` | 2413–2416, 2428–2431, 9347–9350 | Missing theory, large: the same value assertion over `H_c` for `K=ℚ(√k)`, at the already fixed form with discriminant `k c²`. |
| `hjg : W.jgen = jgenOf … selG`, `hjr : W.jrc = jrcOf … selR` | 2411–2416 | Integrator data choice (small). Set the fields to those native index readings when building `W`. |
| `hk0,hksq,hk4,hk2N,hkcop` | 2595–2603, 2692–2693 | Final companion lane, existing `CompanionTarget` outputs in Branch 2. Required only for `Gz34Target`. |

`RingParamValue` is the only new proposition taken as a hypothesis. It
asks for an embedding `ι : H_c →ₐ[ℚ] ℂ` and a single `y : E(H_c)`
with `ι(y) = phiAn E f Lat κ (cmPoint N_E B (k c²))`, for the
already chosen form. It supplies only `ι,y,hy` of a Heegner datum.
It contains no field-discriminant, form, character, primitivity, selector,
rank or comparison statement. In particular it does not assert either
index or any valuation identity. `PreparedParamValue` is the existing
conductor-one input of the same shape. Proving these minimal value
statements would let the selectors and instance assemble without CM-value
hypotheses; the remaining curve, period and interface inputs would still
be needed.

## Manuscript check

- 1012–1013, 1092–1093 — OK: use the actual elliptic curve and the existing modularity consequence for its coefficient-matching form.
- 1765–1767, 2837–2838 — unverified in the period-lattice formulation: the numerical invariant is formalized, its implication for lattice multipliers remains an input.
- 1825–1830, 7175–7177 — OK for the normalization used: one anchor and one scale on negative arguments; the normalization of `W` is explicit.
- 1974–1979, 2344–2353 — gap filled: the Hecke coefficient at `p²` puts the level primes in the bad-prime support; local unit squares then give the GenusOdd conditions.
- 2404–2410 — gap filled: the existing partner is a GenusOdd partner; the prepared filter avoids it and the companion is nonvanishing in the lattice convention. The nonzero rationality in that convention stays named.
- 2460–2462 — gap filled: use the existing intrinsic support for the prepared unit tests and the full support for prime exclusions.
- 2411–2412, 8209–8217 — unverified for the algebraic value: the conductor-one field, form and character are available, and its parametrization value needs the prior realization input.
- 2413–2416, 2429–2431 — gap filled: construct the ring-class form and primitive norm character with exactly the asserted conductor; the algebraic value is explicit.
- 2428–2440 — OK within the existing split-case CST/Kolyvagin interface and Artin factorization: the two unaveraged sums use the same parametrization, yielding (3.4) at every rough companion with period constant zero.
- 2584–2603, 2692–2693 — OK for the final comparison in Branch 2 given the final-companion data; see the known support-order departure of the base interface.
- 10172–10178 — OK for the use of (3.4): the rough clause supplies the required comparison before the odd minimum. The other inputs to (F.4) are outside this lane.
