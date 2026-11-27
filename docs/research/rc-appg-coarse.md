`depths_of_prepared_stages` derives (F.5), the attained minimum, and the
budgeted `IntegerDepth` on the full intrinsic odd filter. Its arithmetic
inputs are (F.3), (3.4), and (3.5) on the original prepared data. Its odd
inputs are (O.7), the native and torsion comparisons on the same Kummer
lifts, and (O.2) at the fixed witness. It uses one ultrafilter and one
chosen depth for every fixed budget. On an eventual set of stages for
`W,R` with `R ≥ 2`, it gives
`T₀ = max(0, δ + W) + R ≤ M` and `min(T₀, δ + ω(n)) ≤ v₂ a(n)`
for every squarefree `n` on the intrinsic filter, without bounding `ω(n)`.
No unconditional instance of the arithmetic or theta data is constructed.

The intrinsic instance is the positive squarefree unit-squareclass
filter of the original support, intersected with the stage's Legendre
condition. `depths_on_filter` also takes the exact domain directly, so
it can use an intrinsic source whose actual fixed sieves add only
coprimality tests. In that case use the supplied domain; treating a
coprimality sieve as a squareclass test would shrink it. Neither route
uses an address-filter minimum. Changing only `admissible` cannot widen
the arithmetic preparation; use (F.3), (3.4), and (3.5) for the original
prepared filter if the address build has also narrowed `prepared`.
The fixed `D_w` proves nonemptiness
with valuation `9 + ω(N) + c_w`. The attained minimum is a separate
conclusion about a possibly varying bounded-weight sequence.

## Statements

All declarations are in `ZInQ.Manuscript.RC.AppGCoarse`; file names below
are relative to `ZInQKernel/Contrib/OneProof/RC/AppGCoarse/`.

| Declaration | Statement and depth premise |
| --- | --- |
| `Intrinsic.lean`: `coarse_on_filter` | From uniform (F.3), (3.4), (3.5), visibility (O.8) on `domain i`, and `domain i n → W.prepared n`, there exists one rational `C` with `v₂ a_i(n) ≥ min(M_i, ω(n) − C)` for all `i,n` on that domain. This is `hF5` for `integerDepth_of_min`, `integerDepth_of_witness`, and `integerDepth_of_data`. The existing calculation uses `C = (2A + C_R + C_E − v₂L_*(h_*) + C_per + 2)/2 + C_det`. |
| `Intrinsic.lean`: `fixed_witness_on_filter` | From (O.7) at the same integer coefficients and the fixed `D_w,c_w` of `WitnessValuation` on the same Kummer lifts, plus advancing precision, eventually `D_w ∈ domain i` and `v₂ a_i(D_w) = 9 + ω(N) + c_w < M_i`. This gives `hw` of `integerDepth_of_witness` after the existing equality of the two integer valuations. |
| `Intrinsic.lean`: `minimum_on_filter` | From (F.5) and the preceding fixed-witness inputs, `∃ δ, IsLeast (DepthSet stages M v domain) δ`, with `v_i(n) = v₂ a_i(n)`. Membership gives a bounded-weight sequence of visible indices attaining `δ`; leastness ranges over every such sequence in `domain`. Supplies `hmin` of `integerDepth_of_data`. |
| `Intrinsic.lean`: `depths_on_filter` | Produces (F.5) and one attained `δ` from the preceding arithmetic and witness inputs. Installs that `δ` in the `RCData` passed to `integerDepth_of_data`. For every budget `W,R` with `2 ≤ R`, obtains `IntegerDepth M_i W R δ (fun n => domain i n) a_i` eventually. |
| `Intrinsic.lean`: `restricted_minimum_iff` | For a subfilter of the intrinsic domain, an intrinsic least depth is also the least depth on the subfilter iff it is attained there. The lower bound restricts automatically; attainment is a separate condition. This is a diagnostic for checking a restricted reading, and is not a premise of the depth lemmas. Provenance (c): order reasoning about the tree's `DepthSet`. |
| `Prepared.lean`: `preparedSpec_of_intrinsic` | If `2` is in the original fixed support, the upstream `positivePrepared` filter is positive, squarefree, `1 mod 8`, and prime to that support. The mod-eight assertion uses the unit squareclass at `2`. Supplies `PreparedSpec` to the existing (F.3) producer. |
| `Prepared.lean`: `depths_of_prepared_stages` | For `V = withPreparedStages W S hstar q`, the domain is `positivePrepared S n ∧ stageTest q i n`; the fixed and moving supports come from the chosen source and detecting sequence. Derives (O.8) using the two Kummer comparisons plus (O.7), uses the existing proof of advancing precision, then returns (F.5), the attained minimum, and `IntegerDepth` for every fixed budget on this domain. |

No new structure or named proposition is used as a hypothesis. `onFilter` is
an abbreviation for a data copy changing only `admissible` (provenance (c)); it adds no
condition and leaves the arithmetic, precision and integer coefficients
unchanged. `W`, `S`, `hstar` and `q` are existing data types. The
quantified bounds in (F.3), (3.4), and (3.5) are on rough companions and
native indices, independent of the theta coefficients and depth. The
native and torsion hypotheses control the Kummer lifts; the fixed
witness concerns only one `D_w` and the lifts at that index. None gives
a lower bound or an attained minimum over the full coefficient filter
by itself. `PreparedSpec` supplies the positive, squarefree and local
conditions for (F.3). The copy of `RCData` that sets `δo` is Lean wiring
(provenance (c)); the choice of `δ` before budgets is tex 10190–10213.

## Remaining hypotheses

The following are the premises to instantiate the result for the
project's actual coefficients. The listed producer interfaces describe
what remains before their inputs can be used here; no new printed-form
leaves were added.

| Remaining input | Tex | Owner and smallest required statement |
| --- | --- | --- |
| Original prepared source and its connection to the selected stage | 2016–2029, 2404–2410, 8209–8212, 8246–8259, 8551–8566, 9094–9098, 9471–9483, 10153–10156 | Stage selector and stage identification siblings. Use the actual fixed coefficient support, the same genus partner and detecting sequence, and the same phase-removed integer representatives. If using `LabelData`, compare `oddAdmissible i n` with this exact source domain on all indices of the depth set; agreement merely off the enlarged support is insufficient. No equality with the address-filter `admissible` is needed. The existing sequence supplies the precision and ultrafilter; for a different indexing, `depths_on_filter` takes `Tendsto M stages atTop`. |
| `(F.3)`: bounded partitionable companion on the original preparation | 2295–2401, 10055–10148 | ELLIOT inputs to `Wiring.f3Target_of`: one `A,C_E` and, at each prepared simple zero `h`, a companion `k'` of weight at most `A` with `L_*(hk') ≠ 0` and the upper bound `v₂L_*(hk') ≤ 2ω(h)+2ω(k')+s(hk')+C_E`. The producer needs the normalized even coefficients, the prepared even sources and seeds for the occurring types (`AuxFactorInputs`), their binary realizations, and the even scalar comparison (3.2)/(3.3b), with the existing nonvanishing and rank-zero prints. These are substantial even-source inputs, preceding the odd minimum. `preparedSpec_of_intrinsic` supplies the local preparation clause for the canonical choice. |
| `(3.4)`: same native indices in both height comparisons | 2411–2440, 10172–10178 | ELLIOT same-datum inputs to `Wiring.gz34Target_of_genusOdd`: conductor-one genus and conductor-`|h|` ring-class selections, common normalization and modular parametrization, and their identifications with `j_gen,j_rc,L_*`. The needed output is only the rough companion clause `Gz34CompAt`: one fixed period constant and an error of absolute value at most two for every prepared simple zero and its rough companion. Use the existing Artin factorization, CST and Kolyvagin interfaces. No comparison at the final companion is needed here. |
| `(3.5)`: uniform arithmetic bound at the same companion pairs | 2441–2457, 3987–4047, 4909–5202, 10172–10178 | Missing actual Section 9 realization (large). The smallest incoming statement, `Eq35At`, is one `C_R` for the `A` from (F.3), with `2j_rc(h,k') ≥ 4ω(h)+s(h)+s(hk')−C_R` for every prepared simple zero and admissible companion of weight at most `A`. The existing `eq35Target_of_inputsGG` gives it once the same-class calibration (4.6), actual primitive coordinate/regularity and uniform outer switch models and comparisons are supplied. Those must use the same `j_rc` and Sha lengths as the height comparison. |
| Fixed witness `(O.2)` on the same lifted `λ` | 8246–8260, 8293–8405, 8457–8460, 9391–9402 | ELLIOT selected datum and stage selector: use `OddStagedInstance.witnessValuation` or the finite residue of `WitnessO2At` with `witnessValuation_of_O2`. The one comparison needed here concerns `D_w` and the actual detector row at each chosen place, with `D_w` on the intrinsic filter. A total stage map extended by zero off the witness does not give the all-index theta comparison below. |
| `(O.7)`, native divisibility, and torsion on the full domain | 2522–2538, 9101–9405, 9407–9445 | ELLIOT (O.7), out of scope, on these very coefficients and the `lam` used at `D_w`. The other two inputs require `2^k ∣ lam_i(n)` at a simple zero for `k ≤ M_i` and `k ≤ j_gen(n)−C_native`, and `2^M_i ∣ lam_i(n)` otherwise. `Visibility.visibilityInputs_of_genuine` supplies the latter two using the native index, one multiplier killing native torsion, actual Kummer maps, odd sign and the existing CST/Artin inputs. The remaining all-index point and weight comparisons are part of the actual theta construction; the witness calculation alone cannot supply them. |

Once these are supplied, `δo` for the stage consumer is the output
`δ`. A consumer already carrying a `δo` chosen on a different domain
must identify it with that output before reuse. (O.7), the exact sieve
and squarefree Fourier support, and the stage identification are still
required where the downstream stage consumer asks for them; the present
proof makes no coefficient vanishing claim off the intrinsic filter.

## Known issues

- Source scope error if the old address wiring is reused for the full
  coefficient filter: `Wiring.coarseF5_of_leaves` and `Wiring.exists_oddMinimum`
  use `WData.admissible`, which the address build can narrow.
  `LabelData.oddAdmissible_iff` identifies the two only away from the enlarged
  support. Tex 2026–2029 and 9471–9483 forbid using label tests as an additional
  Fourier sieve. Tex 10153 and 10239 use the original filter.
- Tex 10176 does not define `C_H`. The existing App G arithmetic proof uses
  `C_per + 2` for the fixed period convention and the one-sided error bound
  of (3.4), tex 2436–2440.
- The literal all-types seed instruction in tex 2360–2361 and 10131–10132
  is too broad: a type on which the twist has sign −1 has zero central value,
  hence no even unit by (F.1). `RC/Wiring/AuxFactor3.lean` already records
  this and asks for seeds of the prepared types that can occur in the
  nonvanishing companion construction (tex 10139–10141). The claimed
  (F.3) concerns those companions; no all-types seed hypothesis is used here.
- A comparison only in the theta coefficient ring does not by itself
  identify the chosen integer lift. Use the phase-removed comparison of
  `Odd.ThetaComparison` on those representatives. A valuation test at a
  finite depth depends only on the retained residue below the precision
  (tex 2081–2094); this does not give a stage symbol at all weights.

## Manuscript check

- Tex 2016–2029, 9471–9483 — OK: coefficient support and later stationary label exclusions are separate.
- Tex 2068–2099, 10236–10250 — OK: the depth consumer forces precision strictly above `δ + ω(n)` through the tested weight `W + 1` (for `R ≥ 2`); `coeffSymbol` uses this finite range. The inherited `unitSymbolF7_proof` gives the simple-zero and native index conclusions on the same filter once (O.8) and (F.6) hold.
- Tex 2343–2355, 10055–10076, 10133–10148 — unverified: the actual (F.3) input needs the prepared even sources, seeds and even upper transfer before any odd minimum is chosen.
- Tex 2360–2361, 10131–10132 — error: taken over all types, the instruction includes sign −1 types without an even unit. The needed types are the prepared companion types of tex 10139–10141.
- Tex 2411–2440 — unverified: the two printed height applications require the actual same-parametrization data and native index identifications of (3.4).
- Tex 2441–2457, 3987–4047, 4909–5202 — unverified: (3.5) still needs the actual calibration and uniform arithmetic input at these rough companions.
- Tex 2534–2551 — OK: the fixed visible witness supplies nonemptiness; uniform coarse control and finite cutoff control play distinct roles.
- Tex 8209–8212, 8246–8259 — OK: the original positive squarefree preparation has unit squareclasses at the chosen fixed support, including the genus partner's primes; the test at two gives `1 mod 8`.
- Tex 8358–8405, 8457–8460, 8551–8561 — OK: on the chosen sequence the moving test is the Legendre sign and the precision tends to infinity; the fixed residue comparison concerns the same witness at every stage. The actual detector specialization is supplied by the existing stage construction when its inputs are identified.
- Tex 9101–9389 — unverified: the full weighted comparison (O.7) is beyond this work; only its integer congruence is consumed.
- Tex 9391–9402 — OK: the exact order of the fixed multiplier times the detected Kummer value survives addition of the error at higher precision; retains the named `D_w`.
- Tex 9407–9445 — OK: (O.8) follows from native divisibility at a simple zero and torsion vanishing otherwise, on the same lifts; an index of a torsion point is not used in App G.
- Tex 10172–10179 — gap filled: the companion Sha term cancels and `C_H` is accounted for by `C_per + 2` using tex 2436–2440.
- Tex 10181–10188 — OK: for visible coefficients (O.8) permits the simple-zero argument; at valuation at least `M` the truncation suffices.
- Tex 10190–10207 — OK: bounded-weight attainment and the finite-range contradiction use one ultrafilter on the full filter.
- Tex 10208–10234 — OK: one large-weight cutoff plus (F.6) below it supplies the original all-index budget bound via `integerDepth_of_data`. The downstream divisions have their own (O.7) and support premises.

## Verification

Both files passed individual `lake env lean -j1` checks. The checks ran
sequentially, with host load and available memory checked before each
invocation. All seven `#print axioms` outputs contain only `propext`,
`Classical.choice`, and `Quot.sound`. No upstream source files were edited.
