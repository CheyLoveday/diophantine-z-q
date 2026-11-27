# Appendix F: genus selections at admissible parameters

Scoped stop: the remaining input is the conductor-one algebraic realization of the
analytic parametrization value at one chosen Heegner form for each empty
admissible nonwitness entry. The prepared filter supplies the quadratic field,
its discriminant, the primitive Heegner form, and the genus character. With the
algebraic value supplied, `extendSelG_isSome_of_admissible` closes the selection
row of `RC/StageMap` without a simple-zero assumption. The extended selector
preserves every existing entry, including the exact witness.

`Forms.lean`, `Character.lean` and `Selector.lean` each compile with
`lake env lean -j1`. The audits of all 20 theorems and of the datum and
selector definitions list only `propext`, `Classical.choice` and `Quot.sound`.

In the base, `GenusOddInstance.selG` supplies the witness datum to
`OddStagedInstance` and `RC/WitnessSpec`. The witness code uses the datum to
construct and reduce the exact twist point; it does not construct the
Heegner form or prove the existence of its algebraic parametrization value.
The height identity in `CloudB3RC53/Prints/CST.lean` takes that value as a
hypothesis. No height identity or new print is used here.

The prepared parameter `D` is positive. It is `D*hstar` that is the negative
fundamental discriminant. Taking the product of the two unit-square conditions
gives the Heegner splitting condition at each prime of the level; the condition
at two gives the congruence modulo eight. Squarefreeness follows from
coprimality. For the form take `A=N`, lift a square root `B` modulo `4N`,
and take `C=(B²-D*hstar)/(4N)`. A common divisor of the three coefficients
would have its square divide the discriminant. The field is
`ℚ(√(D*hstar))`, and conductor one gives the maximal order.

The character is the action on `√hstar` in the Hilbert class field. At each
finite prime use whichever of `D` and `hstar` is a unit to see that inertia
fixes the half-integral generator. Local reciprocity at finite units and at
complex places gives admissibility of the trivial modulus. Odd-prime Frobenius
on the root gives the Jacobi symbol of the ideal norm. At two the half-integral
root has idempotent reduction since `hstar ≡ 1 (mod 8)`, so Frobenius fixes it
and the norm symbol is one. When `D=1`, the root already lies in the base field
and the action is trivial. Conductor-one primitivity is vacuous in the existing
definition. The implementation of these steps and the selector packaging are
on-the-spot (c).

## Statements and consumers

All declarations are under `ZInQ.Manuscript.RC.StageSelector`. Paths in this
table are relative to `ZInQKernel/Contrib/OneProof/RC/StageSelector/`.

| Declaration | Statement |
| --- | --- |
| `Forms.lean`: `prepared_discriminant` | `Prepared E hstar D` and `GenusPartner E hstar` give `D*hstar < 0`, squarefreeness, and `SquareAt p (D*hstar)` at all prime divisors of `2*newformLevel E`. |
| `Forms.lean`: `qsqrt_discr` | For negative squarefree `d ≡ 1 (mod 4)`, the chosen quadratic field has discriminant `d`. |
| `Forms.lean`: `exists_heegnerForm` | For positive level `N`, squarefree `d` and the local unit squares at `2N`, there exist `B C` with `IsHeegnerForm N d N B C`. |
| `Character.lean`: `admissible_one_of_unramified` (private) | A finite abelian extension of a totally complex number field, unramified at every finite prime, admits the trivial modulus. |
| `Character.lean`: `halfRoot_integral`, `fixes_root_of_congruent_half` (private) | If `s²=d` and `d ≡ 1 (mod 4)`, `(1+s)/2` is integral. An automorphism fixing its reduction at an ideal avoiding `d` fixes `s`. |
| `Character.lean`: `conductorOrder_maximal`, `ringClassField_one` (private) | Conductor one gives the maximal order and that order's ring class field is the Hilbert class field. |
| `Character.lean`: `sqrt_mem_conductorOne` | If a totally complex field contains a root of `D*d` for coprime integers `D,d ≡ 1 (mod 4)`, its conductor-one ring class field contains a root of `d`. |
| `Character.lean`: `frob_fixes_root_at_two` (private) | Frobenius above two fixes a root of `d ≡ 1 (mod 8)`. |
| `Character.lean`: `exists_genusCharacter` | A root of `d ≡ 1 (mod 8)` in the conductor-one class field gives a character satisfying `IsQuadRingClassChar K 1 d χ`. |
| `Selector.lean`: `not_isSquare_prepared`, `level_pos_of_witness`, `preparedAt` (private) | The prepared discriminant is a rational nonsquare; a supplied witness form forces positive level; a parameter admissible at any stage is prepared via the existing filter bridges. |
| `Selector.lean`: `extendSelG_eq_some`, `extendSelG_witness` | Every old `some t` remains exactly `some t`; in particular `selG Dw = some dat` stays true. |
| `Selector.lean`: `extendSelG_isSome_of_admissible` | Every `W.admissible θ D` with `D ≠ Dw` has some datum under the extension. |
| `Selector.lean`: `exists_selected_of_admissible` | With the existing witness equation, each admissible pair has `∃ t, extendSelG … D = some t`. Pass that equality and the admissibility proof to `StageMap.lamOf_admissible` with the extended selector. |
| `Selector.lean`: `jgen_extendSelG_at_simpleZero` | At a prepared simple zero the extended index reading equals `W.jgen D`, as required by (3.4). |
| `Selector.lean`: `preparedGlue_of_withStages` | The actual stage construction already gives the admissibility-to-preparation bridge. |

The definition `datumOfPrepared` assembles the proved field, form and character
with the realization hypothesis into the same `HeegnerDatum` type used at the
witness. `extendSelG` uses it at a parameter only if the old selector is empty,
the parameter is admissible at some stage, and it is different from `Dw`.
There is one selected datum per parameter, independent of the stage.

## Remaining hypotheses and interfaces

| Input | Manuscript | Owner and size |
| --- | --- | --- |
| `PreparedParamValue E f Lat κ hN hgp hp` for each `D` admissible somewhere with `D ≠ Dw` and `I.selG D = none`: for the fixed `K=ℚ(√(D*hstar))`, `H=H₁(K)`, `A=N` and the chosen `B`, obtain `∃ ι : H →ₐ[ℚ] ℂ, ∃ y : E(H), ι(y) = phiAn E f Lat κ (cmPoint A B (D*hstar))`. | 8209–8217, 9272–9285, 9347–9350 | Missing theory, large: the canonical model of `X₀(N)`, the field of definition of the CM point with its level structure, and compatibility of the rational parametrization with the analytic `phiAn` at the chosen scale. This is a single value assertion on an already constructed field and form. It supplies only `ι,y,hy`, no character, primitivity, selector or stage condition. It is strictly smaller than supplying a full datum. |
| `GenusOddInstance W` (uses its fixed `f,Lat,κ`, genus partner, prepared-filter map and original genus selections; the index statement also uses its `hselG,hjg`). `PreparedGlue W` is obtained from `StagesFrom.withStages_eq` for actual stages. | 2403–2416, 8209–8217, 8246–8259, 9105–9108 | Existing wiring and stage construction. The selector requires no analytic rank evidence for a new entry. |
| Original witness datum and its selection equation for the witness conclusion; actual stage-map consumers still use their fixed witness, row, precision and place data. | 2460–2498, 8247–8259, 8340–8405 | Existing witness and stage-map construction. The original datum gives positive level already. Its entry, including its fields and complex realization, is kept. |
| Match the reference `x_D` and the parametrization of the supersingular pairs to the newly selected datum at the same place, and prove the comparison and (O.7). | 2522–2530, 9105–9113, 9265–9295 | ELLIOT comparison input and sibling lanes for stage identification, theta and adelic level structures; outside this task. |

## Known issues

- The source's analytic `phiAn` and the CST print's hypothesis about its
  algebraic value do not supply CM descent. Merely knowing that a value is
  algebraic over `ℚ` would also be insufficient: the reduction needs the
  conductor-one ring class field. The existing CST height statement is used
  nowhere in this construction. The related
  `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean` provides an interface for CM reciprocity
  on rational modular functions, with a consumer for the level-32 model. It
  does not prove the field of definition of this `phiAn` value.
- The old `W.jgen = jgenOf … I.selG` is an equality of total functions; it
  cannot automatically be transferred to the extended selector at formerly
  empty parameters. At prepared simple zeros the old entries remain and the
  equality is proved there. No rank-one index of a torsion point is used.
- Choices of forms and embeddings have to agree with the reference point
  used by the geometric comparison. The extension only supplies the point and
  its selection equation; it does not replace an existing `OddModels.hcore`
  or infer a theta coefficient at a newly filled entry.
- The base's support convention at the primes of `hstar` is recorded in
  `RC/Skeleton/Steps.lean`; the selector uses the given prepared/admissible
  bridge and does not change that support.
- No manuscript or cited-source error was found in the steps used here.
  External references for the canonical model and CM descent were not
  independently checked.

## Manuscript check

- 2404–2416, 8209–8212 — OK: the positive prepared parameter and negative genus partner give the imaginary field of odd fundamental discriminant and the level splitting conditions.
- 8209–8217 — gap filled: lift local square roots to a root modulo `4N` and construct a primitive form of precisely that discriminant and level.
- 8213–8217, 8261–8266 — gap filled: put the genus square root in the Hilbert class field and construct the quadratic character with the stated norm values, including at two and for `D=1`.
- 8213–8217, 9272–9285, 9347–9350 — unverified: algebraic realization of the chosen reference parametrization value over the conductor-one field is the scoped stop.
- 2460–2498, 8247–8259 — OK: use the fixed existing witness and keep its entry.
- 2522–2530, 9105–9113 — OK for the geometric argument of the comparison: at any admissible pair use the selected, scaled genus point at that stage, with no simple-zero condition on selection.
- 9265–9291 — unverified for the geometric-to-theta comparison: identifying the reference point and its images on the two sides is outside this task.
- 9417–9419, 9439–9443 — OK for the selector's domain: a non-simple-zero parameter still needs the genus point, even though its rank-one index is unused.
