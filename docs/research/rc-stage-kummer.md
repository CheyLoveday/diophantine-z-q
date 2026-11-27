The shared stage evaluation is reduction at the detector's chosen place followed by its finite detector. On every datum with $(D/\ell_0)=1$ it gives the exact homomorphism premise of `PMGeometry.lamOf_reduction_at`, and at the fixed witness it gives `OddStagedInstance.hev`. With the supplied reference orbit and the two pointwise CM inputs, the constructor fills `O7Actual.DatumAt.reduce`; the existing orbit comparison then supplies the comparison core for the same map. This does not construct the CM or orbit data and does not close (O.7) unconditionally.

## The place and the row

A stage uses the absolute prime of `selectedFrobenius q i` that constructs the detector. To identify the datum fields in that absolute closure, fix an isomorphism from it to the algebraic numbers in ℂ extending the identification of the two embeddings of the witness field. The other embeddings are the inverse of that one isomorphism composed with each datum's recorded complex embedding. Use the original `w.emb` at the witness, where the new construction gives exactly that embedding. This fixes one realization of the reference Heegner datum and its Artin translates before taking any reduction. Its place is the contraction of the detector's absolute prime to that realization (tex 9265); there is no independently chosen prime of the ring class field. The extension of the witness identification need not be canonical; it is fixed once for the whole family, and both pointwise CM inputs use the resulting place. The prime below it in the quadratic field is the corresponding contraction, and the prime below that in ℤ is $(\ell_0)$. The quadratic prime above $(\ell_0)$ is unique by inertness. The stage's negative sign on $h_*$ and the positive sign on $D$ give the inert sign on the datum discriminant. The existing conductor-one reduction uses the resulting residue field of cardinality $\ell_0^2$.

The detector uses the witness twist's Tate row composed with the inverse of its torsion specialization. The split twist in `actualLocalStage` is equivariant for the selected Frobenius because it fixes the exact square root (`stage_root_fixed`). Its torsion specialization is the original curve's specialization composed with that twist. The equality in `selectedEvaluation_lam` identifies the two homomorphisms on **all** quadratic residue points, by the definition of the Kummer map and of that same inverse specialization. This is the split twist version of the untwisted calculation `stageMap_eq_lam_comp`; the latter takes an already transported row on the original Tate module. `detector_lam` reuses `selectedEvaluationOn_lam`, the underlying theorem of `detectorAt_lam`, with the same detector and stage transport. The witness proof uses the coincident reductions and these actual rows; it does not identify rows just from their value on the witness point. Outside the moving split support the shared family has zero entries solely to inhabit the total existing interface; (O.7) never reads those entries.

The equality of homomorphisms holds for any supplied datum on the split support. The selector extension preserves the selected witness and fills admissible holes subject to the selector lane's one algebraic realization premise. If this extension is installed in the genus record, its total `jgen` function must be recomputed: the original record demanded a global equation even off prepared simple zeros. The new wrapper changes `selG`, `hselG`, `W.jgen` and `hjg` together; at every prepared simple zero the old and new indices coincide. The other stage data, including `hstages`, have the same values. The odd record has `ev := s.ev`, a proved `hev`, and `T` and `hcore` built for the same family when using `toOddStagedInstanceOfReference`. The supplied genus inputs and fixed witness data are kept.

## Statements and consumers

Names are relative to `ZInQ.Manuscript.RC.StageKummer`. Here $v_i$ is the detector's absolute place, $d_i$ is its selected evaluation, and $r_{i,t}$ is the reduction at the contraction of $v_i$ to the field of $t$.

| Declaration | Statement and consumer |
| --- | --- |
| `witnessEmbeddings_at_witness`, `anchoredEmbeddings_complex` | The simultaneous realizations send the witness field by `w.emb`; after the common complex identification, the anchored embedding of every datum is its recorded complex embedding. Supplies the field realization. |
| `datumPlace_under`, `datumPlace_liesOver` | The contracted prime lies above $(\ell_0)$ and above the contraction of the same absolute prime to the quadratic field. Supplies compatibility of places. |
| `datumReduction_eq`, `datumReduction_witness` | `datumReduction` is the reduction used in the existing stage evaluation; at the witness it is `actualRingClassRed`. Supplies the geometric component of both `hev` equalities. |
| `ev_eq_comp`, `evActual_eq_comp`, `hev_at` | At every moving split datum, the stage map equals $\lambda_{d_i}\circ r_{i,t}$, first on the integral presentation and then in the transported wiring and comparison. The transport normalizes the additive group instances explicitly. Supplies `PMGeometry.lamOf_reduction_at.hev`. |
| `witness_detector`, `evActual_witness`, `Setup.hev` | The witness map equals $\lambda_{d_i}\circ r_{i,w}$; hence the shared entry is exactly `actualStageMapOn`. Supplies `OddStagedInstance.hev`. |
| `evActual_off_support` | The total family is zero when the moving split test fails. |
| `selectorOnModel_some`, `lamOf_onModel` | Transport preserves selection of a row and its integer read. Supplies the selector equation and equality of the right-hand sides across the integral presentation. |
| `detector_lam` | The selected `PM.lam` is the finite evaluation component of `actualForStages` on the whole quadratic residue group, in the transport's heterogeneous form. |
| `reference_reduction` | $2^{M_i}\mid\sum_c\chi_F(c)u(z_c)-\operatorname{lamOf}(i,D)$, from the Artin match, $r_c=C(z_c)$ and $\pi(r_c)=r_{i,t}(\sigma_c y)$ at the reference tuple. Supplies `DatumAt.reduce`. |
| `stageGood`, `Setup.stageTest_of_admissible` | The stage prime is prime to the discriminant of the integral model, and admissibility implies the moving split test. Supplies the geometric good reduction and support proofs. |
| `stage_mod_four` | The chosen stage prime is $3$ modulo $4$, by its Chebotarev congruence at precision at least two. Supplies the explicit level order. |
| `referenceStage`, `datumAt` | The stage takes its geometry from the given coarse model and its integer weights are the least lifts of the selected detector applied to $L\pi$. The datum record has its `reduce` field filled by `reference_reduction`. |
| `positiveLevel`, `selected_of_admissible` | The witness form forces positive level; the extended selector selects a datum at every admissible pair, including the witness. Supplies the selector input for comparison. |
| `extendedIndex_at_simpleZero` | Installing the extended selector preserves the old genus index at all prepared simple zeros. Supplies the index compatibility for uses of (3.4). |
| `extendedSetup_ev` | Installing the selector leaves the underlying family of homomorphisms unchanged. |
| `phaseAt_eq` | The phase on the admissible domain of `ThetaSide` is the phase of its reference tuple. |
| `Setup.toOddStagedInstance`, `toOddStagedInstanceOfReference` | The first fills `ev` and `hev` and consumes a comparison core indexed by this map. The second builds that core from the reference records and the existing orbit calculation, without a comparison-core premise. Both are accepted `OddStagedInstance` records. |

## Remaining hypotheses

These obligations are strictly smaller than the desired comparison in scope. None asserts equality of a theta coefficient with a genus evaluation, and each can be formulated before using that equality. This does not mean the final congruence logically implies every premise: cancellation in a sum can hide failure of a summand.

| Owner | Exact input and why it is independent of (O.7) |
| --- | --- |
| Appendix F stage construction and existing genus wiring | `Setup` uses the common genus instance and multiplier, its prepared selected witness and exact rational twist with embedding, the division tower and invariant row with fixed cocycle value, the actual detecting sequence and `StagesFrom`. The row invariance `hb` is present in `exists_detector_stages` and is absent from the older `OddStagedInstance` interface; it compares actions on the Tate module of one elliptic curve. Neither the witness inputs nor the arithmetic and precision of the stage sequence mention a theta coefficient. `MultiplierKillsNativeTorsion` and `AdmissibleOddSign` remain the existing genus/visibility inputs to the final wiring. |
| `rc-stage-selector`, manuscript construction | `MissingParamValues` is `PreparedParamValue` at the chosen form for each admissible nonwitness hole, using the existing genus partner and prepared filter. It is just the algebraic realization of one analytic value. If a selected row is already supplied, the reference theorem needs only its selection equation. |
| `pm-adelic-join`, existing PM geometry, and `rc-theta-join` | The explicit level order needs the supplied adelic comparison and one coarse model `GeometricInput` with its classes and specialized parametrization and operator identities. The actual `PMLocal` supplies the integral Schwartz function and norm weights on that order at $m=|h_*|$. These are the independent geometric and local objects used to define the summands. |
| `pm-adelic-join` / Cornut–Jetchev as used by the manuscript | The actual reduction $r_c$ of each enhanced reference conjugate is the coarse class $C(z_c)$ in the chosen special fibre (tex 9265–9279). The current abstract print acts on an abstract reference orbit; realizing those classes as geometric reductions remains a pointwise input. No detector occurs in this input. |
| `pm-adelic-join`, manuscript specialization | $\pi(r_c)=r_{i,t}(\sigma_c y)$ at each of those conjugates (tex 8476–8479 and 9283–9291). This is commutation of two maps on a finite set of individual points. It asserts no orbit sum. |
| `rc-o7-orbits` and `rc-o7-character` | The remaining `IntegralSupport` and `OrbitFibers` give half-integral optimal embeddings, the quadratic integral basis and the orientation/Picard parametrization. The Artin equivalence labels its class index by datum automorphisms and `ArtinMatch` identifies `weights.character` with the datum character on that index. These are separate order, orbit and character statements, without the finite detector. |
| `rc-o7-orbits`, `rc-o7-character`, and adelic/local weight transport | `TorusWeights`, the reference tuple, and `Normalizers` provide the two weight factors, orbit reindexings, class projections, cusp annihilation and the edge signs. These are identities on individual terms and local moves. The existing assembly proves the orientation congruences and stabilizer count; no additional sum equality is an input. |
| Actual theta coefficient wiring | If supplying the independently indexed $W.a_\theta$, `ha` says it represents the phase-removed raw coefficient of the actual theta stage. This only identifies two readings of the theta side. Contraction at two is `O7Actual.ring_two` in the actual coefficient ring; the generic assembly takes that ring property explicitly. Neither input compares the coefficient to an elliptic curve point. |

Primality is the stage's `q.stage i` field. The reduced curve is elliptic by `StageIdent.selectedCurveOn_elliptic`, and the level is positive by `positiveLevel` and `EcurveZ_baseChange`. These routine interface proofs need no further inputs. The final assembly is conditional on the data in the table at every admissible row.
The pointwise gap left here has the size of the two finite families of equations in the two CM rows. A proof constructing the reductions and the specialized modular parametrization would be substantially larger; the present lane only needs their values at the reference conjugates. No print or new leaf has been added.

## Known issues

- Inherited citation scope error at tex 8468–8474: the Jetchev–Kane citation does not cover level one, as recorded in the existing source audit and in `docs/research/pm-adelic-join.md`. This lane does not apply it at level one.
- The manuscript switches Frobenius notation: the map called $F^2$ at tex 8382 is called $F$ at tex 8444. Both mean arithmetic Frobenius over the quadratic residue field; the Lean detector consistently squares prime-field Frobenius.
- The old selector's default zero does not construct a datum, and its globally specified `jgen` cannot simply be reused after filling holes. The optional selector adapter updates that index and proves the precise agreement needed on the old prepared simple zeros.
- Cornut–Jetchev's cited external locators are UNVERIFIED here. The existing print and its geometric scope are unchanged.

## Manuscript check

- Tex 2460–2493, 8370–8377, 8399–8405 — OK: use the fixed witness and its actual sequence with one precision and one place per stage.
- Tex 8374, 8437 — OK: the Chebotarev congruence at precision at least two gives $\ell_0 \equiv 3 \pmod 4$.
- Tex 8378–8391, 8439–8456 — OK: use the finite Kummer map and the invariant row, with inverse torsion specialization on the same residue group.
- Tex 8392–8398, 8457–8459 — gap filled (c): the shared family's whole witness entry matches the split twist map in the wiring, so its existing cocycle proof applies.
- Tex 8468–8474 — error: the cited scope does not include level one.
- Tex 8476–8479 — unverified: commutation of the actual specialized parametrization with reduction stays a pointwise input.
- Tex 9205–9209 — OK: the product of the Legendre symbols yields the inert discriminant.
- Tex 9265 — gap filled (c): use the common absolute place and contract via embeddings compatible with the witness and the given complex data.
- Tex 9266–9279 — unverified: identifying the actual enhanced CM reductions with the reference adelic classes is the first pointwise input.
- Tex 9283–9291 — gap filled (c): supply the datumwise equality of stage maps and use the existing additive sum lemma with the two CM inputs.
- Tex 2522–2533, 9105–9113 — OK: the same stage map reads the scaled genus point on the moving split support; the comparison does not read it off that support.
- Tex 9272–9277, 9439–9443 — unverified at a previously empty admissible row until the chosen form's algebraic value is provided; the existing selector builds the row from that value.

## Validation

All six deliverable files (`Actual.lean`, `Wiring.lean`, `Selector.lean`, `Transport.lean`, `Reference.lean`, and `Assemble.lean`) passed `lake env lean` with Lean 4.35.0, one run at a time. One final assembly start was held above the development server's load limit and was retried after load fell.

The scratch audit in `scratch/rc-stage-kummer/Axioms.lean` reported exactly `propext, Classical.choice, Quot.sound` for all 29 checked declarations from the first five files, including all their theorems and the map and record constructors. `scratch/rc-stage-kummer/AssemblyAxioms.lean` reported the same three axioms for both `phaseAt_eq` and `toOddStagedInstanceOfReference`. No other axioms, new printed leaves, or `sorry` occur in the new proofs.
