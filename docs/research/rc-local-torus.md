# The local inputs to the Picard fibers of (O.7)

Both remaining inputs of `picardFibers_of_local` are proved: `localTorusChart` gives `∀ p, Nonempty (LocalTorusChart (ActualOrder s) ι₀ x₀ α p)`, and `hasLocalRealizations` gives `∀ t, HasLocalRealizations s α t`. The [assembly](../../ZInQKernel/Contrib/OneProof/RC/LocalTorus/Assembly.lean) supplies `PicardFibers` and `OrbitFibers`. For each tuple `t` it gives an equivalence
`ClassGroup (𝓞 F) ≃ {P : OrbitSet s.visibility (index s D) // orientation s H P = t}`.
It takes the actual stage, the full filter (including the fixed-partner detecting symbol), the quadratic integral basis, the chosen rational embedding, and the support bridge. There are no remaining placewise hypotheses.

The reference quantities are `d = D · (−s.weights.m)`, `x₀ = ι₀(√d)` and `α = ι₀((1 + √d)/2)`. In the split ambient algebra, two nonscalar affine generators with characteristic polynomial `T² − T + c` have the same companion form in cyclic bases. The companion matrix itself is integral at exponent zero. At positive level the two ordered diagonal branches give the two bits; the affine root has unit separation from its complement, including at two. In the division algebra the two square roots give opposite nonzero residues. The elementary ambient intertwiner is the sum of the two roots when that sum is nonzero, and a nonzero commutator with the reference root otherwise. This is the required local form of Skolem–Noether. The choice of intertwiners is on-the-spot (c).

For the torus, contract places to the rational prime and extend the rational scalar map. CRT makes the integer ring dense in the product of the completed integer rings. The integral affine basis has compact image, so that image is the whole product. For injectivity, divisibility by `p` at its places implies global divisibility by `p` on the ring of integers. Thus two integral coefficients with image in `p` times the product of integer rings are both divisible by `p`. Scaling arbitrary coefficients reduces the coefficient test to this integral test. Inverting `p` identifies the ambient quadratic algebra with the product of completed fields. The quaternion centralizer is the span of one and the trace-zero root. After conjugation, integrality of the affine generator gives the inclusion of its integral span in the order. Finiteness of the completed order gives the converse by integrality in each valuation ring. Taking units applies this intersection to a value and its inverse. This completion and intersection argument is on-the-spot (c).

The chart uses the same integral coefficient test at the special places. At two the generator is already the affine one, and the simple roots from the splitting filter are used when two divides the level. At a positive-level prime the order chart uses exponent `N.factorization p`; both diagonal matrices satisfy its divisibility condition, and their labels differ modulo that full exponent. At the detecting prime the two Legendre symbols imply that the rational local quadratic algebra is a field. Its affine generators are made integral inside the division order by dividing by the unit two. At the other primes the quaternion order is split and maximal; the CRT comparison retains the actual places above the rational prime whether the quadratic source splits, is inert, or ramifies.

## Declaration statements

In this table, $a_0=(1+\sqrt d)/2$, $A_p=\prod_{v\mid p}F_v$, and $I_p=\prod_{v\mid p}\mathcal O_v$. All statements are on the actual prime and completion types.

| Declaration | Statement and use |
| --- | --- |
| `local_centralizer_span` | A quaternion commuting with a nonzero trace-zero quaternion $x$ is its scalar part plus a scalar multiple of $x$. Torus image. |
| `split_ambient_conj` | Nonscalar trace-one matrices of the same determinant are conjugate by an ambient unit. Split realization. |
| `division_ambient_conj` | In a division algebra two roots of a common scalar square are ambient-unit conjugate if the first is noncentral. Detecting realization. |
| `under_eq`, `liesOver`, `finitePlacesAbove`, `primesEquiv_eq` | The rational contraction of every indexed place is the ideal over $p$; the index is finite; the rational place equivalence agrees with this indexing. Torus. |
| `dvd_of_local_valuation`, `valuation_prime_lt_one` | If $v(a)\le v(p)$ at all places over $p$, then $p\mid a$ in the global integer ring. At each indexed place $v(p)<1$. Torus. |
| `completedScalar_ratCast`, `continuous_completedScalar`, `completedScalar_mem` | The scalar map $\mathbf Q_p\to F_v$ extends the rational scalar map continuously and sends $\mathbf Z_p$ into $\mathcal O_v$. Torus. |
| `denseRange_diagonal_integers` | The diagonal map $\mathcal O_F\to I_p$ has dense range. Torus. |
| `affine_relation`, `generator_linear_independent`, `generator_rational_span` | If $d=1-4c$, $a_0^2=a_0-c$; $1,a_0$ are independent over $\mathbf Q$ and span $F$. Torus. |
| `affineEval_rat`, `affineEval_int`, `localInteg_eval`, `nat_scalar` | Affine evaluation agrees with the diagonal on rational and integer coefficients, maps integral coefficients into $I_p$, and its scalar map preserves natural casts. Torus. |
| `choose_residue`, `coefficients_dvd` | Every $p$-adic integer has an integer representative modulo $p$. If integral affine coefficients give a value in $p I_p$, both coefficients are divisible by $p$. Torus. |
| `affineEval_mem_iff`, `integral_eval_surjective` | An affine value is in $I_p$ exactly when both coefficients are integral, and every element of $I_p$ has such coefficients. Torus. |
| `eval_surjective`, `eval_injective`, `completedQuadratic`, `completedQuadratic_apply` | Affine evaluation on $\mathbf Q_p^2$ is bijective; with the quadratic multiplication it is a ring equivalence onto $A_p$ given by that same evaluation. Torus. |
| `local_reference_root`, `split_reference` | The completed reference root is nonzero, trace zero and squares to $d$; the affine generator in the split chart is nonscalar, of trace one and determinant $c$. Both inputs. |
| `eq_of_two_distinct_bits`, `conj_map_equiv` | Two bits distinct from the same bit are equal; conjugation by a transported unit commutes with a ring isomorphism. Realization. |
| `affine_cancel`, `split_of_model`, `levelPrime_injective` | Equality after applying $2X-1$ cancels over the local field; a split integral model of the given trace and determinant is an ambient conjugate; a level place has a unique index. Realization. |
| `division_order_eq`, `division_chart_eq`, `transported_chart_val`, `division_chart_val` | The actual completion is the explicit detecting-prime order; its chart is the transported division chart and agrees with the ambient chart on values. Realization. |
| `noncentral_of_nonsquare` | A root of a nonsquare is noncentral when scalars exhaust the center. Realization. |
| `division_root_for_bit`, `division_affine_model`, `division_square_val` | Choose a root with the requested residue bit, solve $2V-1=W$ in the division order, and read the scalar square in the ambient division algebra. Realization. |
| `realize_split`, `realize_division`, `hasLocalRealizations` | At a split place or the detecting place, respectively, an ambient unit carries the reference generator into the actual order with the prescribed label. Together they give `∀ t, HasLocalRealizations s α t`. |
| `local_order_finite`, `ambientEval_apply`, `ambientEval_injective`, `ambientEval_image` | The completed order is a finite module; the quadratic algebra evaluates injectively at the reference affine generator, and its image is the full centralizer. Torus. |
| `embedProduct_diagonal`, `conjugated_integral_iff`, `localTorusChart` | The product embedding is diagonal on $F$; if $z^{-1}\alpha z\in R_p$, its conjugated image belongs to $R_p$ exactly on $I_p$. On units this gives `∀ p, Nonempty (LocalTorusChart (ActualOrder s) ι₀ x₀ α p)`. |
| `picardFibers`, `orbitFibers` | Apply the two existing assembly maps to these inputs with `ClassGroup (𝓞 F)`. |

## Verification

All eight new Lean modules compiled individually with `lake env lean`, with one Lean process at a time. The [axiom check](../../scratch/rc-local-torus/Axioms.lean) ran `#print axioms` on every new theorem and definition constant, including private helpers and generated equations. The [output](../../scratch/rc-local-torus/axioms.txt) lists 97 theorem constants and 18 definition constants. The two local inputs and both assembly definitions use only `propext`, `Classical.choice`, and `Quot.sound`. Every other audited declaration uses a subset of those three. No new print was added.

## Hypotheses and owners

| Owner | Hypothesis | Scope relative to (O.7) |
| --- | --- | --- |
| Manuscript filter | `AdmissibleD s D`, tex 9105–9108 and 9121–9134, including splitting at every prime of `2N`; the fixed-partner symbol `legendreSym s.ell (−s.weights.m) = −1`, tex 8372 and 9205–9208. | Conditions on rational arithmetic that do not concern orbits or theta coefficients. The fixed-partner symbol is separate from `AdmissibleD` in the base interface. |
| Actual stage and support bridge | `StageAt` with the actual `PMLocal` and `SupportBridge s D`, tex 9123–9134. | The bridge is a pointwise membership test on the norm sphere; it neither counts orbits nor identifies their weights. |
| `rc-o7-character` | `QuadraticBasis F (disc s D)`. | A presentation of the quadratic field and its integer basis, without a class-group action or a character claim. |
| Existing Voight GLUE | The chosen rational `ι₀` from `O7Orbits.exists_reference_embedding`, tex 9150–9154. | A rational embedding with no specified integral realization or orientation. Its existence citation is outside this lane. |
| Torus weights, normalizers and reference reduction | `DatumAt.weights`, `DatumAt.moves`, `DatumAt.reference`, `DatumAt.reduce`; the respective lanes, with `rc-o7-assemble` joining the datum. | These give individual weights and normalizer moves or evaluate one selected tuple; the theta congruence needs all of them. |

## Known issues

- The existing Voight implication at tex 9154 remains GLUE (printed wording UNVERIFIED). No new print is introduced.
- The bare norm character issue recorded by `rc-o7-orbits` concerns descent of a weighted summand and is outside the Picard comparison.
- The full splitting filter rules out the earlier `D = N = 193` example. At two we use the affine equation; a division by two is allowed only in the rational local algebra or at the odd detecting place.
- No new error in the manuscript has been identified.

## Manuscript check

- 9105–9108 and 9121–9134 — OK: retain the full filter and the integral affine generator.
- 9136–9139 — gap filled: the integral companion provides a representative even at a discriminant prime; ambient conjugacy connects it to the chosen reference.
- 9140–9146 — gap filled: the integral affine roots give opposite bits, also at two by lifting a simple root of the affine equation.
- 9146–9148 — gap filled: use the two reduced square roots in the actual division model.
- 9150–9154 — unverified: the cited rational embedding is the existing Voight GLUE.
- 9155–9156 — gap filled: construct an ambient conjugating unit at each place for the chosen integral model, before applying the base patch.
- 9157–9164 — OK: use the existing representative and rational centralizer comparisons.
- 9164–9165 — gap filled: complete the affine basis, apply CRT at all places over each rational prime, and check the conjugated integral unit intersection.
- 9165–9169 — OK: use the existing idele valuation quotient and the transport to actual orientation fibers.
