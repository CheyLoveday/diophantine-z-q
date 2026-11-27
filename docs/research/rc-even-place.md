# One coefficient place for the even source

**Scoped stop: the coefficient-place construction and the depth-zero singleton divisions are proved on the existing arithmetic interfaces. The actual App E producer and its two consumer instantiations are not connected in Lean.** The checked construction takes a common bound on the two-power character orders and chooses one prime above two in a cyclotomic subfield of `ℂ`. The two-adic field and ring of integers are the completion at this prime. The characteristic-zero subring of `ℂ` is the image of the valuation ring before completion, at the very same prime. One shift by `-δ` makes all coefficients of a source integral. At depth zero the ordinary squarefree lower bound and the shell recurrence imply integrality of the exact `KSplit.Bp` and `KSplit.Hp` at every index, before assuming there is no unit seed.

The remaining binding is small source-specific Lean work once the imports are available; it does not require a new analytic theorem. The worktree initially lacked 1,997 project import artifacts in the combined consumer closure, including the dependency trees of `AppE.Assembly`, `EvenBudget.Place`, and `KSplitSeed.Seed`. The files here were checked with the available imports and a small sequential dependency build. No weight-two analytic realization, constituent construction, old-unit comparison, or modulus choice is made here.

The manuscript has two App E sources (tex 10288–10318). The budget uses the negative-sign form for the original curve at a fixed total type; the singleton seed uses the normalized positive-sign form for the companion twist. They need not have identical coefficients or phases. When both are needed together, the common-order-bound construction takes the maximum of the four character exponents and works at a single prime for both. No choice depends on a tested `U` or `p`.

## Checked statements

Names are under `ZInQ.Manuscript.RC.EvenPlace`. `F` is the embedded number field; `V : Place F` is the choice of prime. `V.LocalField` and `V.LocalIntegers` are the two completed types and `V.complexIntegers` is the precompletion ring in `ℂ`.

| Lean result | Statement and consumer input |
| --- | --- |
| `phaseField_mem` | If $z^{2^f}=1$ and $f\le e$, then $z\in\operatorname{PhaseField}(e)$. The field is a number field by the existing `LocalWeights.characterField_numberField` construction. This supplies the archimedean field for `SourceAtPlace.K₀`. |
| `place_exists` | Every such embedded number field has a `Place F`, a height-one prime containing two. |
| `Place.mem_complexIntegers_iff` | For $x\in F$, its complex image lies in `V.complexIntegers` iff its completed image lies in the integers at that place. This identifies the two realizations used by the consumers. |
| `Place.root_mem_complexIntegers` | A value in $F$ with $z^m=1$, $m>0$, is in the complex coefficient ring. |
| `Place.odd_inv_mem`, `Place.half_not_mem` | Every inverse of an odd natural belongs to `V.complexIntegers`; the inverse of two does not. These give `hodd` and `hhalf`. |
| `Place.liesOver_two` (private) | The chosen prime lies over $(2)\subseteq\mathbb Z$. |
| `Place.continuous_padic`, `Place.padic_mem` (private) | The map from `ℚ_[2]` to the completion is continuous and takes `ℤ_[2]` into the integers there. |
| `Place.padic_agree` | The completed integer inclusion composed with `V.padicInt` equals `V.padic` on `ℤ_[2]`. Gives the three p-adic fields of `SourceAtPlace` together with their definitions. |
| `character_value_pow` | A Dirichlet character with $\chi^{2^e}=1$ satisfies $\chi(x)^{2^e}=1$ at every unit residue. |
| `Place.character_mem`, `common_place_for_characters` | All values, including zero at nonunits, lie in the ring at one common prime for a family whose character exponents share a bound. These give `hηO`, and `hz` when $z_D=\eta(\operatorname{sqrtRatio}(N,D_0,D))$ as in the existing producer. Both $\psi$ and $\eta$ are covered. |
| `Place.fieldLift_complex`, `Place.localLift_eq`, `Place.localLift_pow` | The lifts recover the input complex value, and the completed integral lift maps to the image of the same field lift. Any supplied root equation persists in the completed ring. These are the character and phase lift equations and the good-prime power condition, once the actual character order is retained. |
| `Place.rat_mem` | A rational of nonnegative two-adic valuation maps to the complex coefficient ring. |
| `Place.scaled_phase_factor` | If $z\in\mathcal O$ and $r\ne0\Rightarrow s-k\le v_2(r)$, then $2^kzr=2^s y$ with $y\in\mathcal O$. Includes $r=0$ and negative integer $k$. Supplies the depth-zero squarefree factor in the singleton proof. |
| `all_mem_of_recurrence` | An integral character, integral squarefree coefficients, zero at index zero and off the prime support, and `RecAt` at every good prime imply integrality at every index. |
| `recur_scale` | Scaling the entire sequence by one scalar preserves `RecAt`. |
| `Place.unshiftedLift_complex`, `Place.unshiftedLift_local` | From $2^k a_n\in\mathcal O$ construct a field lift of $a_n$; the integral lift of $2^k a_n$ agrees with $2^k$ times the same lift under the completion embedding. Gives the two equations for the coefficient fields of `SourceAtPlace`. |
| `Place.source_shift_mem` | The squarefree phase identity, $v_2(r_D)\ge\delta$ at retained nonzero coefficients, sieve vanishings, and the exact recurrence give $2^{-\delta}a_n\in\mathcal O$ for every $n$. |
| `sourceHyp_of_complex` | Lift an integral character and a sieved coefficient sequence satisfying the squarefree integer-two factor and the signed recurrence to subring-valued sequences. Their complex images are the inputs, and they satisfy `SourceHyp t δ` for every (t). Used for the depth-zero singleton. |
| `shell_indices_unique`, `unary_on_shell` (private) | The representation $n=dm^2$ has unique positive shell variables with $d$ squarefree; the unary coefficient of subscript $J$ there is $\eta(m)m$ exactly when $J=d$ and $m$ is coprime to the cutoff, and zero otherwise. |
| `mem_of_dvd` (private) | If $e\mid z$ in the subring, $e\ne0$ and $eb=z$ in $\mathbb C$, then $b$ lies in the subring. |
| `singleton_divisions` | From `SourceHyp 2 0` on the primes coprime to the even cutoff $M$, both exact `Bp` and `Hp` lie in the subring for every such prime and every index. Uses `O9`, `O11_theta`, and `O11_offJ`. |
| `singleton_of_shell` | The same result directly on complex Fourier coefficients: uses the positive-sign `ShellRecurrence`, sieve vanishings, character laws, $a_q\equiv q+1\pmod4$, and the squarefree $2^{\omega(D)}$ factor. The `Hp` conclusion is exactly the integrality conjunct of `hpacket` after specialization. |

The construction of the completion maps, the valuation-ring comparison, the rational factor lemma, and the arithmetic interface transports are on-the-spot (c). The division estimates themselves reuse the manuscript's existing `O9` and `O11` proofs. No new printed-form leaves.

## Remaining inputs and owners

For `budgetRealization_of_blocks`:

- **App E and coefficient-place binding (this lane, pending import artifacts).** The smallest producer statement is the same conclusion as `AppE.evenPhaseData_of_prints`, on the same witness `P`, with the added conjuncts `∃ eψ, P.ψ ^ (2 ^ eψ) = 1` and `∃ eη, P.η ^ (2 ^ eη) = 1`. Preserve the original record and its `retained` and `z` equalities verbatim; forgetting the two conjuncts gives the original result. The existing print gives the first and `AppE.eta_pow_two_pow_eq_one` gives the second before the existential witness is packaged. Thread that very record through `AuxInputs.evenSource_of_phase` and make the family choice once per type. The existing existential does not identify a particular witness with a new independent choice.
- **Coefficient record binding (this lane, same build stop).** For the resulting $P$, apply `source_shift_mem` to `P.sievedCoeff` using `squarefree_phase`, `sieved_off_squarefree`, `sieved_recurrence`, and `P.lower`. Form `C : SourceAtPlace P V.LocalIntegers V.LocalField` with `K₀ := F`, `eC := F.subtype`, `eK := FinitePlace.embedding V.v`, `k := -P.δ`, coefficients from `unshiftedLift` and `localLift`, and both character maps from `fieldLift` and `localLift`. The phase lift uses the latter two maps as well. The missing checked conclusion is `∃ C : SourceAtPlace P V.LocalIntegers V.LocalField, ∀ p, T.Good p → ∃ t : ℕ, C.η p ^ (2 ^ t) = 1`. The prime eligibility for the power condition is `fresh_domains` and the character power transports by `localLift_pow` (or `eta_phase_of_character`). This step requires no additional divisibility estimate.
- **Even analytic realization.** For the same $C$, a single parity choice `i : Fin 2` and `hF : ∀ U, (∀ p ∈ U, T.Good p) → U.card + 1 ≤ B → ∀ n, n ≠ 0 → A.coeff n (X.F U) = ThetaCoeff.timesTheta (evenH hS A C i U) n` on actual weight-two forms.
- **Constituent and formwise lanes.** One budget-wide `X : Model P hS B` and `A : FourierData X` over compatible completed coefficient maps, `CharZero X.K`, `hm : X.m.IsMaximal`, and `hHecke : A.FormwiseHecke`. This includes the common stable lattice and actual determinant (diamond) and trace and inertia data in the even-budget report. The place construction is independent of $B,U$; identifying or extending it to the constituents is part of this assembly.
- **Local-block lane.** `localBlocks`: for each tested $U$, $q\in U$ and `Q : LocalPair q`, `Nonempty (O12Local.Stage A U Q (hU q hqU).1.ne_zero)` at the indicated prime instance.

For `kSplitSeed_of_singleton_trace`:

- **Actual transported source binding (this lane, same build stop).** Retain the two character orders from the positive-sign App E call in `genuineEvenSource_of_prints`, with its original `phase_eq`. On this same `G`, use `V.complexIntegers` for `O`, `odd_inv_mem` and `half_not_mem` for the denominators, and `character_mem` for `hηO` and `hz`. Specialize `singleton_of_shell` with `a := evenCoeff G`, `M := D.m₂`, `ap := apk W`, and `adm := S0Filter S 1`. The recurrence is `evenCoeff_shell`, the mod-four input is `apModFour_curve` with `D.bad₂`, and `evenCoeff_squarefree` and `scaled_phase_factor` give the base factor from `hlow`. The singleton integrality conjunct then holds before any no-reading assumption.
- **Address integrator.** Align the two supports with `∀ q, q.Prime → (q ∈ S ↔ q ∣ D.m₂)` or provide the same sieve and unary support compatibility directly. This run chooses no modulus.
- **Old-unit lane.** Supply `hlow : ∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n)`, exactly the output of `transported_lower_of_old_unit`.
- **Singleton analytic, constituent, and trace lanes.** For each tested prime, the remaining `hpacket` requires $p'\ne p$ prime, coprime to `D.m₂`, with `jacobiSym W.kfin p' = 1`, and `tf df δB δ1 δp` with `δB = δp`, `δp ∈ O`, `InTwoO O (δp - δ1)`, `DphiBlocks df a η D.m₂ p δB δ1 δp`, `tf (p ^ 2) = thetaMul (Hp a η D.m₂ p) (p ^ 3) + df p`, and `InTwoO O (tf (p ^ 2) - thetaMul (Hp a η D.m₂ p) (p ^ 2 * p'))`. The existing fresh-prime result can supply $p'$ given finite restriction-class descent modulo $2\mathcal O$ and the good-prime Fourier formula at that same coefficient.

## Known issues

- Tex 8162–8167 (ledger N4): the displayed normalization gives $b_0=a(D)$; the $b_r$ as defined there need not be integers. Use the integer multipliers $A_{p,r}(D)$ in tex 8168–8182 and the exact recurrence (E.12).
- The complex ring is the image of the algebraic field's valuation ring. There is no use of an embedding into $\mathbb C$ of the whole completed coefficient ring. The chosen prime is shared by the precompletion and completion realizations.
- The singleton's unary correction uses `D.m₂` and the actual Fourier sieve uses `S`. If a prime is excluded by just one of these, the shell divisibility argument does not apply on the mismatched shell. The manuscript uses one support for both; the existing interfaces leave the alignment implicit.
- The existing phase record does not retain the character order. The order of the displayed squarefree phases alone is not used as a substitute for it.
- No printed source was reread and no page or theorem locator from memory is asserted. The properties of the existing print inputs were used as stated in the repository when inspecting the producer.

## Manuscript check

- Tex 7943–7944 — unverified: the existing App E order theorem is present, but threading it through the actual source producer was not checked in this checkout.
- Tex 8040–8082 — gap filled: for the sieved sequence, the single coefficient field follows directly from the character values, rational squarefree factors, and shell recurrence; the geometric base-change claim is not needed for this closure.
- Tex 8130–8145 — OK: use the phase evaluation and the rational factor in (E.11); the proof includes zero coefficients.
- Tex 8156–8161 — OK: reuse the exact signed coefficient recurrence, with the off-index term zero.
- Tex 8162–8167 — error: the stated normalization omits the factor (a(D)) for the integer multipliers.
- Tex 8168–8182 — gap filled: induction at a prime square propagates the same field and integrality to every retained index; the sieve gives zero on the discarded indices.
- Tex 8183–8189 — gap filled: character and phase power equations survive at the chosen place. Residue comparison on a supplied source is already in `EvenBudget.Valuation`.
- Tex 9585–9608 — OK: the good-prime mod-four input is the one required by the existing shell estimates.
- Tex 9450–9455, 9570–9584 — gap filled: the fixed depth gives the exact integer-two division, including the singleton's first division at all indices.
- Tex 9471–9483, 9618–9632 — gap filled: match the Fourier-sieve support and unary cutoff, split the two unary shells from the off-shell indices, and apply the existing integer-two estimates.
- Tex 9638–9643 — gap filled: both coefficient rings come from the same prime above two; the singleton argument divides by integer two before reduction.
- Tex 9649–9652 — unverified: compatible constituent spaces and fields are outside the coefficient construction.
- Tex 10288–10318 — OK: the two sources may have different phases; use only the old-unit lane's valuation bound on the transported source.
- Tex 10332–10333 — OK: use the characteristic-zero coefficient ring with two noninvertible; the ideal $2\mathcal O$ is distinguished from the maximal ideal.
- Tex 10337–10344 — gap filled: the exact `Bp` and `Hp` integrality follows from the shell proof, including the zero constant term, without using the strengthened no-unit bound.

## Verification

- `Place.lean`, `Scalars.lean`, `Source.lean`, and `Singleton.lean` each passed `lake env lean -j1`, one Lean invocation at a time.
- All 29 statements above, including the six private lemmas, reported exactly `[propext, Classical.choice, Quot.sound]` in `scratch/rc-even-place/Axioms.lean`. No new axioms, placeholders, or printed-form inputs.
- Direct checks of the upstream entry points stopped at the absent artifacts for `AppE.Rational`, `EvenBudget.Valuation`, and `KSplitSeed.Sieve`, respectively. The upstream consumer bindings are unverified.
