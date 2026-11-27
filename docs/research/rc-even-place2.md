# Bind the App E sources to one coefficient place

The order-retaining App E producer, the fixed-type `SourceAtPlace`, and the
transported singleton coefficient ring are connected on the actual source
records. The two records can use one cyclotomic number field and one prime
above two. The budget source uses the completion and its integers, with
one shift by `-P.δ` at every index. The singleton uses the image in `ℂ`
of the valuation ring before completion, at that same prime. With the
ordinary transported lower bound and common support, both exact divisions
`Bp` and `Hp` lie in this ring at every index, including zero. No
no-reading hypothesis enters either division.

The arithmetic from [the preceding run](rc-even-place.md) is unchanged.
The negative fixed-type form and positive companion form may have different
phases. Neither the source nor the place has to be chosen again for each
operator set or singleton. No new printed-form leaves are used.

## Statements and consumer inputs

The declarations below are in `ZInQ.Manuscript.RC.EvenPlace`. Write
`T = evenTypes W.S hS.1` for the negative source, `V : Place F` for the
chosen prime of the embedded number field `F`, and `O = V.complexIntegers`
for the complex ring.

| Lean result | Statement and input supplied |
| --- | --- |
| `phaseData_forget_order` | For the same witness `P` with `PhaseOrigin P`, `P.retained = {D \| S0Filter S D₀ D}` and `P.z = AppE.phase P.N P.η D₀`, exactly the original data and equalities. |
| `phaseData_with_order_of_prints` | Under the unchanged inputs to `AppE.evenPhaseData_of_prints`, gives `∃ P : EvenPhaseData E L σ S D₀, PhaseOrigin P`. In addition to the two equalities, this records `ψ ^ (2 ^ eψ) = 1` and `η ^ (2 ^ eη) = 1` for some natural exponents, with `eη = eψ + 1` in the construction. The entire phase record uses the original constructor. |
| `evenSource_with_origin` (private) | Under the fixed-type minimum inputs of `AuxInputs.evenSource_of_phase`, a phase witness with `PhaseOrigin` gives an `EvenSource` whose phase field carries that provenance. The proof puts the supplied phase record directly in that field. |
| `evenSource_with_order_of_prints` | Under the inputs of `AuxInputs.evenSource_of_prints` including the nonzero reference, gives `∃ P : EvenSource W L τ, PhaseOrigin P.phaseData`. This is the negative source for `SourceAtPlace`. |
| `sourceFamily_with_order_of_prints` | Under the inputs of `AuxInputs.sourceFamily_of_prints`, gives `∃ P : SourceFamily W L, ∀ τ h, PhaseOrigin (P τ h).phaseData`. This fixes the source once per total type with a nonzero reference. |
| `genuineEvenSource_with_order_of_prints` | Under the inputs of `EvenReading.genuineEvenSource_of_prints`, extends the prescribed prime support `T₀` to `S` and gives `∃ G : GenuineEvenSource C hk S, PhaseOrigin G.P`. It uses the positive-sign App E form on the companion at reference one, with its rational (E.11) coefficients. This is the source for `kSplitSeed_of_singleton_trace`. |
| `phaseScalarsAt_of_order` | For exponents `eψ, eη ≤ e` witnessing the two orders, a place of `PhaseField e` gives `PhaseScalarsAt P V`: all values of both characters and every phase belong to `O`. Gives the character and phase membership used for the lifts, `hz` and `hηO`. |
| `common_phase_scalars` | For any two App E records with `PhaseOrigin`, there are `e` and one `V : Place (PhaseField e)` with `PhaseScalarsAt` for both. The witnesses use the maximum of the four order exponents. |
| `budget_shift_mem` | On the selected budget source, `2 ^ (-P.δ) * P.sievedCoeff n ∈ O` for every `n`. The original lower bound implies the needed squarefree bound, and the exact recurrence propagates it. |
| `sourceAtPlace` (definition) | On the same `P`, gives `SourceAtPlace P V.LocalIntegers V.LocalField`, with `K₀ := F`, the complex inclusion and completion embedding of `F`, `k := -P.δ`, and the coefficient, phase, character and two-adic maps with their agreement equations. |
| `sourceAtPlace_eta_phase` | For each `T.Good p`, the integral character of that very `sourceAtPlace` satisfies `∃ t : ℕ, C.η p ^ (2 ^ t) = 1`. This is `hphase` of `budgetRealization_of_blocks`. |
| `sourceAtPlace_exists` | For the chosen `EvenSource` with provenance, there exist `e`, a place of `PhaseField e`, and a `SourceAtPlace` over its completed integers and field with the good-prime power condition. In particular this supplies the budget's `Nonempty (SourceAtPlace P O K)` over those completed types. |
| `singletonCoefficientsAt_of_shell` | For the same transported `G`, phase scalars at `V`, support alignment and the ordinary lower bound, gives `SingletonCoefficientsAt D G V`. This supplies `O`, `hodd`, `hhalf`, `hz`, `hηO`, and `Bp, Hp ∈ O` coefficientwise at every prime coprime to `D.m₂`. In particular it supplies the integrality conjunct of `hpacket` at every tested singleton. |
| `common_place_for_sources` | For the two selected records with provenance and the same support and lower-bound inputs as the singleton theorem, produces one `V`, phase scalars for both, the good-prime condition for the negative `sourceAtPlace` at `V`, and the positive `SingletonCoefficientsAt` for that same `V`. |
| `kSplitSeed_of_trace_at_place` | Given the singleton coefficient packet, the ordinary lower bound and exactly the remaining matching-prime, determinant and trace conjuncts of `hpacket`, calls `kSplitSeed_of_singleton_trace` on the same `G` and proves `AddressGenuine.KSplitSeed W D (RevGen S G.r)`. |

The refinement of the existential interface, the common exponent bound,
and the comparison between the two consumer interfaces are on-the-spot
(provenance (c)). The `ψ` order is in the existing Waldspurger input; the
`η` order uses the existing `AppE.eta_pow_two_pow_eq_one`. The singleton
specialization reuses the existing integer divisions from (O.9) and
(O.11), the actual Fourier sieve and recurrence, and the curve's mod-four
identity.

## Remaining hypotheses and owners

For `budgetRealization_of_blocks`, fix the same `P`, `hS`, a budget `B`
and the selected place. A tested `U` satisfies
`(∀ p ∈ U, T.Good p) ∧ U.card + 1 ≤ B`.

- **Constituent and formwise lanes:** one budget-wide
  `X : Model P hS B` and `A : O12.FourierData X`, with
  `CharZero X.K`, `hm : X.m.IsMaximal`, and
  `hHecke : A.FormwiseHecke`. The coefficient ring and field of the
  stable lattice must use the constructed place, or a compatible
  extension that carries its maps and integral lifts. The actual
  trace, inertia, and diamond actions on this lattice remain with
  these lanes. A finite prime pool does not realize all the tests.
- **Even analytic realization:** a single `i : Fin 2` and, for every
  tested `U` and every `n ≠ 0`, the identity
  `A.coeff n (X.F U) = ThetaCoeff.timesTheta (evenH hS A C i U) n`
  on actual weight-two forms, with the same `C` and maps. This
  requires the even sieve, moving and unary forms, and ordinary theta
  multiplication at the stipulated levels.
- **Local-block lane:** for every tested `U`, `q ∈ U`, and
  `Q : LocalPair q`, supply
  `Nonempty (O12Local.Stage A U Q (hU q hqU).1.ne_zero)`
  with the prime instance from `hU q hqU`.

For `kSplitSeed_of_singleton_trace` on the actual `G`, write
`a := evenCoeff G`, `η n := G.P.η n`, `M := D.m₂`,
`f := thetaMul (Hp a η M p)` and `O := V.complexIntegers`.

- **Address integrator:** align the transported sieve and the unary
  cutoff: `∀ q, q.Prime → (q ∈ S ↔ q ∣ D.m₂)`.
- **Old-unit lane:** supply
  `∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n)`,
  the output of `transported_lower_of_old_unit`. It pays the exact
  singleton divisions and is also passed to the seed consumer.
- **Singleton analytic, constituent and trace lanes:** for each prime
  `p ∉ S` coprime to `M` with `jacobiSym W.kfin p = 1`, supply a prime
  `p' ≠ p` coprime to `M` with `jacobiSym W.kfin p' = 1`, and
  `tf df : ℕ → ℂ`, `δB δ1 δp : ℂ`, with `δB = δp`, `δp ∈ O`,
  `InTwoO O (δp - δ1)`, `DphiBlocks df a η M p δB δ1 δp`,
  `tf (p ^ 2) = f (p ^ 3) + df p`, and
  `InTwoO O (tf (p ^ 2) - f (p ^ 2 * p'))`. The existing fresh-prime
  argument gives the match once supplied the finite restriction-class
  comparison modulo `2O` and the good-prime formula at this coefficient.

These are the remaining inputs to these two consumers. The preexisting
App E print, reference and minimum inputs are unchanged.

## Known issues

- Tex 8162–8167 (ledger N4), already recorded in the previous report:
  the displayed normalization gives `b₀ = a(D)`, and its `b_r`
  need not be integers. The missing factor is `a(D)` in the integer
  multiplier formula; use (E.12) and tex 8168–8182.
- Tex 10393–10404: as recorded in the singleton report, the zero branch
  of (G.4b) uses the full stationary support after transport. If “old
  support” means the smaller support before transport, that wording
  misses newly excluded primes. The seed consumer uses the preceding
  determinant identity instead.
- A choice from the old bare existential is not identified with an
  independent new choice. Forgetting the order proofs works on the
  exact new witness, with every original field in the same record.
- The complex subring is the image of the valuation ring of the
  algebraic field. The construction does not embed the completed
  integers into `ℂ`. Ramification does not identify the integer ideal
  `2O` with the maximal ideal.
- External printed locators were not checked in this run. No page or
  theorem locator from memory is asserted. The existing conditional
  print statements, including the Ramsey field-extension input, are
  unchanged.

## Manuscript check

- Tex 7793–7810, 10079–10087 — OK: use the negative source on its original total-type filter with its nonzero reference and fixed minimum.
- Tex 7943–7944 — gap filled: keep the two order equations when packing the original phase witness, using the quadratic character identity to obtain the order of `η`.
- Tex 8040–8082 — gap filled: one number field contains the selected sieved coefficients by the phase identity and recurrence. The geometric section comparison stays in the existing App E inputs.
- Tex 8116–8135 — OK: the chosen square-root residue is evaluated by `η`; its value lies in the same character field.
- Tex 8136–8145 — OK: use the squarefree identity and its rational part (E.11) on the actual filters, including zero coefficients.
- Tex 8148–8161 — OK: the two actual sieve masks preserve the exact signed good-prime recurrence.
- Tex 8162–8167 — error: the stated integer multipliers omit the base coefficient.
- Tex 8168–8182 — gap filled: the exact recurrence propagates the shifted integral lift at every index of the negative sieve.
- Tex 8183–8189 — gap filled: the local lift preserves the good-prime character order; the existing budget residue comparison takes this source at the chosen place.
- Tex 9450–9455, 9570–9584 — gap filled: the depth-zero bound specializes (O.9) to the exact first division on the companion.
- Tex 9471–9483, 9618–9632 — gap filled: the shell estimates give the second division with the Fourier support and unary cutoff aligned.
- Tex 9585–9608 — OK: the good-prime mod-four identity is the input required by the shell calculation.
- Tex 9638–9643 — gap filled: the complex subring and completed integers are obtained from one place, and the proof uses integer-two division.
- Tex 9647–9652 — unverified: analytic weight-two realization and compatible constituent fields are separate inputs.
- Tex 10288–10295 — OK: use the positive transported source at reference one, independently of the original negative form.
- Tex 10296–10318 — unverified: the old-unit comparison is a separate input; only its ordinary squarefree valuation bound is used here.
- Tex 10326–10331 — unverified: the bad-prime trace and determinant packet is a separate input.
- Tex 10332–10333 — OK: the singleton consumer takes congruences modulo integer `2O` in characteristic zero.
- Tex 10337–10344 — gap filled: both exact singleton divisions are integral for every index before the no-reading argument.
- Tex 10393–10404 — error: reading “old support” as the support prior to transport leaves out the newly excluded indices; the existing seed proof uses the determinant route.

## Verification

- Serial Lake builds of the imports passed, including `AppE.Assembly`,
  `EvenBudget.Place`, `KSplitSeed.Sieve`, and `KSplitSeed.Seed`.
  `lake build` of the full new binding chain also passed.
- `Producer.lean`, `Sources.lean`, `BudgetBinding.lean`, and
  `KSplitBinding.lean` each passed `lake env lean -j1`.
- [Axioms.lean](../../scratch/rc-even-place2/Axioms.lean) checked all 15
  results in the statement table, including the private lemma and the
  `sourceAtPlace` definition. Each reported exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, new axioms,
  or new printed inputs.
