**Manuscript support slip (tex 10393–10404).** If “old support” means the
pre-transport support of tex 10293, the zero-or-shell split in (G.4b) misses
indices divisible by newly excluded primes. The zero branch uses the full
stationary support of the transported form, as in tex 9471–9479. If “old”
means before adding the tested prime `p`, that is already the full
stationary support. The proof below uses the preceding determinant identity,
tex 10375–10386, for the required divisibility.

**Scoped stop.** The Lean proof supplies `KSplitSeed` for the same
`RevGen S G.r`, conditional on the old-unit comparison and the actual
singleton divisions and trace data. Attainment at index 1 accounts for
the empty reading; the trace argument is what gives a nonempty seed.
The odd and even density conversions use finite fields at the individual
tested sets. The genuine constituent realizations and their finite
quotients remain to be supplied.

All declarations below are in `ZInQ.Manuscript.RC.KSplitSeed`.
Write `n_U` for the product of the primes of `U`, `a` for `evenCoeff G`, and
`a_p` for `apk W p`. Here `H_p` is the existing
`KSplit.Hp a (fun n => G.P.η n) D.m₂ p` and `f = θ H_p` is the
existing `KSplit.thetaMul H_p`. The construction introduces neither a
seed operator nor a new Galois trace operator.

| Declaration | Statement and consumer |
| --- | --- |
| `revGen_eq_one_iff` | On a prime set `U`, `RevGen S r U = 1` iff `n_U` is in `S0Filter S 1`, `r`n_U` ≠ 0`, and `v₂ r`n_U` = U.card`. Used for the genuine seed. |
| `transport_valuation` | From the three rational square identities with ratios `L_D/L_k`, `L_D/L_ref`, and `L_k/L_ref` and the indicated nonzero values, `v₂ r_new`D` = v₂ r_old(d_k D) − v₂ r_old`d_k``. Used for the genuine seed. |
| `revGen_empty` | If `L_*(k) ≠ 0`, `RevGen S G.r ∅ = 1`. Together with the transported lower bound this proves attainment of depth zero. It does not produce the nonempty seed. |
| `succ_le_padicValRat_of_revGen_zero` | If `n_U` is retained, the coefficient is nonzero, `v₂ r`n_U` ≥ U.card`, and the reading is zero, then `v₂ r`n_U` ≥ U.card + 1`. Used for the genuine seed. |
| `evenCoeff_squarefree`, `evenCoeff_one` | At a squarefree index, the normalized and sieved coefficient is `z_D r_D` in the exact filter, and zero outside it. At 1 it is 1. Used for the genuine seed and identifies the source to be used by the even budget. |
| `evenUnitSieve_mul_sq`, `evenCoeff_shell` | The Fourier sieve is invariant under multiplying the index by `p^2` at every prime outside `S`. The actual normalized and sieved coefficients satisfy the existing `ShellRecurrence` with `apk W p` and `ψ(p) = η(p) (−1/p)`. Used for the genuine seed. |
| `transported_lower_of_old_unit` | From `S` containing the prime factors of `d_k`, the old square comparison at `d_k` and `d_kD`, the old unit at `d_k`, and the old lower bound at retained `d_kD`, obtain `∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n)`. Used for the genuine seed and even budget. |
| `ratCast_pow_two_factor` | For nonzero rational `r` with `v₂(r) ≥ e ≥ 0`, `(r : ℂ) = 2 ^ e * y` for some `y ∈ O`, provided `O` contains inverses of odd positive integer denominators. Used for the genuine seed. |
| `evenCoeff_factor_of_no_reading` | Under that rational ring condition, phase integrality and the transported lower bound, a zero reading on a prime set gives `∃ y ∈ O, a n_U = 2 ^ (U.card + 1) * y`. Includes off-filter and zero coefficients. Used at the singleton and pair in App G. |
| `dirichletValue_unit_of_coprime` | If the natural-index values of η lie in the coefficient ring, at a unit residue its value is nonzero and its inverse also lies in the ring. The inverse is another value of η. Used for the genuine seed. |
| `eight_dvd_of_trace_match` | Given the singleton divisibility and trace inputs listed below at two distinct good split primes, absence of nonempty units of the same reading gives `(8 : ℤ) ∣ (p : ℤ) + 1 - apk W p`. The evenness of the determinant term uses tex 10375–10386. |
| `kSplitSeed_of_singleton_trace` | Given the ring, lower bound and singleton inputs below for the selected `G`, supplies `KSplitSeed W D (RevGen S G.r)` in `AddressDensityLeafGenuineEven`. The exceptional set is `S ∪ D.m₂.primeFactors`. The existing `exists_unit_of_kSplitSeed` turns this implication into a nonempty seed under its ambient and companion hypotheses, including `FreshPrime`. |
| `exists_fresh_trace_match` | If the actual scalar coefficient `g ↦ (t(g)f)[p²]` descends modulo `2O` at the given Frobenius lift on a finite field, and the good Hecke formula gives that scalar at `q ≠ p`, the proved density theorem produces `p′ ≠ p` avoiding a prescribed finite set, of the same stationary type and with `(k/p′) = 1`, together with the match modulo `2O`. Used for the singleton comparison in the genuine seed. |
| `matched_product_in_filter` | Two distinct good primes with the same stationary squareclass have a product in `S0Filter S 1` when `S ⊆ D.m₂.primeFactors`. This also checks the square-unit condition at 2. Certifies App G’s matched-pair filter. |
| `evenGood_iff`, `not_dvd_even_level` | When `D.m₂.primeFactors = S`, the good primes of `D.T₂` are precisely the primes outside `S`; the inclusion in the other direction from the base adapter, `S ⊆ D.m₂.primeFactors`, alone ensures they avoid the actual level `G.P.N`. Used for the even density models. |
| `densityOfFiniteFields` | On an existing constituent model `X` with `X.Inputs`, finite fields with the exact inertia property below give a `GaloisDensityModel`. One may transfer the symbol using equality at good sets up to the cutoff, without equating the total functions. |
| `evenDensityModels_of_constituent_fields` | Given such constituent realizations at each budget, supplies `EvenDensityModels W D (RevGen S G.r)` in `AddressDensityLeafGenuineEven`. |
| `oddDensityModels_of_stage_fields` | Given such constituent realizations at `Wc + 1` eventually on `W.stages` for each `Wc`, with the same intrinsic symbol on tested primes, supplies `OddDensityModels W D` in `AddressDensityLeafGenuineEven`. Use `O12StageVal.rodd_eq_intrinsic D` with the existing integer stage symbol on `D.oddAdmissible`. |

At an odd cutoff the bridge can use the existing stage reading directly:

```lean
oddDensityModels_of_stage_fields D
  (fun θ => O12StageVal.intrinsic (W.aθ θ) W.δo (fun n => D.oddAdmissible θ n))
  (fun θ _ hU => O12StageVal.rodd_eq_intrinsic (i := θ) D hU)
```

The remaining argument gives the actual constituent data and its fields on
the eventual set for each cutoff.

## Exact remaining hypotheses and owners

The results are conditional. Here the names in code (especially
`hpacket` and `hfields`) give the exact Props. No new structure or
leaf is taken as a hypothesis. The inputs below are smaller in scope:
they concern the source coefficients, one Fourier coefficient and its
operators, or the finite fields of an already given system of forms.
In particular none contains a claim of existence of a nonempty unit.
Finite field ramification is a specific sufficient witness, stronger
than the density interface's permission to use extra finite exceptions;
it is the full-support construction of App F.

| Input | Tex and owner |
| --- | --- |
| `hOldk`, `hUnit`, `hOld`, `hOldLow` of `transported_lower_of_old_unit` (with a common nonzero `Lref`, `L_*(k) ≠ 0`, and `k.natAbs.primeFactors ⊆ S`) | 10260, 10293–10314. ELLIOT, companion integrator and existing Appendix E comparison. The current companion identifies a nonzero reference and exclusions; it does not identify the valuation of its old coefficient with the old minimum. On the exact old source the square comparisons are (E.11). The remaining alignment says `d_kD` stays in its old retained filter; `D` is a square unit at the old support. Once those comparisons and the single old unit equation are supplied, there is no further lower-bound input. |
| `O : Subring ℂ`, `hodd : ∀ d : ℕ, ¬ 2 ∣ d → (d : ℂ)⁻¹ ∈ O`, `hhalf : (2 : ℂ)⁻¹ ∉ O`, `hz : ∀ n, S0Filter S 1 n → G.P.z n ∈ O`, and `hηO : ∀ n : ℕ, G.P.η n ∈ O` | 8140–8145, 8182–8187, 9638–9643, 10332–10333. Coefficient realization, `rc-even-budget` and existing Appendix E. The material input is a characteristic-zero realization of the coefficient valuation ring and of the phases in it, with the chosen prime above 2; completion or an embedding into ℂ of all completed coefficients is unnecessary. The η inverse at a good prime is proved from its unit residue and the given η values. |
| `∀ n, Hp a η D.m₂ p n ∈ O` for each tested singleton | 10337–10344 and (O.11), 9450–9455. `rc-even-budget`: exact integer divisions of the same depth-zero even series. The shell recurrence is now proved and is not an input. |
| For every prime `p ∉ S` coprime to `D.m₂` with `jacobiSym W.kfin p = 1`, `hpacket` further asks for `p′ ≠ p` prime, coprime to `D.m₂`, split in `K`; `tf df : ℕ → ℂ` and `δB δ1 δp : ℂ` with `δB = δp`, `δp ∈ O`, `InTwoO O (δp - δ1)`, `DphiBlocks df a η D.m₂ p δB δ1 δp`, and `tf (p ^ 2) = f (p ^ 3) + df p`, `InTwoO O (tf (p ^ 2) - f (p ^ 2 * p'))`. | 10326–10333, 10355–10379, 10437–10441. ELLIOT/GLUE, weight-two singleton realization: the characteristic-zero bad-prime `U_p² t(φ)` identity and three determinant blocks at that Frobenius lift, plus the one coefficient trace match. The smallest remaining matching input is constancy of `(t(g)f)[p^2]` modulo `2O` on a restriction class and the good formula at that same coefficient, as in `exists_fresh_trace_match`; the choice of `p'` then follows. The bad-prime identity and determinant comparison are separate one-packet equations. Constructing the characteristic-zero representation and its compatible integral Fourier lattice is substantial if unavailable. The residual address density model alone has no `p^2` reading or modulus `2O`. |
| On the selected actual model `X`, for each good `U` with `U.card + 1 ≤ B`: `∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧ E.fixingSubgroup ≤ X.N U ∧ ∀ q : ℕ, T.Good q → q ∉ U → ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q → Q.inertia GalQ ≤ E.fixingSubgroup`. | 9524–9555, 9638–9668, 9745–9750. Trace realization and finite field glue. Choose a quotient for the trace action on `F_{U'}` for `U′ ⊆ U`, together with the fixed labels and radicals at the added primes. This is a field for one tested `U`; no common field for all `U` is required. |
| In the even case, at every `B`, an `X` and `X.Inputs` at `D.T₂`, `RevGen S G.r`, `apk W`, `typChar D.m₂`, with its forms realized as the manuscript's `F_U = θ H_U` on the selected normalized and sieved coefficients `evenCoeff G`. | 9450–9455, 9570–9573, 9638–9745, 9754–9918, 10288–10318. `rc-even-budget` for exact divisions and the attached coefficient packet; ELLIOT/missing weight-two realization for constituent representations at the actual levels with compatible `T_q,U_p,d` action and the local block comparison. Existing trace, Fourier and (O.12) consumers handle the formal rules once those data are available. No new printed-form leaf is added. |
| In the odd case, at `B = Wc + 1`, `X` and `X.Inputs` for the intrinsic stage symbol, eventually in `W.stages` for each `Wc`, with the fields above on the same packet. | 10190–10255, 10533–10548 and the App F trace/local lines in the preceding row. Use the existing `O12StageVal.integerDepth_of_data` and `inputs_of_pm` at those stages. What remains is the genuine Fourier realization and local comparisons in `inputs_of_pm`, and the odd stage premises supplied by the reviewers and `rc-theta-join`, `rc-theta-close`, `rc-o7-actual`, `rc-stage-kummer`. In particular the odd symbol and its minimum use the intrinsic old filter. Later exclusions cannot be used as extra Fourier vanishings. |
| `D.m₂.primeFactors = S` as the intended full-support choice, or the two inclusions separately for the good-prime and filter implications. | 2016–2029, 9471–9483, 10292–10295. Address integrator and `rc-even-budget`. The base provides `D.m₂.primeFactors ⊆ S` for the squareclass implication; the new good-prime bridge uses `S ⊆ D.m₂.primeFactors`. The integrator must choose the modulus after accounting for the actual stationary sieve and the new source level. No `LabelData` constructor is added here. |

## Known issues

- See the support slip at the top. The alternative determinant proof does
  not use (G.4b). The final mod-eight argument uses the actual division by
  two, as required at tex 10332–10333. The manuscript's weaker phrasing
  “zero in the residue field” at 10478–10480 also suffices for this
  particular coefficient, because after multiplication by a unit it is
  an integer, and the proper ideal above two contracts to the ideal `(2)` on
  `ℤ`.
- `GenuineEvenSource.P.g` is a pre-sieve analytic eigenspace witness.
  Its `retained` field describes the squarefree domain of (E.11); it
  does not assert that the raw Fourier coefficients are zero outside it.
  `evenCoeff` takes the all-index coprime square-unit sieve explicitly.
  Its proof is coefficientwise. Modular realization of this same sieve
  and its divided forms belongs to the budget and weight-two packet work.
- `TraceLimits.buildConstituentModel` uses one fixed avoidance set; its
  coverage conditions exclude any added good prime from that set. Its
  unramifiedness premise therefore cannot cover the genuinely ramified
  blocks at added primes. The new conversion does not apply this constructor
  to those blocks.
- No new prints. The existing Appendix E good Hecke identity and character
  convention are reused through `GlueSweep.Sym`. The existing printed-form
  attachments (Waldspurger, Shimura and the weight-two Carayol and local
  constituents used by App F) are unchanged. Their external locators were
  UNVERIFIED in this run. No unread statement is promoted to LEAF; any
  later addition requires the lead's skeptic pass.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 2016–2029, 2068–2089 | gap filled | Match the actual exclusions to the conductor and evaluate the symbol at the product of distinct primes. The Lean casts and prime counts are on-the-spot (c). |
| 8136–8146 | OK | Reuse (E.11), also at a zero coefficient. Take valuations only at the nonzero coefficients; the two-power phases are units at the place above two. |
| 8147–8161, 9471–9483 | gap filled | The sieve on all indices persists through a good square shell. The divisibility, mod-eight and finite-field proofs of commutation are on-the-spot (c). |
| 9450–9455, 9570–9573 | unverified | Exact divisions on the genuine even forms are the even budget lane's input. |
| 9524–9555, 9638–9668 | unverified | Actual weight-two modular realizations and their integral trace lattices are pending. The fixed-level constructor is too restrictive for the added-prime packets. |
| 9671–9704, 9719–9750, 9754–9918 | gap filled | Assemble a model from the constituent readings and per-set fields. The trace and local comparisons on actual forms are still inputs. Use the proved density theorem for the quotient; the finite field and symbol transport is on-the-spot (c). |
| 10190–10255 | OK | Use the existing eventual depth and precision through the cutoff on the intrinsic odd filter. This does not select a common stage for all cutoffs. |
| 10288–10314 | gap filled | Cancel the normalizing old value in the three square identities, and count the prime factors of the coprime product. Formal valuation and ring bookkeeping is on-the-spot (c); the old unit and its comparison remain upstream. |
| 10317–10318, 10437–10450 | gap filled | Adjoin the stationary type field for the Frobenius match. Equal unit squareclasses multiply to the neutral type, and the product meets the dyadic condition. The field and squareclass bookkeeping are on-the-spot (c). |
| 10323–10325, 10345–10353 | gap filled | Use integrality of the rational valuation and exclude equality with the same symbol; express the result as integer-two divisibility in the coefficient ring. This bridge is on-the-spot (c). |
| 10326–10333, 10355–10379 | unverified | The bad-prime operator and determinant-block comparison on the actual characteristic-zero form are inputs. |
| 10380–10386, 10430–10436 | OK | The determinant identity already gives evenness at p; theta multiplication preserves the coefficient modulo integer two. |
| 10393–10404 | error | The split on “old support” is incomplete as written if it refers to pre-transport support. The zero branch requires the full stationary transported sieve before adding p. |
| 10442–10481 | OK | The existing unary-subtracted shell identity gives the exact coefficient. Use the match and the two-prime divisibility before the mod-eight test. |
| 2628–2654, 10482–10500 | OK | Reuse the formalized mod-eight contradiction for the particular split cubic and the prescribed fresh ramification. |
| 10533–10548 | OK | The odd models are indexed separately by cutoff and are available on an eventual set in the original ultrafilter. |

## Verification

`Valuation.lean`, `Sieve.lean`, `Seed.lean`, `Fresh.lean`, and `Density.lean`
each passed `lake env lean -j1`, run serially.
`scratch/rc-ksplit-seed/Axioms.lean` checks all 23 declarations (20 theorems
and three definitions); each depends only on `propext`, `Classical.choice`,
and `Quot.sound`.
