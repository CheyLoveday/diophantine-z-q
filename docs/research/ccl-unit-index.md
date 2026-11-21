# Cai–Chen–Liu unit index

**Result: stopped before changing the leaf.** The manuscript correctly excludes
the two exceptional fields (tex 2720–2722 and 2839–2840). The Lean CCL interface
omits that restriction, and its generic transport consumers still promise the
unweighted equation at conductor one. The proposed level argument needs a
correction: −4 is a square modulo 8. Lean verifies that `4 ∣ N` gives the
required obstruction modulo **16**, and verifies that a prime divisor already
present in the staged chain makes every old conductor greater than one. Neither
argument supplies the missing premise of the generic consumers. No production
Lean declaration changed and no consumer gained an open hypothesis.

Cai–Chen–Liu, Trans. Amer. Math. Soc. 370 (2018), Thm 2.15, p. 3730 (read: AI
reading of the journal page). This locator and the formula are recorded by the
reading desk; the journal page was not independently re-read for this task.
The theorem has `uₘ` times the trace on the left, with `uₘ = 1` for
`m ≠ 1` and `u₁ = [𝒪_K^× : ℤ^×]`. The hypothesis
for an unweighted statement is therefore `m = 1 → u₁ = 1`.
Equivalently, for a genuine imaginary quadratic field with fundamental
discriminant `DK`, use `m = 1 → DK ≠ -3 ∧ DK ≠ -4`. An imaginary quadratic
unit has norm 1 and integral trace between −2 and 2. Traces ±2 give ±1; the
other traces give the extra roots of unity in the two exceptional fields.
The index is 2 for discriminant −4, 3 for −3, and 1 otherwise. The guard is
only an arithmetic restriction on an input; it asserts neither the existence
of an anchored point system nor a norm equality. No new structure or
hypothesis-bearing Prop was introduced.

The staged input constructor `e2ChainInputsS_of_actual` sets
`d = thetaCond Fam x (G.r (t + 1))`. Even for the more general staged
input, `G.r_prime`, `dvd_thetaCond_r`, `I.hfd`, `dvd_chainCond` and
`I.chainCond_pos` give a prime divisor of every `d_i` and `1 < dᵢ`.
This discharges the guard if the print is applied with `m = dᵢ` in its
range. For the manuscript audit's `c = dᵢ, m = 1` choice, the same
constructor has the field exclusion instead: `St.companion hodd` gives
`D.kfin ≠ -3` and `D.kfin % 4 = 1`, and `discr_of_sqrt` identifies
`discr C.K` with `D.kfin` (so it is also unequal to −4). The full anchor
identifies `D.DK` with this field discriminant. The good reduction and
support wrappers pass through the same data.

The generic `H20HeegnerNorm` and `H20Transport` lemmas have an admissible
pair, the split Jacobi value, and an additive comparison. Their print
wrappers allow arbitrary anchors. `H20Dictionary` adds the Galois
comparison; `H20Anchor` and `H20DictFields` also furnish a Heegner form
at conductor one, but leave the curve and level generic. The arithmetic
premises really allow `d = 1`: with `N = 37`, `DK = -4`, and `q = 5`,
the form `[37,12,1]` has the required level and discriminant, the pair is
numerically admissible, and the Jacobi value is 1. Lean verifies these
numerical facts. Additive transport preserves a scalar factor and does
not turn `uₘ x = y` into `x = y`. The three `H20PresClass*` step lemmas
inherit the unrestricted output. The old `CommonCoordinate18E2` provider
only records that its base conductor is positive and divisible by a
nonzero `f`; the level divisibility needed for the alternative route is
unproved for its `newformLevel`. `CochainNorm` already takes the point
equality as an explicit input, and does not call the leaf.

**Changed consumers: none.** The full inventory, including
`CommonCoordinate18LeafE2`, `CommonCoordinate19Leaf`, wrappers and
comment-only users, is in [consumers.md](../../scratch/ccl-unit-index/consumers.md).
The two Mathlib import modules built separately. The
[scratch check](../../scratch/ccl-unit-index/Check.lean) compiled with
[only standard axioms](../../scratch/ccl-unit-index/axioms.txt) in its six
declarations. There were no changed project modules or downstream
rebuilds to verify under the stop rule.

## Known issues

- **VERIFIED, tree error:** `HeegnerPointData.NormRelations` in
  `ZInQKernel/Contrib/OneProof/RC/PrintsArith/Heegner.lean` drops `uₘ`
  without enforcing the condition. The manuscript invokes the field
  exclusions explicitly; this mismatch is in the tree.
- **VERIFIED, proposed level argument:** the reduction modulo 8 fails for
  −4, since `2² ≡ −4 mod 8`. If `4 ∣ N`, the Heegner form
  condition `B² − D = 4AC and N ∣ A` gives reduction modulo 16, where the
  residues of −3 and −4 are 13 and 12, neither a square. No theorem
  identifying the actual curve's `newformLevel` as divisible by four was
  used or proved.
- **UNVERIFIED, change of print indices:** the reading desk uses
  `c = d, m = 1`, with the full old conductor in `c`. Even for `d > 1`,
  this choice still has `m = 1`. To use `m = d > 1` instead, check the
  allowed conductors and the exclusions in the print's set `S`. In
  particular, the tree allows `3 ∣ d` when `3 ∤ 2ND_K`, whereas
  `3 ∈ S`; moving the whole conductor into the index supported outside `S`
  is therefore not a general replacement. No independent error in
  the journal statement has been established.

A revision can carry the printed scalar through the generic transport and
export the unweighted equality only after specialization. It still needs
a proof for the older conductor-one wiring or a decision to retire that
unrestricted guarantee. Strengthening the opaque print witness or the
arbitrary anchor to assert the desired specialization would leave the
same obligation open.

## Manuscript check

| Step in `diophantine_zq.tex` | Verdict |
| --- | --- |
| Tex 2720–2722: imaginary quadratic field split at `2N` and neither exceptional field. | OK |
| Tex 2728–2741, 2780–2785 and 3500–3506: the moving character comes from a ring class field of prime conductor. | OK |
| Tex 2836–2838: the parametrization is algebraic over `ℚ` and normalized at infinity. | unverified (the identification with `phiAn` is GLUE). |
| Tex 2839–2844: the exclusions and the ring class field of the order of conductor `f`. | OK |
| Tex 2846–2855: enlarge the old conductor by the new primes and use the finite character from the ring class group. | OK |
| Tex 2915–2917: choose a global compatible family of proper ideal lattices and fix the orientations at level `N`. | unverified (GLUE; the existing analytic anchor provides individual forms rather than this compatibility). |
| Tex 2917–2921: specialize to `X_0(N)` at split level; take `c = d, m = 1` and the new prime outside `6dND_K`. | OK in the recorded journal reading. |
| Tex 2921–2922: `u₁ = 1` from the explicit exceptional-field exclusion. | OK |
| Tex 2924–2929: the resulting unweighted point norm at inert and split primes. | OK under the manuscript's field restriction. |
| Tex 2931–2932: Frobenius at the conjugate prime is the inverse because the product is the Artin symbol of a rational principal ideal. | OK mathematically; GLUE in the dictionary. |
| Tex 2933–2936: Hecke equivariance and the cusp at infinity give the identity without a cusp term. | unverified (the passage through the normalized algebraic quotient is GLUE). |
| Tex 4142–4146, 4157–4172: the unused-prime comparison uses the split point factor and the retained boundary. | OK at the level of the cochain calculation from the point equality. |

The following are the six **GLUE** items for the leaf docstring once the
statement can change: (1) the `c/m` dictionary: at `c = d, m = 1`, the
print's `H_m` denotes the field of conductor `cm`; (2) the decomposition
law identifying the Jacobi value with inertness or splitting; (3) the
identification of Frobenius at the conjugate prime with
`σ_q⁻¹`; (4) the global compatible family of lattices and
orientations at tex 2915; (5) the identification of the CM ring class field
with the vendored class-field-theory ring class field; (6) the identification
of `phiAn` with the algebraic parametrization over `ℚ` satisfying
`π(∞) = 0`, with the Hecke action and cusp normalization at tex
2933–2936.
