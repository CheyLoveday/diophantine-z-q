# Shimura's positive-index ring and quotient split

**Error in the base encoding, repaired.** The all-index ring in the
[committed verdict](../../.fleet/shimura-ring0-verdict.md) could force the
quotient map at `diophantine_zq.tex` L770–773 to vanish. The ring now uses
only positive indices. `ShimuraThm1Printed` contains the printed clauses
used for the quotient row, and the reduction to the unchanged
`R16Thm1b.ShimuraThm1Af` also takes `ShimuraQuotientByC`, the construction
from Shimura's proof on p. 526 (provenance (c), GLUE).

## Error and scope check

On the base, replacing `ξ 0` by the identity of `J` preserved
`XiAction` and `PrintedClauses`. Since a cusp form has `ak f 0 = 0`,
the old generating set then contained `(1, 0)`. The identity of `J`
was in the annihilator and its saturation (take multiplier 1). The
killing half of `PrintQuotient` therefore forced `ν = 0`, contradicting
surjectivity onto the printed `A` of dimension `[K_f : ℚ] ≥ 1`.
This counterexample concerns the old definition only.

**ON THE SPOT (provenance (c)).** Index zero is an artifact of the Lean
family. `printRing_update_zero` checks independence of its dummy value.
`printRing_eq_closure_of_zero` checks that the omitted pair under
`HeckeRelations.zero` is the zero of the product ring, hence already in
the closure. For every positive `n`, `XiAction` requires that `ξ n`
satisfy `IsXi` and that every operator satisfying that formula be equal
to `ξ n`. A formula that admits arbitrary operators cannot supply an
arbitrary generator through this pinning. The closed Hecke bridge supplies
the family, including its value at 1.

The closure uses finite ring operations on the positive pairs and the
product ring's identity. Clause (ii) puts these generators in
`compatRing ν θ`, which is a subring. Thus all closure elements, including
any cancellations between Hecke expressions, satisfy the intertwining
relation. An annihilating pair has second coordinate zero; injectivity of
rationalization and cancellation of positive integer multiplication in
`Hom(J,A)` make its composite with `ν` zero. Saturation preserves the
killing condition and the scheme theoretic image family by
`kills_sat_iff` and `image_family_sat`. The new killing lemma checks this
directly without any assumption about `ξ 0` or a separate Hecke bridge.
This rules out a new generator that would make the killing half fail.
The saturation is the integral part of the rational annihilator:
clearing a positive denominator in a rational combination with zero
eigenvalue gives a pair in the integral ring with zero second coordinate.

For a printed triple, (ii) therefore gives `C ⊆ ker ν`. The construction
on p. 526 produces `J/C` with dimension `[K_f : ℚ]`; factoring `ν`
through it gives a surjective map of equal dimension, hence an isogeny.
The isogeny criterion in (i) makes that map an isomorphism. Consequently
every printed triple presents `J/C`, and the unique factorization in
`PrintQuotient` is its universal property. Neither compatibility with
`θ` for maps out of the quotient nor a choice of quotient object is
required by the named construction input. This check explains the scope
of the input; it is not a Lean proof of the input. Proving it requires
the general construction of an abelian variety quotient by an abelian
subvariety and the dimension calculation for this `C`. The smallest
input needed here is the stated universal property for printed triples;
with the printed clauses it suffices for the exact quotient row.

## Lean statements

All new names are in `ShimuraSteps`, in
[`ShimuraRing0.lean`](../../ZInQKernel/Contrib/OneProof/ShimuraRing0.lean).
The two propositions share the binders for `N ≥ 2`, weight-two newform
`f` with character `χ` on Γ₁(N), the integral curve model with generators
`jX, tX`, the pointed Jacobian with Abel–Jacobi map, and the family `ξ`
with `XiAction`.

| Definition or theorem | Statement |
| --- | --- |
| `ShimuraThm1Printed : Prop` | Under those binders, `FiniteDimensional ℚ (coeffField f)` and a triple `(A, ν, θ)` satisfying `PrintedClauses ξ f ν θ` (surjectivity with connected kernel, rational intertwining at each positive index, dimension equal to the coefficient degree). For every other such triple `(A', ν', θ')` there is `ψ : AbVar.Hom A A'` with `IsIso ψ.hom`, with no condition on the composite with `ν`. |
| `ShimuraQuotientByC : Prop` | Under the same binders, for every triple `(A, ν, θ)`, `PrintedClauses ξ f ν θ → PrintQuotient ξ f ν`. Proof content, p. 526, provenance (c), GLUE. |
| `printRing_update_zero` | For every `t : AbVar.End J`, `printRing (Function.update ξ 0 t) f = printRing ξ f`. |
| `printRing_eq_closure_of_zero` | If `ξ 0 = 0`, then `printRing ξ f = Subring.closure (Set.range fun n : ℕ => (ξ n, ak f n))`. |
| `kills_print_of_printedClauses` | `PrintedClauses ξ f ν θ → Kills (Sat (annihilator (printRing ξ f))) ν`. |
| `asPrinted_of_split` | `ShimuraThm1Printed → ShimuraQuotientByC → ShimuraThm1AsPrinted`. |
| `printed_of_asPrinted` | `ShimuraThm1AsPrinted → ShimuraThm1Printed`. |
| `shimuraThm1Af_of_split` | `ShimuraThm1Printed → ShimuraQuotientByC → ShimuraHeckeRelations → SameDimSurjectiveFinite → R16Thm1b.ShimuraThm1Af`. |
| `shimuraThm1Af_of_split_closed` | `ShimuraThm1Printed → ShimuraQuotientByC → R16Thm1b.ShimuraThm1Af`. |

**ON THE SPOT (provenance (c)).** The two packaging proofs add or forget
the construction conjunct and preserve the same witness and uniqueness
clause. The split reduction passes that witness to the existing quotient
comparison. The closed reduction uses `shimuraHeckeRelations` from
`pointDictionary` and the existing `sameDimSurjectiveFinite` theorem.
The earlier comparisons with the kernel's Hecke generators and its
commuting uniqueness clause remain the existing Lean glue.

## Existing files edited

- `ZInQKernel/Contrib/OneProof/ShimuraSteps.lean`: positive-index
  `printRing`, updated ring and quotient docstrings, `print_annihilator_eq`
  proof using the normalized zero pair, and the reduction docstring.
- `ZInQKernel/Contrib/OneProof/SameDimFinite.lean`: reduction docstring only.
- `ZInQKernel/Contrib/OneProof/ShimuraOrbits.lean`: reduction docstring only.

The existing propositions and consumer signatures are unchanged. The
frozen target and `OPEN.md` are untouched. The sole printed form proposed
here is `ShimuraThm1Printed`; no new leaf rating, fold, or count change
is claimed.

## Known issues

- The manuscript cites Theorem 1 for the quotient. The statement on
  pp. 525–526 gives the clauses used here and uniqueness. The
  identification `ker ν = C` is in the proof on p. 526. The historical
  name `ShimuraThm1AsPrinted` includes that extra construction.
- The conjugate form in the p. 526 eigenform equation has `a_n^σ f` on
  the right of `f_σ | T_n`; it should have `a_n^σ f_σ`. This does not
  affect clauses (i)–(iii). The locators here are from the reviewer's
  reading and the recorded source audit.

## Manuscript check

| Lines in `diophantine_zq.tex` | Verdict | Finding |
| --- | --- | --- |
| L770–773, base Lean encoding of the construction | error | The zero-index pair could force the surjective quotient map to be zero. This was an error in the inherited Lean encoding, now repaired. |
| L770–771, quotient construction | OK | The citation reaches Shimura's construction on p. 526. The identification `ker ν = C` is in the proof. |
| L770–773, quotient row used by the formalization | gap filled | The split exposes the proof's universal property as its own input; the existing Lean comparison transports it and derives compatible uniqueness. |
| L771–773, Euler identity, choice of Tate constituent and dual | unverified | These claims are outside the quotient row and were not checked here. |
| L11053–11057, bibliography | OK | The citation names the paper, Theorem 1 and DOI identified by the reviewer. |
