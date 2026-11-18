# Nonzero coefficients and integral old Kummer models

## Outcome

**A remains open.** The nonzero coefficient modules, cancellation core, finite
coefficient setting, nonempty new-place set, and genuine full-condition short
exact sequence are constructed. They are not an `Identification3` instance.

**B: the literal model equality is constructed** for integral equations with
`a₁ = a₃ = 0`, at every finite place. In particular, the construction applies to
every integer twist of the manuscript curve `E_ℓ`. Its equality is used in the
genuine residual Kummer count, both at odd places and at places above two.

The supplied integration base was `3b0ffbb9`. Only new files were written.
No existing source file was edited, and no commit, checkout, package build,
or dependency update was performed.

## Proof files

- `ZInQKernel/Contrib/RC53Assist/NonzeroIdentification/NonzeroTriangle.lean`
  - Size: 9,631 bytes.
  - SHA-256: `507b471e4b2955b6b5f46c30e19cc9b38e822191d541f0bce0123b851b6a15f5`.
  - Ten theorems; twenty declarations, each with a kind and locator.
- `ZInQKernel/Contrib/RC53Assist/MattuckModel/IntegralTwist.lean`
  - Size: 12,819 bytes.
  - SHA-256: `6eec4b0260d4808d2ca0f728568fb942a319d64b5f0eb45211ac686ab1ec1538`.
  - Eleven theorems; fourteen declarations, each with a kind and locator.

## Exact statements and axiom output

The following files contain the complete compiler-printed statements, with all
parameters and universe levels displayed, immediately followed by the output
of `#print axioms` for each theorem:

- [A: ten theorem statements and axiom reports](../NonzeroIdentification/TheoremsAndAxioms.txt)
  - Size: 9,447 bytes.
  - SHA-256: `f35959c1397686eac5721cb26c37d8a68a5621a972caec7f90224122dbcdf64b`.
- [B: eleven theorem statements and axiom reports](TheoremsAndAxioms.txt)
  - Size: 14,361 bytes.
  - SHA-256: `d1cb3cec31788a806a26a26b31343a5e4dc7f3037205ec47b226c660b935cb83`.

The proof files and the separate scratch audits compiled successfully with
version 4.35.0 under the prescribed single-file invocation. All twenty-one
theorem reports contain only the standard axioms:

```
propext
Classical.choice
Quot.sound
```

For B, `integralTwist_map` uses only `propext`, and `baseChange_tower` uses
`propext` and `Quot.sound`. Every other theorem in the two proof files has the
three-axiom report above. The scratch files were removed after their output
was saved. Neither final proof file contains checking or printing commands.

## A: what is proved

The explicit field is `CyclotomicField 4 ℚ`. The old support consists of places
above two, and one place above three is added. The coefficient modules are

```
FamilyCoefficient b = TrivMod (GKS KA S₂') (MonoidAlgebra OO (SignGroup b))
AugmentationCoefficient = TrivMod (GKS KA S₂) (ZMod 2)
```

Both are nontrivial, with trivial Galois action and discrete topology. Constant
cochains give an injection of the coefficient module into every nonnegative
continuous cochain term. In particular, the degreewise-zero global premise of
the earlier zero-coefficient construction is formally proved to fail here.

The main partial result, with the namespace opened, is exactly:

```lean
theorem nonzero_data_witness (b : ℕ) :
    Nonempty (FullCore (NewPlaces KA S₂ S₂') b 0 0 0 0) ∧
    Nontrivial (FamilyCoefficient b) ∧ Nontrivial AugmentationCoefficient ∧
    NekovarFiniteSetting KA S₂ 2 (ZMod 2) ∧ Nonempty (NewPlaces KA S₂ S₂') ∧
    (galoisFullSES KA hS₂ (ZMod 2) AugmentationCoefficient ψurB hψurB
      augmentationConditions).ShortExact
```

This theorem does not identify a finite model with a genuine Selmer complex.
The current relaxed conditions are a nonzero-data demonstration, not a proposed
solution of all the identification fields.

### Remaining for A

A full nonzero `Identification3` still requires appropriate local conditions
and the finite-model comparisons `ψf`, `ψ0`, and `ψold`, their quasi-isomorphy,
the inclusion square, and the genuine tame comparison. No such field is
postulated or claimed to have been discharged by this contribution.

## B: what is proved

In the exact source statement, `hC` is an equality of Weierstrass equations:

```lean
C.baseChange (v.1.adicCompletion K) = localTwist W h v.1
```

It is not a quasi-isomorphism of local complexes. For an integral equation
with `a₁ = a₃ = 0`, the denominator-free equation

```
[0, h*a₂, 0, h^2*a₄, h^3*a₆]
```

has generic fibre equal to the actual local twist. The exact main equality is:

```lean
theorem hC_localIntegralTwist (W : WeierstrassCurve (𝓞 K)) (h : 𝓞 K)
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (v : HeightOneSpectrum (𝓞 K)) :
    (localIntegralTwist W h v).baseChange (v.adicCompletion K) =
      localTwist (W.baseChange K) (algebraMap (𝓞 K) K h) v
```

For the manuscript curve the integral hypotheses are constructed, not assumed:

```lean
theorem hC_Ecurve_integer (ℓ : ℕ) (h : ℤ) (v : HeightOneSpectrum (𝓞 K)) :
    (localIntegralTwist (integralEcurve (K := K) ℓ) (h : 𝓞 K) v).baseChange
        (v.adicCompletion K) =
      localTwist ((ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).baseChange K) (h : K) v
```

The three count theorems consume this constructed equality and the actual
`actualKummerAt` object at level one:

- `oldKummer_count_integralTwist`: the exponent is the genuine table's old
  Kummer dimension of the constructed local model.
- `oldKummer_count_integralTwist_odd`: with rational two-torsion of order four,
  the product of the two cohomology orders is `2^4`; point-quotient finiteness is
  proved rather than assumed.
- `oldKummer_count_integralTwist_two`: under the corresponding place-above-two
  hypothesis and rational two-torsion of order four, the product is
  `2^(4 + [K_v : ℚ₂])`; point-quotient finiteness is again proved.

The original square-root, ellipticity, finite-level full-torsion, and local
character hypotheses of the actual Kummer condition are retained. No new
printed arithmetic premise, and no premise equivalent to the count, is added.

### Remaining scope for B

An independently prescribed arbitrary local model `C` must still be linked to
the constructed equation; the contribution does not assert that every `C` has
the same generic fibre. Nonintegral twisting parameters or equations not in
this short form may require a change of variables rather than literal equality.
No all-level comparison between a finite free presentation and the completed
point module is asserted here.

## Source and policy checks

Every declaration has a mathematical kind and a source locator. The direct
proof-file scan found no forbidden proof placeholders, new axioms, evaluation
commands, syntax extensions, broad import, or private identifiers or external
filesystem paths. The only explicit heartbeat limit is 600,000.

Mathematical locators: `diophantine_zq.tex`, lines 3413–3438, 4544–4573, and
5234–5238; `ClearingComplex/FullConditionIdentification.lean`, fields 220–297;
`OldKummer/Mattuck.lean`, lines 89–135; `RC/KummerMaps/Iota.lean`, lines 71–92
and 313–325; `Mattuck/Two.lean`, lines 118–152. These are constructions and
uses of already proved results, not new assumptions attributed to the literature.
