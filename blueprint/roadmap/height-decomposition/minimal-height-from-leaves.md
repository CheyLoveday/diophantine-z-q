---
article_id: af_78010d6fcd0139911e3a7f29
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HDec.HSyn.sixContactMin_of_open107
---

# The minimal height hypothesis from twenty-nine statements

The [minimal height hypothesis](../multiplication/certificate/six-contact-min.md) follows from the
twenty-nine statements of this chapter taken together: theorems from the literature, grouped by the
theory they come from ([Shimura curves of discriminant 6](shimura-curves/README.md),
[complex multiplication](cm-fibres/README.md), [abelian varieties](abelian-varieties/README.md),
[Néron models, semistable reduction and monodromy](neron-models/README.md),
[Faltings 1983 and Faltings heights](heights/README.md),
[p-adic Hodge theory](p-adic-hodge/README.md),
[Galois representations of modular forms](modular-galois/README.md)). Of the twenty-nine statements
from the literature, nineteen are published statements, some of them specialized or weakened; and
ten are consequences of published theorems, which take further theorems to reach from the print. The
project's strict convention, which counts a published statement only once its reading against the
print and its review are complete and find it in its printed form, counts seventeen of the
twenty-nine as published (eighteen without the strictest reading of one flagged statement). None of
the twenty-nine is proved here.

The proof follows the manuscript's proof of its Theorem 4.1 at the one instance the main theorem
uses, which the project has split into named steps, each proved from these statements and the steps
before it. Among them are the existence of an unramified vertical prime above each prime $p>324$ in
the Hecke cover, along the steps of the project's Lemma NV; the inequalities between heights, from
the analytic uniformization, the existence of Néron models, the bounds of the section on heights and
the results on semistable reduction and Néron models; the Galois representation of a newform as a
subrepresentation of the Tate module of $J_1(N)$, with its semisimplicity and its conductor; and the
last stretch, from the level bound, the theta point and the height inequalities to the minimal
height hypothesis.

## Depends on

- [The minimal height hypothesis](../multiplication/certificate/six-contact-min.md)

## Proof depends on

- [Pazuki's comparison of the theta height with the Faltings height](heights/pazuki-bound.md)
- [The Deligne–Serre theorem](modular-galois/deligne-serre.md)
- [Frobenius on the Tate module of Shimura's abelian variety](modular-galois/shimura-af-frobenius.md)
- [Hodge–Tate weights of the representation of a newform](modular-galois/kato-hodge-tate-weights.md)
- [Javanpeykar's bound for curves with a Belyi map](heights/javanpeykar-bound.md)
- [Carayol's theorem on the conductor](modular-galois/carayol-conductor.md)
- [The discriminant formula for the Faltings height of an elliptic curve](cm-fibres/elliptic-height-discriminant-formula.md)
- [Fowler's bound for discriminants of bounded class number](cm-fibres/fowler-class-number-bound.md)
- [Grothendieck's semistable reduction theorem](neron-models/semistable-reduction-theorem.md)
- [Berger's theorem: de Rham representations are potentially semistable](p-adic-hodge/berger-de-rham-potentially-semistable.md)
- [Pan's Fontaine–Mazur theorem](p-adic-hodge/pan-fontaine-mazur.md)
- [The lower bound for the Faltings height](heights/bost-lower-bound.md)
- [The isogeny theorem of Gaudron and Rémond](heights/gaudron-remond-isogeny-bound.md)
- [The locus of geometrically connected fibres](neron-models/ega-geometrically-connected-fibres.md)
- [Buzzard's moduli problem at level V₁(5) is a projective curve over ℤ[1/30]](shimura-curves/buzzard-v15-moduli-problem.md)
- [Multiplication by 3 on an abelian scheme is finite étale](abelian-varieties/milne-multiplication-by-3.md)
- [The n-torsion of an abelian surface has n⁴ points](abelian-varieties/milne-torsion-count.md)
- [An automorphism fixing a full level-5 structure is the identity](shimura-curves/buzzard-lemma-2-2-level-5.md)
- [Endomorphisms agreeing on l-power torsion are equal](abelian-varieties/milne-tate-module-injectivity.md)
- [Morphisms of abelian schemes fixing zero are homomorphisms](abelian-varieties/milne-zero-preserving-homomorphism.md)
- [A scheme smooth over a normal base is normal](shimura-curves/smooth-over-normal-is-normal.md)
- [Abelian schemes over a normal base are projective](abelian-varieties/abelian-schemes-over-normal-bases-are-projective.md)
- [Multiplication by 5 on an abelian scheme is finite étale](abelian-varieties/milne-multiplication-by-5.md)
- [Complex abelian surfaces with quaternionic multiplication, in lattice form](shimura-curves/complex-qm-abelian-surfaces-voight.md)
- [Shimura's canonical model at level three and the reciprocity law at CM points](shimura-curves/canonical-model-level-three-reciprocity.md)
- [The fine moduli scheme at level three is Shimura's canonical model](shimura-curves/fine-moduli-scheme-is-canonical-model.md)
- [The Hodge–Tate theorem of Tate and Raynaud for abelian varieties](p-adic-hodge/fontaine-hodge-tate-abelian.md)
- [Every abelian variety is projective](abelian-varieties/abelian-varieties-are-projective.md)
- [Colmez's p-adic periods of an abelian variety, on a proper model](p-adic-hodge/colmez-periods-on-a-proper-model.md)

## Sources

- [The decomposition](../../sources/height-decomposition-locators.md#the-decomposition)
