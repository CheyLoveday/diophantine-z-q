# Results log

- Base: `861030447a55b625cedef42d48a8de57d9f6d159`.
- App G 10288–10325: attainment at 1 is the empty reading; a whole-filter lower bound and the subsequent trace argument are separate.
- App G 10375–10386: the determinant identity proves the needed integrality at index p without the term-by-term (G.4b) expansion.
- `TraceLimits.buildConstituentModel` is a fixed-avoidance construction; added-prime packets may ramify at their added primes. It cannot build the genuine family as stated.
- Tex 10393–10404: (G.4b)'s old support must mean the full stationary support before adding the tested prime, not the pre-transport support from tex 10293; otherwise extra sieve primes are missing from the case split.
- `Valuation.lean`: successful serial compile after fixing cast elaboration in `revGen_eq_one_iff`.
- `Sieve.lean`: serial compile passed; coefficients at squarefree indices, exact normalization at 1, sieve preservation of (E.12), and transport of the lower bound from the old unit.
- `Density.lean`: serial compile passed; support equality and pointwise good-prime level exclusion; finite-field bridge and both density consumers.
- `Fresh.lean`: serial compile passed; joint finite-field match for the type and the coefficient at p², including the dyadic condition on the matched product.
- `Seed.lean`: serial compile passed; determinant-block argument and shell identity give `8 ∣ p + 1 - apk W p`, hence the conditional `KSplitSeed` for `RevGen S G.r`.
- `Axioms.lean`: serial audit passed for all 23 declarations; dependencies are `propext`, `Classical.choice`, and `Quot.sound` only.
