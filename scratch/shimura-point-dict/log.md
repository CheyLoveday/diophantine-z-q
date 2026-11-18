# Shimura analytic points: results log

- VERIFIED: the fixed point predicate tests finite punctured limits of quotients of integral polynomials in the two generators. It quantifies over all complex points of the rational curve; the image point on the rational scheme need not be closed.
- VERIFIED: Mathlib's meromorphic order criterion gives a finite limit for nonnegative order. Negative order gives inverse limit zero. The finite germs in the image of a field form a valuation subring, including when the valuation is trivial.
- VERIFIED: `ShimuraPointDictGerms.lean` compiles with `lake env lean`. Axiom scan for all ten theorems: `propext`, `Classical.choice`, `Quot.sound` only.
- VERIFIED (source): the vendored smooth-curve dimension module has `Scheme.valuationRing_stalk`; Mathlib has the proper and separated valuative criteria and the fraction-field instance for integral scheme stalks.
