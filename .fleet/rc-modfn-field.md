# rc-modfn-field

Scoped stop: `ComplexCuspClassification N`. A complex Laurent series realizing a Γ₀(N)-invariant meromorphic function, with meromorphic germs at every cusp, must belong to the specified embedded field ℂ(j(q), j(q^N)). The [report](../docs/research/rc-modfn-field.md) states the exact proposition. The missing theory is the general complex level-one classification with interior poles, its use on the coefficients of the coset orbit polynomial, and the comparison of the analytic modular function field with its Laurent image. In the proposed orbit argument those coefficients are rational functions of j; a polynomial claim is false in the presence of interior poles. The report also records the inherited Milne citation gap at tex 1788.

All 12 files under `ZInQKernel/Contrib/OneProof/RC/ModFnField/` compile. The 55 theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`. No print was added. The coordinates at the fixed nonzero rational scale have rational Laurent expansions with pole bounds two and three, satisfy the formal Weierstrass equation, and have convergent meromorphic Laurent expansions at every cusp. Rational descent and the algebraic degree comparison are proved.

Conditional on the complex converse, the exact bilateral `HasSum` statement holds in the specified rational field and the generic coordinates give a dominant ℚ-morphism out of a supplied `X0Model N`. The comparison of the full projective values, including the identity, still precedes the existing at-scale consumers. Algebraic cusp specialization and the CM source data remain separate.

Final proof/report SHA (parent of this handoff): `8f430a568de73f1e81d8e0623c29c48a9a77cf62`. The handoff commit SHA is given by `git log -1 --format=%H -- .fleet/rc-modfn-field.md`.
