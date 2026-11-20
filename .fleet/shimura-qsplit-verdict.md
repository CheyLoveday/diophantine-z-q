# Error verdict: the proposed split admits a spurious zero-index generator

At `diophantine_zq.tex` L770–773 (citation L11053–11057), the manuscript uses
Shimura's quotient construction. The formal claim under review is that
`PrintedClauses ξ f ν θ` implies the existing `PrintQuotient ξ f ν` under
the binders through `XiAction`, faithfully expressing that construction.
The error is in that Lean formulation. Identifying `ker ν = C` for the
annihilator-image subvariety is in the proof on p. 526, outside the printed
statement of Theorem 1.

In `ZInQKernel/Contrib/OneProof/ShimuraSteps.lean`, both `XiAction` (L65–67)
and `PrintedClauses` (L633–637) inspect `ξ n` only for `0 < n`.
Given a genuine printed triple, replace `ξ 0` by the identity of `J` and
leave every positive index fixed. Both hypotheses still hold, and the
positive-index Hecke ring defining Shimura's `C` is unchanged. But
`printRing` (L375–377) includes the generator at `n = 0`. The cusp form
has `ak f 0 = 0` by L144 and L193–197. Consequently the new ring contains
`(1, 0)`. Its annihilator and its saturation contain `1` (use multiplier
`1`). The killing half of `PrintQuotient` (L353–354, L383–386) now forces
`ν = 0`. A zero map cannot be surjective onto the printed `A`, whose
dimension is the positive field degree `[K_f : ℚ]`.

Thus even a genuine quotient by Shimura's `C` fails the proposed conclusion
after an allowed change of dummy value. The existing
`ShimuraThm1AsPrinted` (L681–693) also quantifies over that value, so
normalizing only the new input would not recover it as requested.
`HeckeRelations.zero` (L53) supplies the normalization in the existing
Hecke comparison; the proposed hypotheses do not include it.
