# theta-glue (2026-11-14)

**Result.** theta-split's Route 1 statements for `thetaRatiosAlgebraic`:
- `ThetaEightSquare` (`Σθ¹⁶ = (Σθ⁸)²/4` on 𝔥₂) is **PROVED in Lean** for a verbatim copy. The proof
  uses no modular-form theory:
  - absolute convergence of the genus-2 theta series;
  - the duplication formula `θ[a;b](Ω)² = Σ_c ±θ[c;0](2Ω)θ[c+a;0](2Ω)`, proved by an explicit lattice
    change of variables;
  - a degree-16 `ring` identity.
- `QMThetaSymmetricCurve` is **reduced** (proved: `qmThetaSymmetricCurve_of_alg59`) to:
  - one composite LEAF `LinYangThetaCurve`. Along `Ω(τ)`, `ψ₄ψ₆ = 2¹²3⁵χ₁₀` and
    `ψ₄³+ψ₆² = 2¹²3⁶χ₁₂`, in Igusa's theta expressions. This is Lin–Yang Ex. 29 with `j` eliminated,
    checked at 80 digits on the Lean curve.
  - five closed polynomial identities `IgusaAlg 5..9` in four variables (GLUE, no analysis). All are
    VERIFIED by exact symbolic expansion; none is proved in Lean.
  - `IgusaAlg 3` and `IgusaAlg 4` are **proved in Lean** by `ring`.

  Igusa's structure theorem is not needed as a leaf. The global identities
  `e_k(θ⁸) = P_k(ψ₄,ψ₆,χ₁₀,χ₁₂)` follow from the duplication formula plus algebra. Substituting
  Lin–Yang's vector gives theta-split's numerically fitted `qmR 3..9` exactly.

**What compiles.** `scratch/theta-glue/ThetaGlue.lean` (imports TailA): no `sorry`, all
`#print axioms` standard. It takes 6 min 23 s with a peak of 23.5 GB, almost entirely from §7
`igusaAlg4`; drop §7 for an 18 s check. Also compiling: `Dup.lean`, `Alg3.lean`, `Alg4.lean`.

**Exact algebra** (`scratch/theta-glue/py/`, pure Python; no sympy on the host):
- `ψ₆` signs are forced by Sp₄(ℤ)-invariance in second-order thetas;
- the `χ₁₂` Göpel expression equals the form with `χ₁₂|diag = Δ⊗Δ`;
- invariant dimensions match Igusa's;
- `P_k` were found and all seven identities verified.

**What remains.**
- `IgusaAlg 5..9` in Lean (degrees 40-72). Every method tried exceeded 24 GB or was too slow: one-shot
  `ring`, a DP over `ring_nf`, a split proof with convolution, `grind`, and kernel reflection. This is an
  engineering obstacle, not a mathematical one.
- The leaf is composite, in the same style as `PkgI1.QMHauptmodul`. A universal form over
  QM-structured `Ω` was not attempted.
- Report: docs/research/theta-glue.md.
