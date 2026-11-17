# aftate-fix2 (fleet summary)

**Result.** `r16CoreY` is discharged from three new leaves over genuine definitions, plus the existing LEAF
`X1Igusa.IgusaGL2DS` and the bundle's `mumfordTorsionAlgClosed`:
`AfTateLam.r16CoreY_of_printed : HeckeJ1DS → AfShimura → AfTateDSLambda → IgusaGL2DS → MumfordTorsionAlgClosed → R16CoreY`
(standard axioms). This replaces aftate-or's `AfTateDSOr`, which the review rated GLUE.

- (1) **`A_f` is universal.** `AfTateDSLambda` holds for every `(A, π, θ)` that is DS's
  `A_f = J₁(N)/I_f J₁(N)` with its `K_f`-action. The definitions:
  - `T_p` and `⟨d⟩` are the endomorphisms of `J` with DS's double-coset action on divisor classes of the
    points `x_τ ∈ X(ℂ)` (`IsHeckeT`, `IsDiamond`, `AtTau`).
  - `I_f` = ker(`T_p ↦ a_p`, `⟨d⟩ ↦ χ(d)`).
  - `A_f` is the universal quotient killing `I_f J`.

  Existence is two printed leaves: `HeckeJ1DS` (DS §6.3/§7.9) and `AfShimura` (Shimura 1973 Thm 1, read by the
  locator audit).
- (3) **Over `K_{f,λ}`.** The leaf is stated for every place `λ ∣ ℓ` (Mathlib `adicCompletion`, Tau Ceti completion
  map), on `V_λ = K_λ ⊗_{ℚ_ℓ⊗K_f} V_ℓ(A)`. The glue to the kernel's `ι`-components is proved by base change
  (`AfTateLam.component`); the semi-local decomposition is not needed.
- (2) **Determinant: not resolvable in the tree.** The leaf states the characteristic polynomial. Under a
  "satisfies" reading of DS 9.5.4, the determinant would need the Weil pairing, and the tree has none on
  abelian varieties. The consumer uses the determinant, so the clause cannot be dropped. `afTateDSLambda` is
  flagged "reading risk"; a statement check of DS 9.5.4 decides it. A fallback pair is proved but not folded:
  `AfTateDSLambdaSat` (dim 2 + "satisfies") with `AfDetLambda` (`det ρ_{f,λ}(Frob_p) = χ(p)p`) implies the leaf
  (`dsLambda_of_sat_det`). Also proved: `AfTateDSTensor` (the `ℚ_ℓ ⊗ K_f` form) implies the leaf
  (`dsLambda_of_tensor`), so the leaf follows from either form of the print.

**Compiles (VERIFIED).**
- `lake build +Main +Discharges +ZInQKernel.Contrib.OneProof.AfTateLambda`: OK (13704 jobs).
- `#discharges`: `DISCHARGES [OpenResearchLeaves26.r16CoreY] by AfTateLam.r16CoreY_of_printed`, standard axioms.
- Fold dry run (`scratch/aftate-fix2/autofold.json`): strict 34/11 → 38/10 (GLUE −1); `sixContactMin_of_open36`
  has standard axioms. If `afTateDSLambda` is re-flagged "pending reading", the count is 37/11.

**Remains.**
- The DS 9.5.4 wording (statement check).
- The locators of `heckeJ1DS` (DS §6.3/§7.9) and `afTateDSLambda` are UNVERIFIED (no network).
- The uniqueness of `x_τ` and of the Hecke endomorphisms is an argument, not formalized.

Report: docs/research/aftate-fix2.md. Contribution: ZInQKernel/Contrib/OneProof/AfTateLambda.lean.
