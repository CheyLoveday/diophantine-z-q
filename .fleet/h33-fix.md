# h33-fix (2026-11-17)

**Result: `h33` is discharged by a printed-form leaf, `ZInQ.H33Fix.TYZThm33Alg`, over TYZ's algebraic
identification `i₀`. Target met: h33 goes GLUE → LEAF (−1 GLUE), and no field is added.**

**The new leaf.** In `TYZThm33Alg`, `i₀ : (X₀(32), ∞) ≅ (A, O)` is an isomorphism over ℚ, given by its pull-back
`φ = i₀^* : ℚ(A) → ℚ(X₀(32))`:
- `φ` is bijective and `ord_q φ(x) < 0`;
- `ℚ(X₀(32)) = ℚ(j, j₃₂) ⊂ ℚ((q))` is the vendored FLT field, the same one gzopt-dict's GZ leaf uses;
- `ℚ(A)` is Mathlib's function field.

It is evaluated at the points `P_n` through the holomorphic `X, Y` on ℍ with q-expansions `φ(x), φ(y)`. These are
unique (`eq_of_hasQExp`), so they are determined by `i₀`.

**The deciding step of the review is now a Lean proof.** The review's objection was that h33-dict read `i₀` through
`IsRatModFn`. The fix is `isX0IsoAlg_eta`: the eta model's `φ^*` is onto `ℚ(j, j₃₂)`. Proof:
- `E₄` and `E₆` in theta constants, from Mathlib's level-one rank-one spaces;
- `j = 1728E₄³/(E₄³−E₆²)`;
- Landen's identities plus the kernel's theta forms of `x, y` give `j(τ)` and `j(32τ)` as rational functions of
  `x, y`;
- these identities pass to `ℚ((q))` by uniqueness of q-expansions.

**What compiles.**
- `ZInQKernel/Contrib/OneProof/TYZThm33Alg.lean` and its helper `TYZThm33Alg/ThetaJ.lean` build with `lake build`
  (about 3 min).
- `#discharges` gives `DISCHARGES [h33] by ZInQ.H33Fix.tyzThm33_of_alg, still assumes [T5Glue.ShimuraMainCM,
  TYZThm33Alg]`. `ShimuraMainCM` comes from the existing `hCM` via `shimuraMainCM_of_printed`. Axioms are standard.
- The manual fold (`scratch/h33-fix/FoldCheck.lean`) compiles and is `rfl`-equal to the old theorem. It also needs
  h33-dict's `TYZThm33.lean` to be merged.

**What remains.** These are readings, not Lean: D1 (function fields ≅ curves, the same step as for hGZ),
`X_U ≅ X₀(32)_{ℚ(i)}` with `P_n ↦ τ_n`, the sign of `[i]`, and the model `y² = x³+4x`. The journal version has not
been checked, and no human has reviewed the paper.

Report: `docs/research/h33-fix.md`. The fold spec is `scratch/h33-fix/autofold.json`, and the kinds row is
`scratch/h33-fix/kinds-row.tsv`.
