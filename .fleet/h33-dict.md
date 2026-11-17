# h33-dict (2026-11-16)

**Result: `h33` (TYZSplit.TYZThm33) is discharged by a printed TYZ Theorem 3.3, and every dictionary step is a
Lean proof.** `ZInQKernel/Contrib/OneProof/TYZThm33.lean` proves
`H33Dict.tyzThm33_of_printed (hCM : T5Glue.ShimuraMainCM) (h : TYZThm33Printed) : TYZSplit.TYZThm33`.
`hCM` is already an argument of `frozenTarget`, so the only new leaf is `TYZThm33Printed`.

**The new leaf.** `TYZThm33Printed` is TYZ Thm 3.3 for every identification `i₀ : (X₀(32), ∞) ≅ (A, O)` over ℚ.
`i₀` is given by its pullbacks in ℚ(X₀(32)) (`IsX0Identification`), and `ε` is chosen after `Φ`, as printed. Rated
**printed form** (published, LEAF). An independent model review found it faithful or weaker, not vacuous, and with
no dependence on the eta model.

**Fix (1), phiC vs i₀.** Lean proves the eta model `(x, y)` is an identification. New here: `x = O(e^{4π Im τ})` at
`∞`, and `x` is bounded at every cusp with `32 ∤ c`. These are Ligozat's orders, from an exact Hermite
decomposition, and they hold for all `γ ∈ SL₂(ℤ)`.

**Fix (2), ε before Φ.** TYZ Prop 3.2(4), in its used form, is proved from hCM's CM inputs: glue KER for n ≡ 5,
`z_n ∈ A(H_n)` for n ≡ 7. No Prop 3.2(4) leaf is needed.

**What compiles.**
- `lake build` of the module succeeds.
- `#discharges` gives `DISCHARGES [h33] by tyzThm33_of_printed, still assumes [T5Glue.ShimuraMainCM, TYZThm33Printed]`.
  The axioms are standard.
- The manual fold (`scratch/h33-dict/FoldCheck.lean`) compiles.
- `h33` is a plain argument of `frozenTarget`, so `autofold.py` refuses it. The manual-fold instructions are in
  `scratch/h33-dict/autofold.json`.

**What remains.**
- The readings are of arXiv v1; the journal version has not been checked.
- The TYZ TeX was missing from the host on 11-16, so h33-dict did not re-read it.
- Still readings, not Lean (inherited from tyz-split and h33-sign): `X_U ≅ X₀(32)_{ℚ(i)}` with `P_n ↦ τ_n`, and
  `f₀∘[i] = [i]∘f₀` with the sign of `[i]`.
- No human review of the paper.

Report: `docs/research/h33-dict.md`.
