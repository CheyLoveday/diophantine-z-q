# t5-glue results log

## Setup
- `.lake/build`, `lean/.lake/build` reflink-copied from ~/dzq-check2 (HEAD 13fe43c4; vs this base only
  `ZInQKernel/OneProof/TYZSplit.lean` differs, +6 lines). Import of `ZInQKernel.Contrib.TYZChain.ModFn`: ~75 s.

## Step 1: Elliptic.lean (Mathlib only) — COMPILED, 0 errors, 0 warnings, no sorry (~35 s)
- §0 verbatim copies of tyz-split T5.lean §1: `linIndep_one_tau`, `pp`, `discL`, `jL`, `weber`, `modCoord`.
- §1 `IsScale P Q c` (c ≠ 0, Λ_P = c·Λ_Q): `IsScale.G` (G_n(P) = c⁻ⁿG_n(Q)), `.g₂`, `.g₃`, `.discL`,
  `.weierstrassP` (℘_P(cz) = c⁻²℘_Q(z)), `.derivWeierstrassP` (c⁻³), `.jL` (j(P) = j(Q)),
  `.weber` (h_P(cz) = h_Q(z)).
- §2 `IsConjModel σ P Q μ` (μ ≠ 0, σg₂(P) = μ⁴g₂(Q), σg₃(P) = μ⁶g₃(Q)), σ : ℂ →+* ℂ:
  `.discL`, `.jL` (σ j(P) = j(Q)), `.weber` (σ℘_P(z) = μ²℘_Q(w) ⇒ σ h_P(z) = h_Q(w)),
  `exists_conjModel_of_jL` (Δ(P), Δ(Q) ≠ 0, σ j(P) = j(Q) ⇒ ∃ μ),
  `IsConjModel.adjust` (Δ(Q) ≠ 0, σ h_P(z) = h_Q(w) ⇒ ∃ μ' model with σ℘_P(z) = μ'²℘_Q(w); μ' = μ, iμ, ωμ, ω²μ),
  `IsConjModel.deriv_sign` (σ℘'_P(z) = ±μ³℘'_Q(w), from Mathlib's `derivWeierstrassP_sq`).
