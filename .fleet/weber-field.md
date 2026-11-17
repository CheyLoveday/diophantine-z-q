# weber-field (2026-11-16)

**Result: `X1Igusa.Weber.WeberFieldComparison` is proved in Lean, with no hypotheses and standard axioms.**
- Theorem: `X1Igusa.Weber.weberFieldComparison`, in the new file `ZInQKernel/Contrib/OneProof/WeberField.lean`.
- The statement is x1-igusa's, copied verbatim with `wOf`, `evAn`, `evAlg`.
- It is the function-field comparison `ℚ(j, f₁) = ℚ(j)(x(P))`: for `N ≥ 2`, some point `P` of exact order `N` on the
  kernel's `E_j` has the same ideal of polynomial relations over `ℚ` as `(j(τ), weber(⟨1,τ⟩, 1/N))`.
- This was the gap x1-igusa §4 left between `AfTateCharPolyPicZero` and Diamond–Shurman 9.5.4. That leaf is now the
  print, apart from DS's own construction (`IsCurve`) and the unread wording of DS 9.5.4.

**Proof**, about 970 lines:
- A prime-ideal lemma for `ℚ[J][T]`, via localization to the PID `ℚ(j)[T]`.
- Mathlib's universal division polynomial `ΨSqₙ`, cleared of denominators and specialized to Diamond–Shurman's
  `E_j/\overline{ℚ(j)}` and to `ℂ/⟨1,τ⟩`.
- Tau Ceti's torsion criterion, plus the vendored uniformization.
- Holomorphy of `g₂`, `g₃` (Eisenstein series) and of `τ ↦ ℘_τ(1/N)`, the latter from a new locally uniform bound
  `≪ ‖(m,n)‖⁻³`.
- `g₃(i) = 0` and `g₂(ρ) = 0`, so `j` is not constant.
- The identity theorem on `ℍ`.

**What compiles** (all checked):
- `lake build ZInQKernel.Contrib.OneProof.WeberField` succeeds.
- `#discharges` is recorded in `scratch/weber-field/Discharges-output.txt`. `r16CoreY` is discharged by the imported
  `X1Igusa.r16CoreY_of_picZero_igusaDS`.
- The autofold spec `scratch/weber-field/autofold.json` has the same leaves as x1-igusa's. Only the flag of
  `afTateCharPolyPicZero` changes, to record that its dictionary step is proved.
- Its fold dry run gives `strict 45/10 -> 47/9`, `strictest 43/12 -> 45/11`, a strict −1. `sixContactMin_of_open31`
  has the standard axioms.

**Remaining:**
- Nothing remains for this Prop, and no new leaves were introduced.
- Leaf ratings are unchanged (`afTateCharPolyPicZero` and `igusaGL2DS` are published, unread, locators UNVERIFIED).
- Report: `docs/research/weber-field.md`.
