# isj1-dict (fleet summary)

**Result.** The `IsJ1` dictionary behind r16-used's `AfTateCharPoly` is reduced as far as the kernel allows,
and the leaf is made to hold under the weak reading of Diamond–Shurman 9.5.4. All of it compiles with
standard axioms (`ZInQKernel/Contrib/OneProof/R16IsJ1Dict.lean`, namespace `R16IsJ1Dict`).

- **Pic⁰ is the Albanese: proved.** Every kernel Jacobian (`IsJacobian`) is isomorphic to every
  tensor-compatible representative of `Pic⁰_{X/ℚ}`; the proof uses the vendored Jacobian-Challenge library.
  Base-point independence and transport along curve isomorphisms are proved too.
- **A curve is determined by its function field: proved** (`curveIsoOfFunctionFieldIso_proof`, from the
  vendored valuative extension of rational maps and valuation stalks of smooth curves).
- **Uniqueness of `J₁(N)`** (`abVarIso_of_isJ1'`) is proved from one leaf, `X1PointsConjugate` (Igusa
  transitivity on `x(P)`, a consequence of Shimura 6.6). **Finding:** it is false for `N = 0`, so it is stated
  with `0 < N`.
- **Restated leaf.** `AfTateCharPolyPicZero` is `AfTateCharPoly` for `J₁(N) = Pic⁰` of one model, DS's
  shape. Two directions are proved: it gives `AfTateCharPoly` (with the two leaves), and it follows from
  `AfTateCharPoly` and `X1ModelExists`.
- **Weak reading.** `AfTateWeakOdd` asks only that Frobenius satisfies `X² − a_p X + χ(p)p` over
  `ℚ_ℓ ⊗ K_f`, plus oddness on each ι-component. Proved:
  - it discharges `r16CoreY` (`component_charpoly`: ds965-weak's Chebotarev method on each ι-component,
    with the scalar case excluded by complex conjugation);
  - it is a consequence of `AfTateCharPoly` (`weakOdd_of_afTate`, with oddness proved from the
    characteristic polynomials and `χ(−1) = 1`).

  The scalar case cannot be excluded from the weak relation alone (argument in the report), so oddness is
  the input used.
- **Discharges** (`#discharges` recorded, standard axioms):
  - `r16CoreY_of_picZero_igusa : AfTateCharPolyPicZero → X1PointsConjugate → mumfordTorsionAlgClosed →
    R16CoreY`, spec autofold.json; dry run strict 45/10 → 46/10, strictest 43/12 → 44/12;
  - the weak-reading variant `r16CoreY_of_weakPicZero_igusa`, spec autofold-weak.json.

**Remains.**
- `K_N = ℚ(j, f₁)`: DS's `X₁(N)_alg` has to be a model in the kernel's sense. It cannot be stated in Lean
  today because the tree has no Weber function. This is the one place where the print is not a direct
  instance.
- Igusa (`X1PointsConjugate`) is a leaf, rated consequence. A printed form would need `E[N] ≅ (ℤ/N)²`,
  which Mathlib does not have.
- The DS 9.5.4 wording is unread.
- The fold is not applied (integrator's step). It needs `wip/r16-used` and `wip/ds965-weak` merged.

Report: docs/research/isj1-dict.md; log: scratch/isj1-dict/log.md.
