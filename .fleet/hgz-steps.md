# hgz-steps (fleet summary)

**Main result: `hGZ` is a direct instance of the print, with D1 and D2 proved in Lean.** The new leaf
`ZInQ.GZSch.GrossZagierCurveCd` (`ZInQKernel/Contrib/OneProof/GrossZagierScheme.lean`) is Gross–Zagier (Invent.
Math. 84, Thm I.6.3 and V §2 Thm 2.1, constant forgotten) for any nonconstant morphism of `ℚ`-schemes
`π : X ⟶ ESch E` with `π(∞) = O`:

- `X` is a normal proper model of `X₀(N)` with `K(X) ≅ ℚ(j, j_N)`.
- `ESch E = Proj ℚ[X, Y, Z]/(F_E)`.
- The Heegner points are `ℂ`-points of `X`.
- The twist is by `ε_D`, the Kronecker symbol.

D3 is not needed: the queue9 reading of V §2, p. 310 allows any covering.

**Compiles** (standard axioms, no `sorry`, VERIFIED):
- **The bridge.** `grossZagierAlgOptCd_of_curve : GrossZagierCurveCd → GZAlg.GrossZagierAlgOptCd`.
- **D1.** `φ^*` gives a morphism `π` (`exists_extension`, via Jacobian-Challenge's valuative extension).
- **D2.** The value of `π` at the point `τ` is gz-dict2's `modPt` (`ptOf_eq_modPt`).
- **Model.** The normal model of `ℚ(X₀(N))` exists (`exists_model`, from the vendored `Φ_N` and cloud-w07's
  `NormalModelOfFunctionFieldQ_proof`).
- **Points `τ`.** They exist (`exists_pointAt`, through the place `ord_τ` built in `PointTau.lean`) and are unique
  (`isPointAt_unique`).
- **Cusp.** `∞` exists and `π(∞) = O` (`exists_cusp`, `cusp_not_mem_chart`).
- **`ε_D`.** `ε_D(n) = (n/|D|)` (`epsD_eq_jacobiSym`).

**Checks** (VERIFIED):
- `#discharges` reports `DISCHARGES [hGZ] by ZInQ.GZSch.grossZagierAlgOptCd_of_curve`, still assuming
  `[ZInQ.GZSch.GrossZagierCurveCd]`.
- `scratch/hgz-steps/FoldCheck.lean`, `frozenTarget` with `hGZ` retyped, has standard axioms.

**Rating.** LEAF, printed form. Proposed: `hGZ` GLUE → LEAF, **GLUE −1** in both columns, no glue added.
- Kinds row: `scratch/hgz-steps/kinds-row.tsv`.
- Locators row: `locators-row.md`.
- Autofold spec: `autofold.json`. `hGZ` is a binder, so the fold is manual (`fold-spec.md`).

**What remains.**
- The integrator applies the fold. It needs gz-dict2's `GrossZagierPlane` modules, which are merged here.
- Optional: Lean's `ε_D` is the Kronecker symbol. Its identification with the splitting character of `ℚ(√D)`
  (Dedekind–Kummer) is not formalized; the arithmetic side is proved for odd `p ∤ D` and for `p = 2`.

Report: `docs/research/hgz-steps.md`. Log: `scratch/hgz-steps/log.md`.
