# gz-dict2 (fleet summary)

**Verdict.** fold33-review's three dictionary steps between Gross–Zagier's morphism `φ : X₀(N) → E` and `hGZ`:

- **D2 is proved in Lean.** The leaf is restated so that it no longer needs D2.
- **D1 is proved in Lean** in the two models of `X₀(N)` that the tree has.
- **D3 is isolated.** It reduces to one standard topological fact, and only under one reading of GZ V §2.

The new leaf `ZInQ.GZDict2.GrossZagierPlaneOptCd` (`ZInQKernel/Contrib/OneProof/GrossZagierPlane.lean`) gives `φ` by
`φ^* : ℚ(E) →ₐ[ℚ] ℚ(j, j_N)`. It reads `φ(τ)` as the rational map `(Px/Qx, Py/Qy)` on the plane model at
`(j(τ), j(Nτ))`. The auxiliary `X, Y : ℍ → ℂ` are gone. Rating: **LEAF, printed form**, one reading item: GZ's
hypothesis on `φ`. Proposed: hGZ LEAF, GLUE −1 (kinds row in `scratch/gz-dict2/kinds-row.tsv`, with the
strictest-reading alternative "pending reading: D3 only").

**Compiles (standard axioms, VERIFIED):**

- **The bridge.** `grossZagierAlgOptCd_of_plane : GrossZagierPlaneOptCd → GZAlg.GrossZagierAlgOptCd`, which is what
  the chain reads (`grossZagierFormulaCd_of_alg`'s input), and `grossZagierFormulaCd_of_plane`.
- **D2.**
  - `q`-expansions form a ring (Cauchy product over `ℤ × ℤ`).
  - A nonzero expansion has no zeros high up.
  - The identity theorem on `ℍ`.
  - `eventuallyEq_ratFn`: a meromorphic `X` with expansion `P/Q` equals `P(j, j_N)/Q(j, j_N)` off a discrete set.
  - `modPt_eq_ratFn`.
- **D1** (`GrossZagierPlane/Extension.lean`).
  - `center_of_wEq` / `phi_center`: Hartshorne I.6.8 for `E ⊂ ℙ²`. Every place of `ℚ(X₀(N))` has a center for
    `φ^*`.
  - `modPt_plane_cases`: the leaf's value at `τ` is the continuous extension (finite limits on `E`, or `O` exactly
    at poles of `φ^*x`).
- **D3** (`GrossZagierPlane/OptimalUnique.lean`). `isOptimalParam_unique`: `IsOptimalParam` pins `φ` up to sign.
- **Manual fold.** `scratch/gz-dict2/FoldCheck.lean` is `frozenTarget` with `hGZ` retyped, spec in `fold-spec.md`.
- **`#discharges`.** `DISCHARGES [hGZ] by ZInQ.GZDict2.grossZagierAlgOptCd_of_plane`, still assumes
  `[GrossZagierPlaneOptCd]`.

**What remains.**

- **D1.** The identification of the canonical model `X₀(N)_ℚ` with the abstract curve of `ℚ(j, j_N)` is
  definitional (Shimura §6.7, Hartshorne I.6.9). The tree has no `X₀(N)` scheme on which to state it.
- **D3.** Under the reading "GZ V Thm 2.1 for every φ", the leaf is a restriction and nothing is needed. Under
  "strong Weil only", one fact is needed: P, `periodLattice f` = periods over `H₁(X₀(N), ℤ)`. P is standard but
  not statable in Lean (no `H₁(X₀(N))`, no `J₀(N)`). The reading of GZ p. 230 / p. 312 decides.

Report: `docs/research/gz-dict2.md`. Log: `scratch/gz-dict2/log.md`.
