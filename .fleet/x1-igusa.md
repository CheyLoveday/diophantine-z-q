# x1-igusa (fleet summary)

**Result.** isj1-dict's consequence-rated leaf `R16IsJ1Dict.X1PointsConjugate` (Igusa transitivity) is proved in
Lean from a printed-form leaf, `X1Igusa.IgusaGL2DS`: Igusa's theorem as Diamond–Shurman §7.5 prints it. That is,
`Gal(ℚ(j, E_j[N])/ℚ(j)) ≅ GL₂(ℤ/N)` through the action on `E_j[N]`, for every basis, for DS's model
`y² = 4x³ − g_j x − g_j` (`g_j = 27j/(j−1728)`); the theorem number is UNVERIFIED. So `r16CoreY` is discharged by
two published leaves, `X1Igusa.r16CoreY_of_picZero_igusaDS : AfTateCharPolyPicZero → IgusaGL2DS →
MumfordTorsionAlgClosed → R16CoreY`. The fold dry run gives **strict 45/10 → 47/9 (−1 GLUE)**, where isj1-dict's
fold was neutral.

**How.**
- Step 1, `E[N] ≅ (ℤ/N)²`, was already proved in the tree (`t36_torsionStructure`, from Tau Ceti's division
  polynomials).
- `SL₂(ℤ/N)` transitivity was also already proved (`exists_SL2_first_column`).
- `X1PointsConjugate` is literally `RLeaf.IgusaTransitive` (`Iff.rfl`).
- New Lean: DS's model `EDS` (with `j(EDS) = j`, elliptic), and an explicit change of variables over
  `\overline{ℚ(j)}` from DS's model to the kernel's `E_j` (`cDS_smul`: `u² = −18/(j−1728)²`, `r = −3/2`). With
  it, `x`-coordinates correspond `ℚ(j)`-affinely and Galois transitivity transfers.
- There is also an `x`-coordinate fallback leaf `IgusaGL2DSX` (Shimura's `GL₂/±1`).

**Compiles** (standard axioms):
- `ZInQKernel/Contrib/OneProof/X1Igusa.lean`: `lake build` succeeds;
- `#discharges` recorded (`scratch/x1-igusa/Discharges-output.txt`);
- `FoldDryRun.lean`;
- `scratch/x1-igusa/WeberComparison.lean`.

**Findings.**
1. The kernel's `E_j` is the `ℚ(√−2)`-twist of DS's model. So the old `RLeaf.IgusaGL2` (H-117) was, strictly, a
   consequence of the print rather than its printed form.
2. `AfTateCharPolyPicZero` is not a direct instance of DS 9.5.4. The gap is the function-field comparison
   `ℚ(j, f₁) ≅ ℚ(j)(x(P))`. It is now stated in Lean as the glue Prop `X1Igusa.Weber.WeberFieldComparison`, over
   `T5Glue.weber`, `jL` and `pp`. It needs no Igusa. A proof sketch (uniformization, division polynomial, identity
   theorem) is in the report §4.

**Remains.**
- Proving `WeberFieldComparison` (glue).
- Reading DS §7.5 for the theorem number and model, and DS 9.5.4 for its wording.
- Applying the fold (the integrator's step; spec in `scratch/x1-igusa/autofold.json`).

Report: `docs/research/x1-igusa.md`.
