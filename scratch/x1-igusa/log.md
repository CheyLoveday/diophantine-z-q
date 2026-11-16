# x1-igusa results log

Base: wip/isj1-dict 37628525. Build tree: reflink copy of ~/dzq-check2/.lake/build (leaf-fold30, e22df37cd) and lean/.lake/build.

## Findings (before Lean)
- VERIFIED (read): `R16IsJ1Dict.X1PointsConjugate` (R16IsJ1Dict.lean l.219) has the same body, token for token, as
  `ZInQ.RLeaf.IgusaTransitive` (ZInQKernel/Contrib/RLeaf/X1RationalCusp.lean l.123), over the same constants
  (`LeafModCurves.EjBar`, `Kbar`, `Qj`, `xCoord`).
- VERIFIED (read): the tree already proves Step 1: `ZInQ.RLeaf.t36_torsionStructure : X1Belyi.TorsionStructure`
  (RLeaf/T36Torsion.lean; `nTors W N ≃+ ZMod N × ZMod N` over any algebraically closed char-0 field, from Tau Ceti
  `torsion_addEquiv_prod`, i.e. `#E[n] = n²` via division polynomials, Silverman III.6.4(b)).
- VERIFIED (read): the tree already proves Step 2's group theory and the derivation:
  `ZInQ.RLeaf.exists_SL2_first_column` (SL2(Z/N) transitive on vectors of order N), `igusaTransitive_of_igusaGL2 :
  IgusaGL2 → IgusaTransitive` (RLeaf/IgusaSL2.lean, t40-igusa / curve-split).
- VERIFIED (read): `ZInQ.RLeaf.IgusaGL2` was a LEAF field (H-117, leaf-fold19) but is no longer a field of the current
  bundle (flt-cqj2's bypass fold replaced it by ModularEquationGeneric, then proved that).
- Model gap: `IgusaGL2` is stated for the kernel model `E_j = ofJNe0Or1728 j`; the printed algebraic statement
  (Diamond–Shurman §7.5, UNVERIFIED number) is for `y² = 4x³ − g x − g`, `g = 27j/(j−1728)`.

## Lean (one process at a time)
- 02:10 `lake build R16IsJ1Dict IgusaSL2 TauCeti...VariableChange`: success (10401 jobs, 1m22s; partial rebuild on the copied tree).
- 02:15 `lake env lean scratch/x1-igusa/X1Igusa.lean`: no errors; axioms standard for
  `x1PointsConjugate_of_igusaGL2`, `xTransitive_of_igusaGL2For`, `EDS_j`, `cDS_smul`, `x1PointsConjugate_of_igusaGL2DS`. VERIFIED.
- Computation (VERIFIED by `cDS_smul`, Lean `linear_combination`): with m = j − 1728, u² = −18/m², the change of variables
  (u, r, s, t) = (u, −3/2, m u/2, 0) sends Diamond–Shurman's EDS : y² = x³ − (g/4)x − g/4, g = 27j/m, to the kernel's
  E_j = ofJNe0Or1728 j: `cDS u hu • EDSBar = EjBar`. So x_DS = u² x_kernel − 3/2 on points, u² ∈ ℚ(j).
- `EDS_j : EDS.j = j` VERIFIED; Δ(EDS) = g²(g − 27), g − 27 = 27·1728/m.
- 02:25 `lake build ZInQKernel.Contrib.OneProof.X1Igusa`: success (10402 jobs). VERIFIED.
