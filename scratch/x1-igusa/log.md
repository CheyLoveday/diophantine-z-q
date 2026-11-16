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
