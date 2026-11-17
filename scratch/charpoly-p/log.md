# charpoly-p results log

Base: main 0fcc7e36 (origin/main = main, merge no-op), merged origin/wip/degpoly-proof 0a9e6698
(brings charpoly-ell, deg-det, degpoly-proof contributions under ZInQKernel/Contrib/OneProof/).

## Survey (11-17)
- Mathlib 4.35: abelian sheaf cohomology on sites (`CategoryTheory.Sheaf.H`, Ext-based; Cech, Mayer–Vietoris),
  `Algebra/Homology/EulerCharacteristic.lean` (chain complexes only). No theorem of the cube, seesaw,
  Riemann–Roch, Snapper/Hilbert polynomial of sheaves, intersection numbers, χ(f^*L). VERIFIED (grep).
- Tree, vendored frenzymath Jacobian-Challenge (ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/):
  `Scheme.Modules.H`, `finrankH`, `eulerChar` (Cohomology/Basic.lean), finiteness for coherent modules on
  proper schemes (Cohomology/Proper.lean `hasFiniteH_of_isProper`), flat base change, Serre vanishing on
  projective space, curve Riemann–Roch / genus / line bundle degree on curves, Picard functor + Poincaré
  bundle for curves, rigidity. VERIFIED (read headers).
