# r1univ-rigid results log

## Library survey (VERIFIED by grep, 11-14)
- Field-level rigidity is proved in the kernel: `G0FibreSimple.rigidityHom` (ZInQKernel/Contrib/FrobChain/Rigidity.lean;
  a pointed morphism of PkgI3.AbVar is a homomorphism), CloudW06PoincareRigidity.rigidity_family,
  CloudW07JacobiansCurves .../Group/Rigidity.lean `isMonHom_of_isProper_of_geometricallyIntegral`.
- No relative rigidity over a base scheme S (Mumford GIT Ch. 6) and no group structure on a proper smooth family
  with a section exists in ZInQKernel/ (incl. vendored Tau Ceti, CloudW0*). `IsAbelianScheme` (Objects.lean:801) is a
  class over affine `Spec O` only (GIT Def 6.1); CloudW03's `AbelianSchemePropertyBundle` assumes a group law.
- Build: no .lake/build in this worktree; check.sh uses ~/dzq-check2's build (same commit df98652a).
