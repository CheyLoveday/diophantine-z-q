import ZInQKernel.Contrib.OneProof.GrossZagierScheme.Core
import ZInQKernel.Contrib.OneProof.GrossZagierPlane.Extension
open UpperHalfPlane Filter Topology
open scoped WeierstrassCurve.Affine
open ZInQ.GZAlg ZInQ.GZDict2
example {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N) [E.IsElliptic] {Px Qx Py Qy : MvPolynomial (Fin 2) ℚ}
    (hrx : IsRatRep N (φ (genX E) : LaurentSeries ℚ) Px Qx)
    (hry : IsRatRep N (φ (genY E) : LaurentSeries ℚ) Py Qy) (τ : ℍ) : True := by
  have h1 := modPt_plane_cases E φ hrx hry τ
  trivial
set_option backward.isDefEq.respectTransparency false in
example {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N) [E.IsElliptic] {Px Qx Py Qy : MvPolynomial (Fin 2) ℚ}
    (hrx : IsRatRep N (φ (genX E) : LaurentSeries ℚ) Px Qx)
    (hry : IsRatRep N (φ (genY E) : LaurentSeries ℚ) Py Qy) (τ : ℍ) : True := by
  have h1 := modPt_plane_cases E φ hrx hry τ
  trivial
