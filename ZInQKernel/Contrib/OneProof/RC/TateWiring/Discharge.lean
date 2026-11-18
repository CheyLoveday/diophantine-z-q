import ZInQKernel.Contrib.OneProof.RC.TateWiring.Image
import ZInQKernel.Contrib.CloudB3RC53.DetTateCyclotomic.Equality

/-!
# The determinant of the 2-adic Tate representation is the cyclotomic character

`DetTateTwoEqCyclotomic E` (the hypothesis this lane's moving-character statements take, `Image.lean`) holds for
every elliptic curve over `ℚ`: it is `CloudB3RC53.DetTateCyclotomic.detTateTwoEqCyclotomic`, proved from the Weil
pairing (Galois equivariance and surjectivity onto `μ_{2^k}` at every level `k`). Both definitions have the same body.
-/

namespace ZInQ.Manuscript.RC.TateWiring

/-- **`det ρ₂ = χ₂`** for every elliptic curve over `ℚ` (tex 3597–3605; PROVED). -/
theorem detTateTwoEqCyclotomic_holds (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    DetTateTwoEqCyclotomic E :=
  ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoEqCyclotomic E

end ZInQ.Manuscript.RC.TateWiring
