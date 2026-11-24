import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Torus
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Realization

/-! The actual Picard and orbit fibers of (O.7), tex 9155–9169. -/

noncomputable section

open scoped NumberField

namespace ZInQ.Manuscript.RC.LocalTorus

open Eichler O7Actual O7Orbits PicardFibers Visibility

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}
variable {F : Type} [Field F] [NumberField F]

/-- One ideal-class parametrization of each actual orientation fiber. -/
def picardFibers (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) :
    PicardFibers s H (ClassGroup (𝓞 F)) :=
  picardFibers_of_local s A H hh Q ι (localTorusChart s A Q ι)
    (hasLocalRealizations s A hh Q ι)

/-- The orbit-fiber input of the actual (O.7) datum. -/
def orbitFibers (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) :
    OrbitFibers s.visibility (index s D) N.primeFactors.card (ClassGroup (𝓞 F)) :=
  orbitFibers_of_local s A H hh Q ι (localTorusChart s A Q ι)
    (hasLocalRealizations s A hh Q ι)

end ZInQ.Manuscript.RC.LocalTorus
