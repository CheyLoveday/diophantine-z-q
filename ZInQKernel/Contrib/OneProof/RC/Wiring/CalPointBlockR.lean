import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointKmIdent
import ZInQKernel.Contrib.OneProof.RC.Wiring.KmIdentBlock

/-!
# Theorem 5.3, Lane RC34: the R-block of the calibration with its point half derived

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141; the Kummer
coordinate, tex 3877–3892, 3895–3986, 4005–4021, 4057–4064). Lane RC35's block
`KummerCoordinateBlockR` replaces the literature block's free identification by the
identification constructed over the ordinary compact central Kummer complex, pinned by a
`CentralClassFunctional`. Its point fields `aP`, `bP`, `ha`, `hb`, `haP`, `hbP` (the
conclusion-shaped half of the old block) are here **derived**:

* `blockROfPointData`: the R-block from the integral duality `hdual`, point data `D` at the
  address (`RetainedPointData`) and the remaining block inputs (`h2`, `hK`, `finite2`,
  `rank_one`, the central comparison `link`, the arithmetic orders `arith`); the identification
  is pinned by `centralClassFunctional hdual D hm`, with `a_P = C (a₀ / m)`, `b_P = C (b₀ / m)`
  and the four point equations proved (`centralClassFunctional_sevenFields`).
* `blockROfBook`: the same with the genuine Kummer map `centralKummer G hdiv` and the duality
  from the leaf's book statements (`bookDuality`).
* `blockROfPointData_I`: its identification is RC35's `centralKMIdentModelOf` at the central
  class and functional.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CalPoint

open Matrix CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData DiskArith)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (compactCentralComplex centralCurve)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape)
open ZInQ.Contrib.RC53Assist.CalibrationShape (IntegralCentralKummerDuality)
open ZInQ.Manuscript.RC.Wiring (CalibrationBookProps)
open ZInQ.Manuscript.RC.Wiring.KmIdent (KummerCoordinateBlockR centralKMIdentModelOf)

section BlockR

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  {n : ℕ} {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
  {j vL m : ℤ} {tA shaA : ℕ}

/-- **The R-block with its point half derived** (tex 3895–3910, 4005–4021, 4057–4064): lane
RC35's `KummerCoordinateBlockR.ofCentralClassFunctional` at the central class and functional of
the point data, with `a_P = C (a₀ / m)`, `b_P = C (b₀ / m)` and `ha`, `hb`, `haP`, `hbP` proved.
The remaining inputs are those of the R-block other than its point fields. Kind: definition. -/
def blockROfPointData (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G))
    (hdual : IntegralCentralKummerDuality G hfinite)
    {κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1}
    (D : RetainedPointData G κ j vL) (hm : m ≠ 0)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    (hK : IsTotallyComplex K)
    (finite2 : ∀ [DecidableEq K],
      Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (link : ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2], Central.IsClassFunctionalCoord DK zK wK uK ∧
      central uK = ((ε : ℤ_[2]) : ℚ_[2]) *
        central (centralKMIdentModelOf G hfinite H (centralClassFunctional hdual D hm)).coord)
    (arith : DiskArith G tA shaA) : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA :=
  KummerCoordinateBlockR.ofCentralClassFunctional G hfinite H (centralClassFunctional hdual D hm)
    h2 hK finite2 rank_one link _ _ (centralClassFunctional_sevenFields hdual D hm).1
    (centralClassFunctional_sevenFields hdual D hm).2.1
    (centralClassFunctional_sevenFields hdual D hm).2.2.1
    (centralClassFunctional_sevenFields hdual D hm).2.2.2.1 arith

/-- **The identification of the derived R-block is RC35's identification pinned by the central
class and functional.** PROVED. -/
theorem blockROfPointData_I (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G))
    (hdual : IntegralCentralKummerDuality G hfinite)
    {κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1}
    (D : RetainedPointData G κ j vL) (hm : m ≠ 0) (h2) (hK) (finite2) (rank_one) (link) (arith) :
    (blockROfPointData (DK := DK) (zK := zK) (wK := wK) (tA := tA) (shaA := shaA) G hfinite H
      hdual D hm h2 hK finite2 rank_one link arith).I =
        centralKMIdentModelOf G hfinite H (centralClassFunctional hdual D hm) := rfl

/-- **The R-block from the book statements, the genuine Kummer map and the point data**
(tex 3895–3910, 4005–4021, 4057–4064). Kind: definition. -/
def blockROfBook (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G))
    (B : CalibrationBookProps) (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    (hdiv : GlobalDivisionTowers G.S (centralCurve G)) (D : CentralPointData G hdiv j vL)
    (hm : m ≠ 0)
    (finite2 : ∀ [DecidableEq K],
      Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (link : ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2], Central.IsClassFunctionalCoord DK zK wK uK ∧
      central uK = ((ε : ℤ_[2]) : ℚ_[2]) * central (centralKMIdentModelOf G hfinite H
        (centralClassFunctional (bookDuality G hfinite B hK h2) D hm)).coord)
    (arith : DiskArith G tA shaA) : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA :=
  blockROfPointData G hfinite H (bookDuality G hfinite B hK h2) D hm h2 hK finite2 rank_one link
    arith

end BlockR

end ZInQ.Manuscript.RC.CalPoint
