import ZInQKernel.Contrib.OneProof.CMFibreSplit.Reduction
import ZInQKernel.Contrib.OneProof.CMFibreSplit.Curve

/-! # cm-fibre-split: `CMBranch.CMFibreSplit` (diophantine_zq.tex, thm:height, proof, L581-586)

`CMFibreSplit` is proved from the chain's leaves at the open4 generation (G2 `FibreCoverExists`, T6 `HomFreeFiniteC`,
Néron–Ogg–Shafarevich, Raynaud, torsion structure, Yu's dichotomy `YuB6Alg`) and one remaining glue Prop,
`CMCurveOrder` (the geometric endomorphism ring of the elliptic curve `E` is an order of an imaginary quadratic
field). Proved on the way (`Reduction.lean`, `Curve.lean`): A8's Hom field at every fibre without NoCM
(`cmHomFieldModel_of`), the CM case of Yu's dichotomy (`end0Matrix_of_noncentral`), scaled matrix units
(`exists_scaledMatrixUnits`), the curve `E` and the isogeny `E² → A` (`matrixUnit_isogeny`). Report:
docs/research/cm-fibre-split.md. -/

namespace HDec
namespace CMBranch
namespace FibreSplit

/-- **`CMFibreSplit` from the chain's leaves and the glue `CMCurveOrder`.** -/
theorem cmFibreSplit_of_curveOrder (hYu : QMLattice.YuB6Alg)
    (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (hCover : G0ModField.FibreCoverExists)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterionNF.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hCO : CMCurveOrder) : CMFibreSplit :=
  cmFibreSplit_of hYu hHFF (cmHomFieldModel_of hCover hHFF hNOS hRay hTors) (cmMatrixUnitSplit_of hCO)

end FibreSplit
end CMBranch
end HDec
