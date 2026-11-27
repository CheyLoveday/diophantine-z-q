import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaForward
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaLevel
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaNonvanishing
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaTwist
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaWiring
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.CentralBaseZero
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.CentralCalibration
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.CentralEulerFactors
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.CentralSimpleZero
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.CentralUpperBound
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenKato
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenLowerBound
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenModel
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenPhaseBridge
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenPhaseForm
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenSmith
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenVocab
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegAdjusted
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegDescent
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegEmpty
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegInfRes
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegKummer
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegLocalDescent
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegShapiro
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.HeegTorsion
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.LimEvaluation
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.LimGlobal
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.LimOuter
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.LimResidualBound
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.LimRingsBaseZero
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.LimRingsClearing
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.LimTransfer
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.OddApMod
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.OddGenusTorsion
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.OddRootNumber
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.OddVisibility
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.OddVisibilityGenuine
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.SymApEven
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.SymKSplit
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.SymRules
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.SymShell
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateChebotarev
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateGlueArith
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateKummer
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateOdd
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateOpenImage
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TatePrecision
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TatePrintsArith
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateWiring
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.UnifClearing
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.UnifDeterminant
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.UnifSwitch
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.UnifUniform
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.UnifWiring

/-!
# Lane RC22 (glue sweep): all bridge files

Umbrella module importing every file of `ZInQKernel/Contrib/OneProof/RC/GlueSweep/`. Each file
removes GLUE or restated PRINT hypotheses of other lanes' theorems by theorems proved elsewhere in
the tree (other lanes, the shared top layer `ZInQ.Contrib.CloudB3RC53`, the vendored Tau Ceti
library, Mathlib), or records why a hypothesis cannot be removed. Namespaces:
`ZInQ.Manuscript.RC.GlueSweep.{Ana, Central, Even, Heeg, Lim, Odd, Sym, Tate, Unif}`.
-/
