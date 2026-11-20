import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.BergerComparison.SurveyTransfer

/-! Run from the repository root. This uses the standard matcher on the exact type of
one headline row. The small root below is a scratch fixture. The source check
identifies the field in the current headline and its bundle; this does not
elaborate the complete headline. -/

run_cmd do
  let main ← IO.FS.readFile "ZInQKernel/OneProof/Main.lean"
  let bundle ← IO.FS.readFile "ZInQKernel/OneProof/H/TailZ98.lean"
  unless (main.splitOn "(r : HDec.HSyn.OpenResearchLeaves72)").length > 1 ∧
      (bundle.splitOn "structure OpenResearchLeaves72 : Prop where").length > 1 ∧
      (bundle.splitOn "  bergerSurveyF : _root_.HDec.PkgI4.PanDict.BergerSurveyF").length > 1 do
    throwError "The checked row has changed; update this fixture from the headline and its bundle."

set_option linter.unusedVariables false in
set_option linter.defProp false in
def ZInQ.OneProof.frozenTarget (bergerSurveyF : HDec.PkgI4.PanDict.BergerSurveyF) : True :=
  True.intro

set_option maxHeartbeats 0 in
#discharges
