import ZInQKernel.Contrib.OneProof.CMHeight62Full.FinalAssembly

/-!
# Checks for the final assembly of `cmHeight62`

`cmHeight62_unconditional` has the type `HDec.CMBranch.CMHeight62` of the open field
`cmHeight62`, with no hypotheses, and its axioms are the standard ones.
-/

open ZInQ.Contrib.CMHeight62Full

example : HDec.CMBranch.CMHeight62 := cmHeight62_unconditional

example : ZInQ.Contrib.CMHeight62.Step7 := step7_unconditional

example : LocalAssemblyCore := localAssemblyCore

example : ShortComparisonInput := shortComparisonInput

#check (cmHeight62_unconditional : HDec.CMBranch.CMHeight62)

#print axioms shortComparisonInput
#print axioms groupModel_isIntegral
#print axioms localAssemblyCore
#print axioms step7_unconditional
#print axioms cmHeight62_unconditional
