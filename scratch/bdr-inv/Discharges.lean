import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.BdRInvariants

#discharges

example : DeRhamPrint.BdRInvariantsPrinted := BdRInv.bdRInvariantsPrinted_proof
#print axioms BdRInv.bdRInvariantsPrinted_proof
