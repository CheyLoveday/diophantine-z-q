import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.DeligneNarrow

open Y3Hodge

#print axioms Y3Hodge.bodyNarrow_of_PM
#print axioms Y3Hodge.narrow_of_print
#print axioms Y3Hodge.witness_of_narrow
#print axioms Y3Hodge.shimuraFamilyAb_of_narrow
#print axioms Y3Hodge.connected_of_narrow_body
#print axioms Y3Hodge.y3ConnectedAb_of_narrow
#print axioms Y3Hodge.embed_core_narrow
#print axioms Y3Hodge.obj_at_narrow
#print axioms Y3Hodge.rayClassCMAb_of_narrow
#print axioms Y3Hodge.rayClassCMAb_of_narrow_leaves
#print axioms Y3Hodge.readData_of_narrow

-- The original live reader results, obtained via the bridge in the old-to-new direction.
variable (hM : AvSplit.MumfordTorsionAlgClosed) (h1 : Y3Fix.Y3FineModuliAbP)
variable (h2 : DeligneCanonicalModelY3EveryPrint)

example : HDec.QMSplit.Moduli.ShimuraFamilyAb :=
  shimuraFamilyAb_of_narrow hM h1 (narrow_of_print h2)

example (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) : ShimuraGlue.Ray.RayClassCMAb :=
  rayClassCMAb_of_narrow_leaves hM h1 (narrow_of_print h2) hUL hG

example : DCY3Used.Y3ConnectedAb :=
  y3ConnectedAb_of_narrow hM h1 (narrow_of_print h2)

#discharges
