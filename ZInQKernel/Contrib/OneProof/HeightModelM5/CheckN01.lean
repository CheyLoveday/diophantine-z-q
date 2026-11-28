import ZInQKernel.Contrib.OneProof.HeightModelM5.Defs
import ZInQKernel.Contrib.OneProof.HeightModelM5.StalkOmega

/-!
# Axiom check for nodes N0 and N1

Prints the axioms of every theorem of `Defs` and `StalkOmega`, and of the main constructions.
Each list is expected to lie within `propext`, `Classical.choice` and `Quot.sound`.
-/

-- N0: definitions
#print axioms ZInQ.HeightModelM5.baseHom
#print axioms ZInQ.HeightModelM5.preOmega
#print axioms ZInQ.HeightModelM5.relOmega
#print axioms ZInQ.HeightModelM5.pullOmega
#print axioms ZInQ.HeightModelM5.globalPullOmega
#print axioms ZInQ.HeightModelM5.stalkOmega
#print axioms ZInQ.HeightModelM5.unitOmega
#print axioms ZInQ.HeightModelM5.dSheaf
#print axioms ZInQ.HeightModelM5.moduleStalkOmega

-- N0: basic API
#print axioms ZInQ.HeightModelM5.dSheaf_eq
#print axioms ZInQ.HeightModelM5.dSheaf_add
#print axioms ZInQ.HeightModelM5.dSheaf_zero
#print axioms ZInQ.HeightModelM5.dSheaf_one
#print axioms ZInQ.HeightModelM5.dSheaf_mul
#print axioms ZInQ.HeightModelM5.dSheaf_baseHom
#print axioms ZInQ.HeightModelM5.dSheaf_map
#print axioms ZInQ.HeightModelM5.germ_smul_stalkOmega

-- N1: helpers
#print axioms ZInQ.HeightModelM5.S1.exists_common_germ
#print axioms ZInQ.HeightModelM5.S1.stalkLift_germ

-- N1: the stalk of the sheafification
#print axioms ZInQ.HeightModelM5.isIso_stalkUnit
#print axioms ZInQ.HeightModelM5.stalkUnit_germ
#print axioms ZInQ.HeightModelM5.stalkUnit_smul
#print axioms ZInQ.HeightModelM5.stalkUnitEquiv
#print axioms ZInQ.HeightModelM5.stalkUnitEquiv_germ

-- N1: the stalk of the presheaf of differentials
#print axioms ZInQ.HeightModelM5.S1.baseHom_germ
#print axioms ZInQ.HeightModelM5.S1.algebraMap_stalk_eq
#print axioms ZInQ.HeightModelM5.S1.isScalarTower_germ
#print axioms ZInQ.HeightModelM5.S1.psiU_d
#print axioms ZInQ.HeightModelM5.S1.psiU_smul
#print axioms ZInQ.HeightModelM5.S1.resP_smul
#print axioms ZInQ.HeightModelM5.S1.resP_dP
#print axioms ZInQ.HeightModelM5.S1.dP_mul
#print axioms ZInQ.HeightModelM5.S1.germP_resP
#print axioms ZInQ.HeightModelM5.S1.germP_smul
#print axioms ZInQ.HeightModelM5.S1.psiU_res
#print axioms ZInQ.HeightModelM5.S1.psiFun_germ
#print axioms ZInQ.HeightModelM5.S1.psiLin_germ
#print axioms ZInQ.HeightModelM5.S1.deltaFun_germ
#print axioms ZInQ.HeightModelM5.S1.deltaFun_add
#print axioms ZInQ.HeightModelM5.S1.deltaFun_mul
#print axioms ZInQ.HeightModelM5.S1.deltaFun_algebraMap
#print axioms ZInQ.HeightModelM5.S1.isScalarTower_stalkPre
#print axioms ZInQ.HeightModelM5.S1.chiLin_D
#print axioms ZInQ.HeightModelM5.S1.psiLin_chiLin
#print axioms ZInQ.HeightModelM5.S1.chiLin_psiU
#print axioms ZInQ.HeightModelM5.S1.chiLin_psiLin
#print axioms ZInQ.HeightModelM5.S1.stalkPreEquiv

-- N1: the stalk formula S1
#print axioms ZInQ.HeightModelM5.stalkOmegaEquiv
#print axioms ZInQ.HeightModelM5.stalkOmegaEquiv_germ_dSheaf
#print axioms ZInQ.HeightModelM5.stalkOmegaFormulaCanonical
