import ZInQKernel.Contrib.OneProof.HeightModelM5.Defs
import ZInQKernel.Contrib.OneProof.HeightModelM5.StalkOmega
import ZInQKernel.Contrib.OneProof.HeightModelM5.PullbackStalk
import ZInQKernel.Contrib.OneProof.HeightModelM5.IrreducibleSections
import ZInQKernel.Contrib.OneProof.HeightModelM5.ExteriorSheaf
import ZInQKernel.Contrib.OneProof.HeightModelM5.GenericGerm
import ZInQKernel.Contrib.OneProof.HeightModelM5.GenericGermTop

/-!
# Axiom check for the Mathlib-only part of the sheaf construction

Prints the axioms of every theorem of `Defs`, `StalkOmega`, `PullbackStalk`,
`IrreducibleSections`, `ExteriorSheaf`, `GenericGerm` and `GenericGermTop`, and of the main
constructions. Each list is expected to lie within `propext`, `Classical.choice` and `Quot.sound`.

It also checks that the two module structures on a stalk of the sheaf of differentials, the
instance `moduleStalkOmega` and the general instance `stalkModule`, agree by definition, at
instance transparency.
-/

universe u

open CategoryTheory AlgebraicGeometry

section InstanceCheck

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (x : X)

example : ZInQ.HeightModelM5.moduleStalkOmega f x =
    ZInQ.HeightModelM5.stalkModule (ZInQ.HeightModelM5.relOmega f) x := by
  with_reducible_and_instances rfl

example : (inferInstance : Module (X.presheaf.stalk x) (ZInQ.HeightModelM5.stalkOmega f x)) =
    ZInQ.HeightModelM5.stalkModule (ZInQ.HeightModelM5.relOmega f) x := by
  with_reducible_and_instances rfl

end InstanceCheck

-- N0 (Defs)
#print axioms ZInQ.HeightModelM5.baseHom
#print axioms ZInQ.HeightModelM5.preOmega
#print axioms ZInQ.HeightModelM5.relOmega
#print axioms ZInQ.HeightModelM5.pullOmega
#print axioms ZInQ.HeightModelM5.globalPullOmega
#print axioms ZInQ.HeightModelM5.stalkOmega
#print axioms ZInQ.HeightModelM5.unitOmega
#print axioms ZInQ.HeightModelM5.dSheaf
#print axioms ZInQ.HeightModelM5.stalkAlgebra
#print axioms ZInQ.HeightModelM5.dSheaf_eq
#print axioms ZInQ.HeightModelM5.dSheaf_add
#print axioms ZInQ.HeightModelM5.dSheaf_zero
#print axioms ZInQ.HeightModelM5.dSheaf_one
#print axioms ZInQ.HeightModelM5.dSheaf_mul
#print axioms ZInQ.HeightModelM5.dSheaf_baseHom
#print axioms ZInQ.HeightModelM5.dSheaf_map
#print axioms ZInQ.HeightModelM5.moduleStalkOmega
#print axioms ZInQ.HeightModelM5.moduleStalkOmega_eq_stalkModule
#print axioms ZInQ.HeightModelM5.germ_smul_stalkOmega

-- N1 (StalkOmega)
#print axioms ZInQ.HeightModelM5.S1.exists_common_germ
#print axioms ZInQ.HeightModelM5.S1.stalkLift_germ
#print axioms ZInQ.HeightModelM5.isIso_stalkUnit
#print axioms ZInQ.HeightModelM5.stalkUnit_germ
#print axioms ZInQ.HeightModelM5.stalkUnit_smul
#print axioms ZInQ.HeightModelM5.stalkUnitEquiv
#print axioms ZInQ.HeightModelM5.stalkUnitEquiv_germ
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
#print axioms ZInQ.HeightModelM5.stalkOmegaEquiv
#print axioms ZInQ.HeightModelM5.stalkOmegaEquiv_germ_dSheaf
#print axioms ZInQ.HeightModelM5.stalkOmegaFormulaCanonical

-- N2 (PullbackStalk)
#print axioms ZInQ.HeightModelM5.stalkModule
#print axioms ZInQ.HeightModelM5.stalk_germ_smul
#print axioms ZInQ.HeightModelM5.germ_map_apply
#print axioms ZInQ.HeightModelM5.hom_app_map_apply
#print axioms ZInQ.HeightModelM5.stalkDescAdd_germ
#print axioms ZInQ.HeightModelM5.stalkDesc
#print axioms ZInQ.HeightModelM5.stalkDesc_germ
#print axioms ZInQ.HeightModelM5.skySec_smul_apply
#print axioms ZInQ.HeightModelM5.skyAb_isSheaf
#print axioms ZInQ.HeightModelM5.skyMod
#print axioms ZInQ.HeightModelM5.toSky
#print axioms ZInQ.HeightModelM5.toSky_app
#print axioms ZInQ.HeightModelM5.fromSky
#print axioms ZInQ.HeightModelM5.fromSky_germ
#print axioms ZInQ.HeightModelM5.unitGerm
#print axioms ZInQ.HeightModelM5.stalkPullback_hom_ext
#print axioms ZInQ.HeightModelM5.pullbackStalkAlgebra
#print axioms ZInQ.HeightModelM5.pullStalk_isScalarTower
#print axioms ZInQ.HeightModelM5.stalkPullbackFwdAux_germ
#print axioms ZInQ.HeightModelM5.stalkPullbackInv_unitGerm
#print axioms ZInQ.HeightModelM5.stalkPullbackFwd_tmul
#print axioms ZInQ.HeightModelM5.stalkPullbackInv_comp_fwd
#print axioms ZInQ.HeightModelM5.stalkPullbackFwd_comp_inv
#print axioms ZInQ.HeightModelM5.stalkPullbackEquiv
#print axioms ZInQ.HeightModelM5.stalkPullbackEquiv_unitGerm
#print axioms ZInQ.HeightModelM5.stalkPullbackEquiv_symm_tmul
#print axioms ZInQ.HeightModelM5.stalkPullbackFormula

-- N3 (IrreducibleSections)
#print axioms ZInQ.HeightModelM5.stalkSpecializes_germ_specializes
#print axioms ZInQ.HeightModelM5.germ_injective_of_specializes
#print axioms ZInQ.HeightModelM5.range_germ_eq_iInter_specializes
#print axioms ZInQ.HeightModelM5.germ_top_injective_of_isGenericPoint
#print axioms ZInQ.HeightModelM5.range_germ_top_eq_iInter_of_isGenericPoint
#print axioms ZInQ.HeightModelM5.modulesAbSheaf
#print axioms ZInQ.HeightModelM5.modules_germ_generic_injective
#print axioms ZInQ.HeightModelM5.modules_range_germ_generic
#print axioms ZInQ.HeightModelM5.spec_modules_sections_generic

-- N5a (ExteriorSheaf)
#print axioms ZInQ.HeightModelM5.fun_update_eq
#print axioms ZInQ.HeightModelM5.wedgeMap
#print axioms ZInQ.HeightModelM5.wedgeMap_ιMulti
#print axioms ZInQ.HeightModelM5.wedge_ext
#print axioms ZInQ.HeightModelM5.wedgeMap_apply_eq_self
#print axioms ZInQ.HeightModelM5.wedgeMap_comp_apply
#print axioms ZInQ.HeightModelM5.toRestrict_apply
#print axioms ZInQ.HeightModelM5.map_id_apply'
#print axioms ZInQ.HeightModelM5.wedgePresheafMap_ιMulti
#print axioms ZInQ.HeightModelM5.wedgePresheafMap_id
#print axioms ZInQ.HeightModelM5.wedgePresheafMap_comp
#print axioms ZInQ.HeightModelM5.wedgePresheaf
#print axioms ZInQ.HeightModelM5.wedgePresheaf_map
#print axioms ZInQ.HeightModelM5.germₛₗ_apply
#print axioms ZInQ.HeightModelM5.germₛₗ_res
#print axioms ZInQ.HeightModelM5.wedgeGerm_ιMulti
#print axioms ZInQ.HeightModelM5.wedgeGerm_res
#print axioms ZInQ.HeightModelM5.stalkToWedgeHom_germ
#print axioms ZInQ.HeightModelM5.exists_rep
#print axioms ZInQ.HeightModelM5.germ_ιMulti_eq
#print axioms ZInQ.HeightModelM5.stalkToWedgeHom_germₛₗ
#print axioms ZInQ.HeightModelM5.germₛₗ_update
#print axioms ZInQ.HeightModelM5.wedgeToStalkFun_eq
#print axioms ZInQ.HeightModelM5.wedgeToStalkAlt
#print axioms ZInQ.HeightModelM5.wedgeStalkGerm_res
#print axioms ZInQ.HeightModelM5.stalkToWedgeHom_wedgeStalkGerm
#print axioms ZInQ.HeightModelM5.wedgeToStalk_ιMulti
#print axioms ZInQ.HeightModelM5.stalkToWedgeHom_smul
#print axioms ZInQ.HeightModelM5.stalkToWedge_comp_wedgeToStalk
#print axioms ZInQ.HeightModelM5.wedgeToStalk_comp_stalkToWedge
#print axioms ZInQ.HeightModelM5.stalkWedgeEquiv
#print axioms ZInQ.HeightModelM5.stalkWedgeEquiv_germ_ιMulti
#print axioms ZInQ.HeightModelM5.wedgeSheaf
#print axioms ZInQ.HeightModelM5.toWedgeSheaf
#print axioms ZInQ.HeightModelM5.toPresheaf_map_toWedgeSheaf
#print axioms ZInQ.HeightModelM5.stalkWedgeSheafEquiv
#print axioms ZInQ.HeightModelM5.stalkWedgeSheafEquiv_germ
#print axioms ZInQ.HeightModelM5.isLocallyInjective_ringCatSheaf
#print axioms ZInQ.HeightModelM5.isLocallySurjective_ringCatSheaf
#print axioms ZInQ.HeightModelM5.schemeWedge
#print axioms ZInQ.HeightModelM5.schemeWedgeStalkEquiv
#print axioms ZInQ.HeightModelM5.schemeWedgeStalkEquiv_germ

-- generic germ (GenericGerm)
#print axioms ZInQ.HeightModelM5.modSpec
#print axioms ZInQ.HeightModelM5.modSpec_germ
#print axioms ZInQ.HeightModelM5.modSpec_smul
#print axioms ZInQ.HeightModelM5.GG.kStalk
#print axioms ZInQ.HeightModelM5.GG.kStalk_germ_dSheaf
#print axioms ZInQ.HeightModelM5.GG.towerSp
#print axioms ZInQ.HeightModelM5.GG.kMap
#print axioms ZInQ.HeightModelM5.GG.kMap_kStalk
#print axioms ZInQ.HeightModelM5.GG.sig
#print axioms ZInQ.HeightModelM5.GG.sig_self
#print axioms ZInQ.HeightModelM5.GG.stalkToGeneric
#print axioms ZInQ.HeightModelM5.GG.stalkToGeneric_tmul
#print axioms ZInQ.HeightModelM5.GG.stalkToGeneric_smul
#print axioms ZInQ.HeightModelM5.GG.pullStalkEquiv
#print axioms ZInQ.HeightModelM5.GG.pullStalkEquiv_unitGerm
#print axioms ZInQ.HeightModelM5.GG.phi
#print axioms ZInQ.HeightModelM5.GG.phi_smul
#print axioms ZInQ.HeightModelM5.GG.phi_unitGerm
#print axioms ZInQ.HeightModelM5.GG.phi_modSpec
#print axioms ZInQ.HeightModelM5.GG.pullAbSheaf
#print axioms ZInQ.HeightModelM5.GG.genericGerm
#print axioms ZInQ.HeightModelM5.GG.phi_injective
#print axioms ZInQ.HeightModelM5.GG.modSpec_injective
#print axioms ZInQ.HeightModelM5.GG.genericGerm_injective
#print axioms ZInQ.HeightModelM5.GG.range_genericGerm
#print axioms ZInQ.HeightModelM5.GG.genericGerm_smul

-- N5b general argument (GenericGermTop)
#print axioms ZInQ.HeightModelM5.GG.stalkToGenericₛₗ
#print axioms ZInQ.HeightModelM5.GG.stalkToGenericₛₗ_apply
#print axioms ZInQ.HeightModelM5.GG.wedgeGen
#print axioms ZInQ.HeightModelM5.GG.exists_baseChange
#print axioms ZInQ.HeightModelM5.GG.wedgeMap_equiv_injective
#print axioms ZInQ.HeightModelM5.GG.wedgeMap_comp_eq
#print axioms ZInQ.HeightModelM5.GG.wedgeMap_injective_of_baseChange
#print axioms ZInQ.HeightModelM5.GG.wedgeGen_injective
#print axioms ZInQ.HeightModelM5.GG.wedgeUnit
#print axioms ZInQ.HeightModelM5.GG.schemeWedge_exists_germ
#print axioms ZInQ.HeightModelM5.GG.schemeWedgeStalkEquiv_wedgeUnit
#print axioms ZInQ.HeightModelM5.GG.wedgeUnit_smul
#print axioms ZInQ.HeightModelM5.GG.schemeWedgeStalkEquiv_smul
#print axioms ZInQ.HeightModelM5.GG.pullPre
#print axioms ZInQ.HeightModelM5.GG.pullOmegaTop
#print axioms ZInQ.HeightModelM5.GG.phiₛₗ
#print axioms ZInQ.HeightModelM5.GG.phiₛₗ_apply
#print axioms ZInQ.HeightModelM5.GG.rhoTop
#print axioms ZInQ.HeightModelM5.GG.rhoTop_apply
#print axioms ZInQ.HeightModelM5.GG.wedgeMap_phi_wedgeGerm
#print axioms ZInQ.HeightModelM5.GG.rhoTop_modSpec
#print axioms ZInQ.HeightModelM5.GG.rhoTop_smul
#print axioms ZInQ.HeightModelM5.GG.schemeWedgeStalkEquiv_symm_smul
#print axioms ZInQ.HeightModelM5.GG.rhoTop_symm_ιMulti
#print axioms ZInQ.HeightModelM5.GG.wedgeMap_phi_eq
#print axioms ZInQ.HeightModelM5.GG.rhoTop_injective
#print axioms ZInQ.HeightModelM5.GG.modSpecTop_injective
#print axioms ZInQ.HeightModelM5.GG.topAbSheaf
#print axioms ZInQ.HeightModelM5.GG.genericGermTop
#print axioms ZInQ.HeightModelM5.GG.genericGermTop_injective
#print axioms ZInQ.HeightModelM5.GG.range_genericGermTop
#print axioms ZInQ.HeightModelM5.GG.genericGermTop_smul
#print axioms ZInQ.HeightModelM5.GG.hodgeModule
#print axioms ZInQ.HeightModelM5.GG.hodge_smul_aux
#print axioms ZInQ.HeightModelM5.GG.hodgeAlt
#print axioms ZInQ.HeightModelM5.GG.toHodge
#print axioms ZInQ.HeightModelM5.GG.toHodge_ιMulti
#print axioms ZInQ.HeightModelM5.GG.toHodge_smul
#print axioms ZInQ.HeightModelM5.GG.thetaₛₗ
#print axioms ZInQ.HeightModelM5.GG.fromHodge
#print axioms ZInQ.HeightModelM5.GG.fromHodge_tmul
#print axioms ZInQ.HeightModelM5.GG.fromHodge_smul
#print axioms ZInQ.HeightModelM5.GG.fromHodge_toHodge
#print axioms ZInQ.HeightModelM5.GG.toHodge_injective
#print axioms ZInQ.HeightModelM5.GG.range_comp_eq_iInter
#print axioms ZInQ.HeightModelM5.GG.mem_of_forall_maximal
#print axioms ZInQ.HeightModelM5.GG.relIndex_span_range
