import ZInQKernel.Contrib.OneProof.HeightModelM5.PullbackWedge
import ZInQKernel.Contrib.OneProof.HeightModelM5.BaseStalk
import ZInQKernel.Contrib.OneProof.HeightModelM5.SheafRows2

/-!
# Axiom check for the completion of the sheaf construction

Prints the axioms of every declaration of `PullbackWedge` (the pullback of the top exterior power
is the top exterior power of the pullback), `BaseStalk` (differentials relative to the base
stalks) and `SheafRows2` (the GR1 rows over `ε*Ω^g` taken literally). Each list is expected to lie
within `propext`, `Classical.choice` and `Quot.sound`.
-/

-- (a) PullbackWedge
#print axioms ZInQ.HeightModelM5.PW.valC
#print axioms ZInQ.HeightModelM5.PW.pullM
#print axioms ZInQ.HeightModelM5.PW.wedgePull
#print axioms ZInQ.HeightModelM5.PW.pullWedge
#print axioms ZInQ.HeightModelM5.PW.unitₛₗ
#print axioms ZInQ.HeightModelM5.PW.wedgeUnitₗ
#print axioms ZInQ.HeightModelM5.PW.wedgeUnitₗ_apply
#print axioms ZInQ.HeightModelM5.PW.psiApp
#print axioms ZInQ.HeightModelM5.PW.psiApp_apply
#print axioms ZInQ.HeightModelM5.PW.psiApp_ιMulti
#print axioms ZInQ.HeightModelM5.PW.wedgeUnit_res
#print axioms ZInQ.HeightModelM5.PW.psiApp_res
#print axioms ZInQ.HeightModelM5.PW.psi
#print axioms ZInQ.HeightModelM5.PW.bigPsi
#print axioms ZInQ.HeightModelM5.PW.bigPsi_app_wedgeUnit
#print axioms ZInQ.HeightModelM5.PW.wedgePullMap
#print axioms ZInQ.HeightModelM5.PW.wedgePullMap_app_unit
#print axioms ZInQ.HeightModelM5.PW.stalkMap
#print axioms ZInQ.HeightModelM5.PW.stalkMap_germ
#print axioms ZInQ.HeightModelM5.PW.germ_bigPsi_congr
#print axioms ZInQ.HeightModelM5.PW.wedgeStalkLin
#print axioms ZInQ.HeightModelM5.PW.wedgeStalkLin_apply
#print axioms ZInQ.HeightModelM5.PW.exteriorPower_map_bijective
#print axioms ZInQ.HeightModelM5.PW.wedgeMap_eq_map_baseChange
#print axioms ZInQ.HeightModelM5.PW.pullWedgeStalkMap
#print axioms ZInQ.HeightModelM5.PW.pullWedgeStalkMap_bijective
#print axioms ZInQ.HeightModelM5.PW.pullWedgeStalkMap_unitGerm
#print axioms ZInQ.HeightModelM5.PW.wedgeStalk_germ_psiApp
#print axioms ZInQ.HeightModelM5.PW.wedgeStalkLin_comp_stalkMap
#print axioms ZInQ.HeightModelM5.PW.stalkMap_bijective
#print axioms ZInQ.HeightModelM5.PW.abSheaf
#print axioms ZInQ.HeightModelM5.PW.abSheafHom
#print axioms ZInQ.HeightModelM5.PW.stalkFunctor_map_abSheafHom
#print axioms ZInQ.HeightModelM5.PW.wedgePullMap_stalk_bijective
#print axioms ZInQ.HeightModelM5.PW.wedgePullMap_app_bijective
#print axioms ZInQ.HeightModelM5.PW.isIso_abSheafHom
#print axioms ZInQ.HeightModelM5.PW.wedgePullSectionsEquiv
#print axioms ZInQ.HeightModelM5.PW.wedgePullSectionsEquiv_apply
#print axioms ZInQ.HeightModelM5.PW.wedgeStalkEquiv_germ_wedgePullMap
#print axioms ZInQ.HeightModelM5.index_span_map_equiv
#print axioms ZInQ.HeightModelM5.exists_span_index_iff_of_equiv
#print axioms ZInQ.HeightModelM5.GG.pullTopOmega
#print axioms ZInQ.HeightModelM5.GG.globalPullWedgeEquiv
#print axioms ZInQ.HeightModelM5.GG.genericGermTop_globalPullWedgeEquiv
#print axioms ZInQ.HeightModelM5.GG.genericGermPullTop
#print axioms ZInQ.HeightModelM5.GG.genericGermPullTop_injective

-- (b) BaseStalk
#print axioms ZInQ.HeightModelM5.BS.kaehlerMap_bijective
#print axioms ZInQ.HeightModelM5.BS.kaehlerLocalizationEquiv
#print axioms ZInQ.HeightModelM5.BS.kaehlerLocalizationEquiv_D
#print axioms ZInQ.HeightModelM5.BS.algBase
#print axioms ZInQ.HeightModelM5.BS.algBaseStalk
#print axioms ZInQ.HeightModelM5.BS.isLocalization_baseStalk
#print axioms ZInQ.HeightModelM5.BS.isScalarTower_baseStalk
#print axioms ZInQ.HeightModelM5.BS.kaehlerBaseStalkEquiv
#print axioms ZInQ.HeightModelM5.BS.kaehlerBaseStalkEquiv_D
#print axioms ZInQ.HeightModelM5.BS.stalkOmegaBaseEquiv
#print axioms ZInQ.HeightModelM5.BS.stalkOmegaBaseEquiv_germ_dSheaf
#print axioms ZInQ.HeightModelM5.BS.stalkOmegaBaseFormula

-- tree-facing (SheafRows2)
#print axioms ZInQ.HeightModelM5.GlobalPullTopOmega
#print axioms ZInQ.HeightModelM5.globalPullTopOmega_eq
#print axioms ZInQ.HeightModelM5.globalPullTopEquiv
#print axioms ZInQ.HeightModelM5.globalPullTopEquiv_apply
#print axioms ZInQ.HeightModelM5.genericGermPullTopOmega
#print axioms ZInQ.HeightModelM5.genericGermPullTopOmega_apply
#print axioms ZInQ.HeightModelM5.printedDetLattice_eq_pullTop
#print axioms ZInQ.HeightModelM5.secIndex_genericGermPullTopOmega
#print axioms ZInQ.HeightModelM5.IsGR1StableHeightSheaf'
#print axioms ZInQ.HeightModelM5.isGR1StableHeightSheaf'_iff_sheaf
#print axioms ZInQ.HeightModelM5.isGR1StableHeightSheaf'_iff
#print axioms ZInQ.HeightModelM5.GaudronRemondThm14GR1Sheaf'
#print axioms ZInQ.HeightModelM5.gaudronRemondThm14GR1Sheaf'_iff
#print axioms ZInQ.HeightModelM5.gaudronRemondThm14GR1_of_sheaf'
#print axioms ZInQ.HeightModelM5.GaudronRemondSec9LowerGR1WeakSheaf'
#print axioms ZInQ.HeightModelM5.gaudronRemondSec9LowerGR1WeakSheaf'_iff
#print axioms ZInQ.HeightModelM5.gaudronRemondSec9LowerGR1Weak_of_sheaf'
