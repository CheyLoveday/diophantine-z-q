import ZInQKernel.OneProof.H.TailY
open CategoryTheory AlgebraicGeometry
#check @GrpObj.inv_comp
#check @GrpObj.comp_inv
#check @Spec.preimage
#check @Spec.map_preimage
#check @Spec.map_inj
#check @Spec.map_injective
#check @IsLocalization.algHom_ext
#check @IsFractionRing.liftAlgHom
#check @IsFractionRing.liftAlgHom_apply
#check @Polynomial.finite_setOf_isRoot
#check @Set.Finite.exists_notMem
#check @PrimeSpectrum.isClosed_iff_zeroLocus_ideal
#check @Scheme.Spec_map_base
#check @Spec.map_base_apply
#check @Over.mono_of_mono_left
#check @IsLocalization.liftAlgHom_apply
#check @IsLocalization.lift_eq
#check @IsLocalRing.eq_maximalIdeal
#check @RingHom.ker_isMaximal_of_surjective
#check @pointOfClosedPoint
#check @LocallyOfFiniteType.jacobsonSpace
example (k : Type) [Field k] : IsReduced (Spec (CommRingCat.of (Polynomial k))) := inferInstance
example (k : Type) [Field k] [IsAlgClosed k] : Infinite k := inferInstance
example (k : Type) [Field k] : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) := inferInstance
