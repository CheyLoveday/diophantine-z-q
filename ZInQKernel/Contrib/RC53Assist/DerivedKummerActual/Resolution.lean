import ZInQKernel.Contrib.RC53Assist.DerivedKummerActual.Actual


noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualConeModels

open CategoryTheory NumberField IsDedekindDomain TauCeti
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSelfDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTransport
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

instance condition_two_subsingleton : Subsingleton ((localCondition K w B).X 2) := by
  change Subsingleton PUnit
  infer_instance

instance condition_three_subsingleton : Subsingleton ((localCondition K w B).X 3) := by
  change Subsingleton PUnit
  infer_instance

instance condition_four_subsingleton : Subsingleton ((localCondition K w B).X 4) := by
  change Subsingleton PUnit
  infer_instance

/-- The exact degree-zero cone differential uses the fixed genuine local Kummer map. -/
theorem cone_d_zero (x : (localQuotientCone K w B).X 0) :
    (localQuotientCone K w B).d 0 1 rfl x =
      (((pointComplex (w.adicCompletion K) B).d 0 1).hom x.1 +
        (localKummerOne K w B x.2).val, 0) := by
  haveI : Subsingleton ((localCondition K w B).X (1 + 1)) := by
    change Subsingleton PUnit
    infer_instance
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

/-- The actual degree-one cone differential has no higher local-condition component. -/
theorem cone_d_one (x : (localQuotientCone K w B).X 1) :
    (localQuotientCone K w B).d 1 2 rfl x =
      (((pointComplex (w.adicCompletion K) B).d 1 2).hom x.1, 0) := by
  haveI : Subsingleton ((localCondition K w B).X (1 + 1)) := by
    change Subsingleton PUnit
    infer_instance
  haveI : Subsingleton ((localCondition K w B).X (2 + 1)) := by
    change Subsingleton PUnit
    infer_instance
  apply Prod.ext
  · have hx : x.2 = 0 := Subsingleton.elim _ _
    change (localCochains K w B).d 1 2 rfl x.1 +
      (localConditionMap K w B).f 2 2 rfl x.2 = (localCochains K w B).d 1 2 rfl x.1
    rw [hx, map_zero, add_zero]
  · exact Subsingleton.elim _ _

/-- The actual degree-two cone differential is the genuine point-cochain differential. -/
theorem cone_d_two (x : (localQuotientCone K w B).X 2) :
    (localQuotientCone K w B).d 2 3 rfl x =
      (((pointComplex (w.adicCompletion K) B).d 2 3).hom x.1, 0) := by
  haveI : Subsingleton ((localCondition K w B).X (2 + 1)) := by
    change Subsingleton PUnit
    infer_instance
  haveI : Subsingleton ((localCondition K w B).X (3 + 1)) := by
    change Subsingleton PUnit
    infer_instance
  apply Prod.ext
  · have hx : x.2 = 0 := Subsingleton.elim _ _
    change (localCochains K w B).d 2 3 rfl x.1 +
      (localConditionMap K w B).f 3 3 rfl x.2 = (localCochains K w B).d 2 3 rfl x.1
    rw [hx, map_zero, add_zero]
  · exact Subsingleton.elim _ _

/-- Projection of a genuine cone one-cycle is the actual point-cochain one-cycle. -/
def cycleOneProjection : LinearMap.ker ((localQuotientCone K w B).d 1 2 rfl) →ₗ[ℤ_[2]]
    SourceFirstCohomology.cycles K w B where
  toFun z := ⟨z.val.1, by
    have h := congrArg Prod.fst z.property
    change ((localQuotientCone K w B).d 1 2 rfl z.val).1 = 0 at h
    erw [cone_d_one] at h
    exact h⟩
  map_add' z u := Subtype.ext rfl
  map_smul' r z := Subtype.ext rfl

/-- The actual degree-one cone class map is the specified boundary/Kummer quotient of the cochain projection. -/
def classOne : LinearMap.ker ((localQuotientCone K w B).d 1 2 rfl) →ₗ[ℤ_[2]]
    SourceFirstCohomology.sourceOne K w B :=
  (SourceFirstCohomology.boundaries K w B).mkQ.comp (cycleOneProjection K w B)

/-- Every actual degree-one quotient class is represented by its genuine cone cycle. -/
theorem classOne_surjective : Function.Surjective (classOne K w B) := by
  intro z
  obtain ⟨c, hc⟩ := (SourceFirstCohomology.boundaries K w B).mkQ_surjective z
  refine ⟨⟨(c.val, 0), ?_⟩, hc⟩
  change (localQuotientCone K w B).d 1 2 rfl (c.val, 0) = 0
  erw [cone_d_one]
  apply Prod.ext
  · change ((pointComplex (w.adicCompletion K) B).d 1 2).hom c.val = 0
    exact c.property
  · rfl

/-- The kernel of the specified actual first class map is exactly the actual degree-zero cone boundary image. -/
theorem classOne_kernel (z : LinearMap.ker ((localQuotientCone K w B).d 1 2 rfl)) :
    classOne K w B z = 0 ↔ ∃ y : (localQuotientCone K w B).X 0,
      (localQuotientCone K w B).d 0 1 rfl y = z.val := by
  haveI : Subsingleton ((localCondition K w B).X (1 + 1)) := by
    change Subsingleton PUnit
    infer_instance
  change (SourceFirstCohomology.boundaries K w B).mkQ (cycleOneProjection K w B z) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hz
    obtain ⟨c, ⟨b, rfl⟩, u, ⟨v, rfl⟩, heq⟩ := Submodule.mem_sup.mp hz
    refine ⟨(b, v), ?_⟩
    erw [cone_d_zero]
    apply Prod.ext
    · exact congrArg Subtype.val heq
    · exact Subsingleton.elim _ _
  · rintro ⟨⟨b, v⟩, hz⟩
    apply Submodule.mem_sup.mpr
    refine ⟨SourceFirstCohomology.incoming K w B b, ⟨b, rfl⟩,
      localKummerOne K w B v, ⟨v, rfl⟩, ?_⟩
    apply Subtype.ext
    have h := congrArg Prod.fst hz
    erw [cone_d_zero] at h
    exact h

/-- Projection and canonical closure transport read actual cone two-cycles in the earlier fixed coefficient complex. -/
def cycleTwoProjection : LinearMap.ker ((localQuotientCone K w B).d 2 3 rfl) →ₗ[ℤ_[2]]
    SourceSecondCohomology.cycles K w B where
  toFun z := ⟨((toAlgComplex (w.adicCompletion K) B).f 2).hom z.val.1, by
    have hz : ((pointComplex (w.adicCompletion K) B).d 2 3).hom z.val.1 = 0 := by
      have h := congrArg Prod.fst z.property
      erw [cone_d_two] at h
      exact h
    have h := congrArg (fun f => f.hom z.val.1) ((toAlgComplex (w.adicCompletion K) B).comm 2 3)
    change ((actualIntegralComplex (w.adicCompletion K) B).d 2 3).hom
      (((toAlgComplex (w.adicCompletion K) B).f 2).hom z.val.1) = 0
    calc
      _ = ((toAlgComplex (w.adicCompletion K) B).f 3).hom
          (((pointComplex (w.adicCompletion K) B).d 2 3).hom z.val.1) := h
      _ = 0 := by rw [hz, map_zero]⟩
  map_add' z u := Subtype.ext (map_add _ _ _)
  map_smul' r z := Subtype.ext (map_smul _ _ _)

/-- The actual second cone class map uses the original genuine cochain boundary quotient. -/
def classTwo : LinearMap.ker ((localQuotientCone K w B).d 2 3 rfl) →ₗ[ℤ_[2]]
    SourceSecondCohomology.sourceTwo K w B :=
  (LinearMap.range (SourceSecondCohomology.incoming K w B)).mkQ.comp (cycleTwoProjection K w B)

/-- The inverse of the specified closure transport recovers each algebraic-closure cochain. -/
theorem transport_alg_inverse (n : ℕ) (c : (actualIntegralComplex (w.adicCompletion K) B).X n) :
    ((toAlgComplex (w.adicCompletion K) B).f n).hom
        (((toSepComplex (w.adicCompletion K) B).f n).hom c) = c := by
  have h := congrArg (fun f => (f.f n).hom c) (toSepComplex_toAlgComplex (w.adicCompletion K) B)
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

/-- The same actual transport recovers every separable-closure cochain in the reverse direction. -/
theorem transport_sep_inverse (n : ℕ) (c : (pointComplex (w.adicCompletion K) B).X n) :
    ((toSepComplex (w.adicCompletion K) B).f n).hom
        (((toAlgComplex (w.adicCompletion K) B).f n).hom c) = c := by
  have h := congrArg (fun f => (f.f n).hom c) (toAlgComplex_toSepComplex (w.adicCompletion K) B)
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

/-- Every actual second quotient class has a genuine cone representative via the canonical closure transport. -/
theorem classTwo_surjective : Function.Surjective (classTwo K w B) := by
  intro z
  obtain ⟨c, hc⟩ := (LinearMap.range (SourceSecondCohomology.incoming K w B)).mkQ_surjective z
  let x : (localQuotientCone K w B).X 2 :=
    (((toSepComplex (w.adicCompletion K) B).f 2).hom c.val, 0)
  have hx : (localQuotientCone K w B).d 2 3 rfl x = 0 := by
    erw [cone_d_two]
    apply Prod.ext
    · change ((pointComplex (w.adicCompletion K) B).d 2 3).hom
        (((toSepComplex (w.adicCompletion K) B).f 2).hom c.val) = 0
      rw [← toSepComplex_d, c.property, map_zero]
    · rfl
  refine ⟨⟨x, hx⟩, ?_⟩
  have hproj : cycleTwoProjection K w B ⟨x, hx⟩ = c := by
    apply Subtype.ext
    exact transport_alg_inverse K w B 2 c.val
  change (LinearMap.range (SourceSecondCohomology.incoming K w B)).mkQ
    (cycleTwoProjection K w B ⟨x, hx⟩) = z
  rw [hproj]
  exact hc

/-- Actual second cone boundaries are exactly the kernel of the prescribed transported class map. -/
theorem classTwo_kernel (z : LinearMap.ker ((localQuotientCone K w B).d 2 3 rfl)) :
    classTwo K w B z = 0 ↔ ∃ y : (localQuotientCone K w B).X 1,
      (localQuotientCone K w B).d 1 2 rfl y = z.val := by
  haveI : Subsingleton ((localCondition K w B).X (2 + 1)) := by
    change Subsingleton PUnit
    infer_instance
  change (LinearMap.range (SourceSecondCohomology.incoming K w B)).mkQ
    (cycleTwoProjection K w B z) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(((toSepComplex (w.adicCompletion K) B).f 1).hom b, 0), ?_⟩
    erw [cone_d_one]
    apply Prod.ext
    · have hv := congrArg Subtype.val hb
      change ((actualIntegralComplex (w.adicCompletion K) B).d 1 2).hom b =
        ((toAlgComplex (w.adicCompletion K) B).f 2).hom z.val.1 at hv
      change ((pointComplex (w.adicCompletion K) B).d 1 2).hom
          (((toSepComplex (w.adicCompletion K) B).f 1).hom b) = z.val.1
      rw [← toSepComplex_d, hv]
      exact transport_sep_inverse K w B 2 z.val.1
    · exact Subsingleton.elim _ _
  · rintro ⟨⟨b, u⟩, hb⟩
    refine ⟨((toAlgComplex (w.adicCompletion K) B).f 1).hom b, ?_⟩
    apply Subtype.ext
    have hv := congrArg Prod.fst hb
    erw [cone_d_one] at hv
    change ((actualIntegralComplex (w.adicCompletion K) B).d 1 2).hom
        (((toAlgComplex (w.adicCompletion K) B).f 1).hom b) =
      ((toAlgComplex (w.adicCompletion K) B).f 2).hom z.val.1
    have h := congrArg (fun f => f.hom b) ((toAlgComplex (w.adicCompletion K) B).comm 1 2)
    calc
      _ = ((toAlgComplex (w.adicCompletion K) B).f 2).hom
          (((pointComplex (w.adicCompletion K) B).d 1 2).hom b) := h
      _ = _ := congrArg ((toAlgComplex (w.adicCompletion K) B).f 2).hom hv

/-- Both actual cone class maps, their onto proofs and their genuine boundary kernels form the source recognition data. -/
def cohomologyData : FiniteSourceRecipe.CohomologyData
    (localQuotientCone K w B) (SourceFirstCohomology.sourceOne K w B)
      (SourceSecondCohomology.sourceTwo K w B) where
  classOne := classOne K w B
  one_surjective := classOne_surjective K w B
  one_kernel := classOne_kernel K w B
  classTwo := classTwo K w B
  two_surjective := classTwo_surjective K w B
  two_kernel := classTwo_kernel K w B

/-- The specific degree-one class reduction kills every actual continuous boundary. -/
theorem point_reduction_boundary (a : ℕ)
    (c : LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 1 2).hom)
    (b : (pointComplex (w.adicCompletion K) B).X 0)
    (hb : ((pointComplex (w.adicCompletion K) B).d 0 1).hom b = c.val) :
    pointH1Reduction (w.adicCompletion K) B a c = 0 := by
  let e := TauCeti.ContCohomology.explicitCoeff1Equiv
    (TauCeti.AbsoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (TauCeti.AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff a)
    (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B a)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (pointLevelEquiv_smul (w.adicCompletion K) B a)
  change e (ZInQ.Manuscript.RC.SelmerComplex.kerToH1
    (reduceOneCycle (TauCeti.AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff a c)) = 0
  apply e.map_eq_zero_iff.mpr
  apply (ZInQ.Manuscript.RC.SelmerComplex.kerToH1_eq_zero_iff _).mpr
  refine ⟨((reduceCochains (TauCeti.AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff a).f 0).hom b, ?_⟩
  change ((finiteIntegralComplex (TauCeti.AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff a).d 0 1).hom
      (((reduceCochains (TauCeti.AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff a).f 0).hom b) =
    ((reduceCochains (TauCeti.AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff a).f 1).hom c.val
  rw [← reduceCochains_d, hb]

/-- The actual completed-point Kummer map is injective on integral classes before any local duality input. -/
theorem local_Kummer_boundary_point_zero
    (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2])
    (hb : ∃ b : (pointComplex (w.adicCompletion K) B).X 0,
      ((pointComplex (w.adicCompletion K) B).d 0 1).hom b = (localKummerOne K w B u).val) :
    (actualLocalPresentation K w B).g u = 0 := by
  obtain ⟨b, hb⟩ := hb
  apply SourceKummerClasses.completion_class_family_injective (w.adicCompletion K) B
  intro a
  have h := point_reduction_boundary K w B a (localKummerOne K w B u) b hb
  rw [localKummerOne_reduction] at h
  change (FiniteTrace.hOneToAlg (w.adicCompletion K) B (2 ^ a)).symm
    (IntegralReduction.actualH1Reduction (w.adicCompletion K) B a
      (IntegralKummer.actualLocalKummerOne K w B u)) = 0 at h
  rw [IntegralKummer.actualLocalKummerOne, IntegralKummer.basedKummerOne_reduction] at h
  have hx := (FiniteTrace.hOneToAlg (w.adicCompletion K) B (2 ^ a)).symm.map_eq_zero_iff.mp h
  rw [map_zero]
  exact hx

/-- Every actual degree-zero quotient-cone cycle is an actual degree-minus-one boundary. -/
theorem cone_zero_exact (z : (localQuotientCone K w B).X 0)
    (hz : (localQuotientCone K w B).d 0 1 rfl z = 0) :
    ∃ y : (localQuotientCone K w B).X (-1), (localQuotientCone K w B).d (-1) 0 rfl y = z := by
  let l : (pointComplex (w.adicCompletion K) B).X 0 := z.1
  let v : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2] := z.2
  have h0 : ((pointComplex (w.adicCompletion K) B).d 0 1).hom l +
      (localKummerOne K w B v).val = 0 := by
    have h := congrArg Prod.fst hz
    erw [cone_d_zero] at h
    exact h
  have hK : (localKummerOne K w B v).val =
      ((pointComplex (w.adicCompletion K) B).d 0 1).hom (-l) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_right h0
  have hg := local_Kummer_boundary_point_zero K w B v ⟨-l, hK.symm⟩
  obtain ⟨u, hu⟩ := (actualLocalPresentation K w B).exact v hg
  have hb : ((pointComplex (w.adicCompletion K) B).d 0 1).hom
      (l + localKummerZero K w B u) = 0 := by
    rw [map_add, localKummerZero_d, hu]
    exact h0
  have hzero := SourceDegreeZero.actual_zero_cochain_kernel K w B _ hb
  refine ⟨(0, -u), ?_⟩
  apply Prod.ext
  · change (0 : (pointComplex (w.adicCompletion K) B).X 0) + (localKummerZero K w B) (-u) = l
    rw [zero_add, map_neg]
    exact (eq_neg_of_add_eq_zero_left hzero).symm
  · change -((actualLocalPresentation K w B).f (-u)) = v
    rw [map_neg, neg_neg, hu]

/-- A genuine degree-minus-one cone cycle is zero, because the point relation map is injective. -/
theorem cone_neg_one_cycle_zero (z : (localQuotientCone K w B).X (-1))
    (hz : (localQuotientCone K w B).d (-1) 0 rfl z = 0) : z = 0 := by
  haveI : Subsingleton ((localCochains K w B).X (-1)) := by
    change Subsingleton PUnit
    infer_instance
  have hu := congrArg Prod.snd hz
  change -((actualLocalPresentation K w B).f z.2) = 0 at hu
  have hz2 : z.2 = 0 := (actualLocalPresentation K w B).injective
    ((neg_eq_zero.mp hu).trans ((actualLocalPresentation K w B).f.map_zero).symm)
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · exact hz2

/-- The actual quotient cone is exact in all degrees at most zero, using the genuine point presentation and Kummer maps. -/
theorem cone_lower_exact (n : ℤ) (hn : n ≤ 0)
    (z : (localQuotientCone K w B).X n) (hz : (localQuotientCone K w B).d n (n + 1) rfl z = 0) :
    ∃ y : (localQuotientCone K w B).X (n - 1),
      (localQuotientCone K w B).d (n - 1) n (by omega) y = z := by
  by_cases hn0 : n = 0
  · subst n
    exact cone_zero_exact K w B z hz
  · by_cases hnm1 : n = -1
    · subst n
      exact ⟨0, by rw [map_zero]; exact (cone_neg_one_cycle_zero K w B z hz).symm⟩
    · have hnneg : n < -1 := by omega
      haveI : Subsingleton ((localCochains K w B).X n) := by
        rcases n with n | n
        · have hnonneg : (0 : ℤ) ≤ Int.ofNat n := Int.natCast_nonneg n
          omega
        · change Subsingleton PUnit
          infer_instance
      haveI : Subsingleton ((localCondition K w B).X (n + 1)) :=
        SelfDualCore.presentationCx_vanishes _ _ _ _ (by omega)
      haveI : Subsingleton ((localQuotientCone K w B).X n) := by
        change Subsingleton (((localCochains K w B).X n) × ((localCondition K w B).X (n + 1)))
        infer_instance
      exact ⟨0, Subsingleton.elim _ _⟩

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualConeModels

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSourceVerified

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedBridge
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSourceCoordinates
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSourceRecipe

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  (C : GCx R) (H1 H2 : Type) [AddCommGroup H1] [Module R H1]
  [AddCommGroup H2] [Module R H2]

/-- Specified finite presentation, cycle lifts and relation lifts of actual source cohomology. -/
structure LiftData (D : CohomologyData C H1 H2) where
  presentation : Presentation (R := R) H2
  rankOne : ℕ
  coordinates : (Fin rankOne → R) ≃ₗ[R] H1
  cyclesOne : (Fin rankOne → R) →ₗ[R] LinearMap.ker (C.d 1 2 rfl)
  classesOne : D.classOne.comp cyclesOne = coordinates.toLinearMap
  cyclesTwo : (Fin presentation.generators → R) →ₗ[R] LinearMap.ker (C.d 2 3 rfl)
  classesTwo : D.classTwo.comp cyclesTwo = presentation.classes
  relations : (Fin presentation.relations → R) →ₗ[R] C.X 1
  differential : (C.d 1 2 rfl).comp relations =
    (LinearMap.ker (C.d 2 3 rfl)).subtype.comp (cyclesTwo.comp presentation.differential)

/-- These source lifts exist by finite presentation and projectivity, independently of a trace comparison. -/
theorem liftData_nonempty [Module.Free R H1] [Module.Finite R H1] [Module.Finite R H2]
    (D : CohomologyData C H1 H2) : Nonempty (LiftData C H1 H2 D) := by
  classical
  let P : Presentation (R := R) H2 := (presentation_nonempty H2).some
  obtain ⟨z2, hz2⟩ := lift_generators C H1 H2 D P
  obtain ⟨frel, hfrel⟩ := lift_relations C H1 H2 D P z2 hz2
  obtain ⟨z1, hz1⟩ := lift_first_classes C H1 H2 D
  let I := Module.Free.ChooseBasisIndex R H1
  let b := (Module.Free.chooseBasis R H1).reindex (Fintype.equivFin I)
  refine ⟨⟨P, Fintype.card I, b.equivFun.symm, z1.comp b.equivFun.symm.toLinearMap,
    ?_, z2, hz2, frel, hfrel⟩⟩
  rw [← LinearMap.comp_assoc, hz1, LinearMap.id_comp]

variable {C H1 H2} {D : CohomologyData C H1 H2} (I : LiftData C H1 H2 D)

/-- The finite source differential is the specified relation differential on its relation coordinates. -/
def differential : (Fin (I.presentation.relations + I.rankOne) → R) →ₗ[R]
    (Fin I.presentation.generators → R) :=
  I.presentation.differential.comp (relationCoordinates I.presentation.relations I.rankOne)

/-- The actual degree-one source map combines relation primitives and independent first classes. -/
def one : (Fin (I.presentation.relations + I.rankOne) → R) →ₗ[R] C.X 1 :=
  I.relations.comp (relationCoordinates I.presentation.relations I.rankOne) +
    (LinearMap.ker (C.d 1 2 rfl)).subtype.comp
      (I.cyclesOne.comp (cohomologyCoordinates I.presentation.relations I.rankOne))

/-- Degree two of the source realizes the specified generators as actual cycles. -/
def two : (Fin I.presentation.generators → R) →ₗ[R] C.X 2 :=
  (LinearMap.ker (C.d 2 3 rfl)).subtype.comp I.cyclesTwo

/-- The finite source differential square is derived from the actual relation lifts. -/
theorem one_d : (C.d 1 2 rfl).comp (one I) = (two I).comp (differential I) := by
  apply LinearMap.ext
  intro x
  change C.d 1 2 rfl (I.relations (relationCoordinates _ _ x) +
    (I.cyclesOne (cohomologyCoordinates _ _ x)).val) = _
  rw [map_add, (I.cyclesOne (cohomologyCoordinates _ _ x)).property, add_zero]
  exact LinearMap.congr_fun I.differential _

/-- The realized finite degree-two source is a cycle map. -/
theorem two_d : (C.d 2 3 rfl).comp (two I) = 0 := by
  apply LinearMap.ext
  intro x
  exact (I.cyclesTwo x).property

/-- The specific finite based source realization of the specified source cohomology lifts. -/
def realization : GHom (twoTermBased (differential I)).toGCx C :=
  FiniteSourceCoordinates.realization (differential I) C (one I) (two I) (one_d I) (two_d I)

/-- The degree-one realization is exactly the specified cycle/primitive map on coordinates. -/
theorem realization_one (u : Fin (I.presentation.relations + I.rankOne) → R) :
    (realization I).f 1 1 rfl (oddCoordinates (differential I) u) = one I u := rfl

/-- The degree-two realization is exactly the specified generator-cycle map. -/
theorem realization_two (u : Fin I.presentation.generators → R) :
    (realization I).f 2 2 rfl (evenCoordinates (differential I) u) = two I u := rfl

/-- Joining the relation and first-class coordinates preserves both prescribed projections. -/
theorem join_relation (r s : ℕ) (u : Fin r → R) (v : Fin s → R) :
    relationCoordinates r s (Fin.append u v) = u := by
  funext i
  exact Fin.append_left u v i

/-- The second prescribed projection reads the first-class coordinates of the same join. -/
theorem join_cohomology (r s : ℕ) (u : Fin r → R) (v : Fin s → R) :
    cohomologyCoordinates r s (Fin.append u v) = v := by
  funext i
  exact Fin.append_right u v i

/-- Relation-free degree-one source coordinates realize the prescribed first cohomology classes. -/
theorem one_join_zero (v : Fin I.rankOne → R) :
    one I (Fin.append (0 : Fin I.presentation.relations → R) v) = (I.cyclesOne v).val := by
  change I.relations (relationCoordinates _ _ (Fin.append 0 v)) +
    (I.cyclesOne (cohomologyCoordinates _ _ (Fin.append 0 v))).val = _
  rw [join_relation, join_cohomology, map_zero, zero_add]

/-- The joined independent first classes are actual cycles of the finite source. -/
theorem differential_join_zero (v : Fin I.rankOne → R) :
    differential I (Fin.append (0 : Fin I.presentation.relations → R) v) = 0 := by
  change I.presentation.differential (relationCoordinates _ _ (Fin.append 0 v)) = 0
  rw [join_relation, map_zero]

/-- Every actual degree-one source cycle is realized by a relation-free finite source cycle modulo an actual boundary. -/
theorem one_surjective_on_classes (z : C.X 1) (hz : C.d 1 2 rfl z = 0) :
    ∃ (u : Fin (I.presentation.relations + I.rankOne) → R) (y : C.X 0),
      differential I u = 0 ∧ one I u + C.d 0 1 rfl y = z := by
  let c : LinearMap.ker (C.d 1 2 rfl) := ⟨z, hz⟩
  let v := I.coordinates.symm (D.classOne c)
  have hv : D.classOne (I.cyclesOne v) = D.classOne c :=
    (LinearMap.congr_fun I.classesOne v).trans (I.coordinates.apply_symm_apply (D.classOne c))
  have hzero : D.classOne (c - I.cyclesOne v) = 0 := by rw [map_sub, hv, sub_self]
  obtain ⟨y, hy⟩ := (D.one_kernel _).mp hzero
  refine ⟨Fin.append 0 v, y, differential_join_zero I v, ?_⟩
  rw [one_join_zero, hy]
  exact add_sub_cancel _ _

/-- The realized degree-one finite cycle has zero relation coordinates, because the actual presentation relation map is injective. -/
theorem one_cycle_relations_zero (u : Fin (I.presentation.relations + I.rankOne) → R)
    (hu : differential I u = 0) : relationCoordinates I.presentation.relations I.rankOne u = 0 := by
  apply I.presentation.injective
  change I.presentation.differential (relationCoordinates _ _ u) = I.presentation.differential 0
  rw [map_zero]
  exact hu

/-- The specified finite source map is injective on actual degree-one cohomology classes. -/
theorem one_injective_on_classes (u : Fin (I.presentation.relations + I.rankOne) → R)
    (hu : differential I u = 0) (hboundary : ∃ y : C.X 0, C.d 0 1 rfl y = one I u) : u = 0 := by
  have hrel := one_cycle_relations_zero I u hu
  have hclass : D.classOne (I.cyclesOne (cohomologyCoordinates _ _ u)) = 0 := by
    apply (D.one_kernel _).mpr
    obtain ⟨y, hy⟩ := hboundary
    refine ⟨y, ?_⟩
    change C.d 0 1 rfl y = _
    change C.d 0 1 rfl y = I.relations (relationCoordinates _ _ u) +
      (I.cyclesOne (cohomologyCoordinates _ _ u)).val at hy
    simpa only [hrel, map_zero, zero_add] using hy
  have hco : cohomologyCoordinates I.presentation.relations I.rankOne u = 0 := by
    apply I.coordinates.injective
    rw [map_zero]
    exact (LinearMap.congr_fun I.classesOne _).symm.trans hclass
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact congrFun hrel j
  · exact congrFun hco j

/-- Every actual degree-two source cycle is realized by the fixed finite generators modulo an actual boundary. -/
theorem two_surjective_on_classes (z : C.X 2) (hz : C.d 2 3 rfl z = 0) :
    ∃ (u : Fin I.presentation.generators → R) (y : C.X 1), two I u + C.d 1 2 rfl y = z := by
  let c : LinearMap.ker (C.d 2 3 rfl) := ⟨z, hz⟩
  obtain ⟨u, hu⟩ := I.presentation.surjective (D.classTwo c)
  have hv : D.classTwo (I.cyclesTwo u) = D.classTwo c :=
    (LinearMap.congr_fun I.classesTwo u).trans hu
  have hzero : D.classTwo (c - I.cyclesTwo u) = 0 := by rw [map_sub, hv, sub_self]
  obtain ⟨y, hy⟩ := (D.two_kernel _).mp hzero
  exact ⟨u, y, by change (I.cyclesTwo u).val + _ = z; rw [hy]; exact add_sub_cancel _ _⟩

/-- Actual degree-two boundaries under the realized source map are precisely the finite source relation image. -/
theorem two_injective_on_classes (u : Fin I.presentation.generators → R)
    (hboundary : ∃ y : C.X 1, C.d 1 2 rfl y = two I u) :
    ∃ v : Fin (I.presentation.relations + I.rankOne) → R, differential I v = u := by
  have hzero : D.classTwo (I.cyclesTwo u) = 0 := (D.two_kernel _).mpr hboundary
  have hclass : I.presentation.classes u = 0 :=
    (LinearMap.congr_fun I.classesTwo u).symm.trans hzero
  obtain ⟨v, hv⟩ := I.presentation.exact u hclass
  refine ⟨Fin.append v 0, ?_⟩
  change I.presentation.differential (relationCoordinates _ _ (Fin.append v 0)) = u
  rw [join_relation]
  exact hv

/-- Exactness away from degrees one and two is source-support information, not a comparison invertibility assumption. -/
def ExactOutside (C : GCx R) : Prop :=
  ∀ (n : ℤ), n ≠ 1 → n ≠ 2 → ∀ z : C.X n, C.d n (n + 1) rfl z = 0 →
    ∃ y : C.X (n - 1), C.d (n - 1) n (by omega) y = z

/-- The specified cycle/relation realization is a quasi-isomorphism once the actual source has the stated support. -/
theorem realization_quasiIso (hother : ExactOutside C) : QuasiIso (GHom.toCC (realization I)) := by
  apply SourceAlgebra.quasiIso_of_cycle_comparisons
  · intro n z hz
    by_cases hn1 : n = 1
    · subst n
      obtain ⟨u, y, hu, hy⟩ := one_surjective_on_classes I z hz
      refine ⟨oddCoordinates (differential I) u, y, ?_, ?_⟩
      · change (twoTermBased (differential I)).toGCx.d 1 2 rfl
          (oddCoordinates (differential I) u) = 0
        rw [oddCoordinates_d, hu, map_zero]
      · rw [realization_one]
        exact hy
    · by_cases hn2 : n = 2
      · subst n
        obtain ⟨u, y, hy⟩ := two_surjective_on_classes I z hz
        exact ⟨evenCoordinates (differential I) u, y, even_d_zero _ _, by rw [realization_two]; exact hy⟩
      · obtain ⟨y, hy⟩ := hother n hn1 hn2 z hz
        exact ⟨0, y, map_zero _, by rw [map_zero, zero_add]; exact hy⟩
  · intro n x hx hb
    by_cases hn1 : n = 1
    · subst n
      have hd : differential I (oddProjection (differential I) x) = 0 := by
        have h := hx
        change (twoTermBased (differential I)).toGCx.d 1 2 rfl x = 0 at h
        rw [← odd_reconstruct (differential I) x, oddCoordinates_d] at h
        have hp := congrArg (evenProjection (differential I)) h
        exact hp
      have hboundary : ∃ y : C.X 0, C.d 0 1 rfl y =
          one I (oddProjection (differential I) x) := by
        obtain ⟨y, hy⟩ := hb
        rw [← odd_reconstruct (differential I) x, realization_one] at hy
        exact ⟨y, hy⟩
      have hu : oddProjection (differential I) x = 0 :=
        one_injective_on_classes I _ hd hboundary
      refine ⟨0, ?_⟩
      rw [map_zero, ← odd_reconstruct (differential I) x, hu, map_zero]
    · by_cases hn2 : n = 2
      · subst n
        have hboundary : ∃ y : C.X 1, C.d 1 2 rfl y =
            two I (evenProjection (differential I) x) := by
          obtain ⟨y, hy⟩ := hb
          rw [← even_reconstruct (differential I) x, realization_two] at hy
          exact ⟨y, hy⟩
        obtain ⟨v, hv⟩ := two_injective_on_classes I (evenProjection (differential I) x) hboundary
        refine ⟨oddCoordinates (differential I) v, ?_⟩
        change (twoTermBased (differential I)).toGCx.d 1 2 rfl (oddCoordinates (differential I) v) = x
        rw [oddCoordinates_d, hv, even_reconstruct]
      · haveI := source_subsingleton (differential I) n hn1 hn2
        exact ⟨0, Subsingleton.elim _ _⟩

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSourceVerified

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSupport

open CategoryTheory
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralFiniteBoundary

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Type) [AddCommGroup A] [DistribMulAction G A]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A]

/-- Higher-degree exactness of the actual finite coefficient cochains, stated before any local comparison. -/
def FiniteHigherExact : Prop :=
  ∀ (a k : ℕ) (z : (finiteIntegralComplex G A a).X (k + 3)),
    ((finiteIntegralComplex G A a).d (k + 3) (k + 4)).hom z = 0 →
    ∃ y : (finiteIntegralComplex G A a).X (k + 2),
      ((finiteIntegralComplex G A a).d (k + 2) (k + 3)).hom y = z

/-- Actual integral support above degree two, phrased entirely in genuine cochains. -/
def IntegralHigherExact : Prop :=
  ∀ (k : ℕ) (z : (integralComplex G A).X (k + 3)),
    ((integralComplex G A).d (k + 3) (k + 4)).hom z = 0 →
    ∃ y : (integralComplex G A).X (k + 2), ((integralComplex G A).d (k + 2) (k + 3)).hom y = z

/-- Finite degree-two class groups and genuine finite higher exactness prove actual integral support, via compatible primitive classes. -/
theorem integralHigherExact_of_finite
    (hcoeff : ∀ a, Function.Surjective (coefficientTransition G A a))
    (H : ℕ → Type) [∀ a, AddCommGroup (H a)] [∀ a, Finite (H a)]
    (q : ∀ a, LinearMap.ker ((finiteIntegralComplex G A a).d 2 3).hom →+ H a)
    (hq : ∀ a x, q a x = 0 ↔ ∃ y : (finiteIntegralComplex G A a).X 1,
      ((finiteIntegralComplex G A a).d 1 2).hom y = x.val)
    (hhigh : FiniteHigherExact G A) : IntegralHigherExact G A := by
  intro k z hz
  rcases k with _ | k
  · apply boundary_of_finite_boundaries G A 1 hcoeff H q hq z
    intro a
    apply hhigh a 0 (((reduceCochains G A a).f 3).hom z)
    rw [← reduceCochains_d, hz, map_zero]
  · change ∃ y : (integralComplex G A).X (k + 3),
      ((integralComplex G A).d (k + 3) (k + 4)).hom y = z
    change ((integralComplex G A).d (k + 4) (k + 5)).hom z = 0 at hz
    apply boundary_of_finite_boundaries G A (k + 2) hcoeff (fun _ => PUnit)
      (fun _ => (0 : LinearMap.ker ((finiteIntegralComplex G A _).d (k + 3) (k + 4)).hom →+ PUnit))
      (fun a c => ⟨fun _ => hhigh a k c.val c.property, fun _ => rfl⟩) z
    intro a
    apply hhigh a (k + 1) (((reduceCochains G A a).f (k + 4)).hom z)
    rw [← reduceCochains_d, hz, map_zero]

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSupport

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSourceResolution

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSelfDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualConeModels
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTransport
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSupport

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- The fixed finite point-coefficient higher exactness obligation, independent of the source resolution and trace comparison. -/
abbrev FinitePointHigherExact :=
  FiniteHigherExact (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B)

/-- Actual finite second cohomology and coefficient transitions lift the independent finite support assertion integrally. -/
theorem point_integral_higher (hF : MilneFiniteLocalDualityPrint)
    (hhigh : FinitePointHigherExact K w B) :
    IntegralHigherExact (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) := by
  let H (a : ℕ) := H2 (Field.absoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a)
  letI : ∀ a, Finite (H a) := fun a => SourceSecondCohomology.finite_second_level K w B hF a
  exact integralHigherExact_of_finite _ _ (SourceSecondCohomology.point_transition_surjective K w B) H
    (fun a => kerToH2 (k := ℤ_[2]) (G := Field.absoluteGaloisGroup (w.adicCompletion K))
      (M := FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) a))
    (fun _ c => kerToH2_eq_zero_iff c) hhigh

/-- In all positive degrees after one, the ordinary cone differential is the actual Galois-cochain differential. -/
theorem cone_d_nat_after_one (n : ℕ) (hn : 1 ≤ n) (x : (localQuotientCone K w B).X n) :
    (localQuotientCone K w B).d n (n + 1) rfl x =
      (((pointComplex (w.adicCompletion K) B).d n (n + 1)).hom x.1, 0) := by
  haveI : Subsingleton ((localCondition K w B).X ((n : ℤ) + 1)) :=
    SelfDualCore.presentationCx_vanishes _ _ _ _ (by omega)
  haveI : Subsingleton ((localCondition K w B).X ((n : ℤ) + 1 + 1)) :=
    SelfDualCore.presentationCx_vanishes _ _ _ _ (by omega)
  apply Prod.ext
  · have hx : x.2 = 0 := Subsingleton.elim _ _
    change (localCochains K w B).d n (n + 1) rfl x.1 +
      (localConditionMap K w B).f (n + 1) (n + 1) rfl x.2 =
        (localCochains K w B).d n (n + 1) rfl x.1
    rw [hx, map_zero, add_zero]
  · exact Subsingleton.elim _ _

/-- Genuine integral point higher exactness gives the actual quotient-cone upper support, with its explicit transported primitives. -/
theorem cone_nat_upper_exact
    (hhigh : IntegralHigherExact (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B))
    (k : ℕ) (z : (localQuotientCone K w B).X (k + 3))
    (hz : (localQuotientCone K w B).d (k + 3) (k + 4) rfl z = 0) :
    ∃ y : (localQuotientCone K w B).X (k + 2),
      (localQuotientCone K w B).d (k + 2) (k + 3) rfl y = z := by
  have hzP : ((pointComplex (w.adicCompletion K) B).d (k + 3) (k + 4)).hom z.1 = 0 := by
    have h := congrArg Prod.fst hz
    erw [cone_d_nat_after_one K w B (k + 3) (by omega)] at h
    exact h
  have hzA : ((actualIntegralComplex (w.adicCompletion K) B).d (k + 3) (k + 4)).hom
      (((toAlgComplex (w.adicCompletion K) B).f (k + 3)).hom z.1) = 0 := by
    have h := congrArg (fun f => f.hom z.1) ((toAlgComplex (w.adicCompletion K) B).comm (k + 3) (k + 4))
    calc
      _ = ((toAlgComplex (w.adicCompletion K) B).f (k + 4)).hom
          (((pointComplex (w.adicCompletion K) B).d (k + 3) (k + 4)).hom z.1) := h
      _ = 0 := by rw [hzP, map_zero]
  obtain ⟨b, hb⟩ := hhigh k (((toAlgComplex (w.adicCompletion K) B).f (k + 3)).hom z.1) hzA
  refine ⟨(((toSepComplex (w.adicCompletion K) B).f (k + 2)).hom b, 0), ?_⟩
  erw [cone_d_nat_after_one K w B (k + 2) (by omega)]
  apply Prod.ext
  · change ((pointComplex (w.adicCompletion K) B).d (k + 2) (k + 3)).hom
      (((toSepComplex (w.adicCompletion K) B).f (k + 2)).hom b) = z.1
    rw [← toSepComplex_d, hb]
    exact transport_sep_inverse K w B (k + 3) z.1
  · haveI : Subsingleton ((localCondition K w B).X (((k + 2 : ℕ) : ℤ) + 1 + 1)) :=
      SelfDualCore.presentationCx_vanishes _ _ _ _ (by omega)
    exact Subsingleton.elim _ _

/-- The actual cone has exact source support outside degrees one and two from the independent finite coefficient support assertion. -/
theorem cone_exactOutside (hF : MilneFiniteLocalDualityPrint)
    (hhigh : FinitePointHigherExact K w B) :
    FiniteSourceVerified.ExactOutside (localQuotientCone K w B) := by
  intro n hn1 hn2 z hz
  by_cases hn : n ≤ 0
  · exact cone_lower_exact K w B n hn z hz
  · have hpos : 3 ≤ n := by omega
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = (k : ℤ) + 3 := by
      refine ⟨(n - 3).toNat, ?_⟩
      have h : ((n - 3).toNat : ℤ) = n - 3 := Int.toNat_of_nonneg (show 0 ≤ n - 3 by omega)
      omega
    subst n
    obtain ⟨y, hy⟩ := cone_nat_upper_exact K w B (point_integral_higher K w B hF hhigh) k z hz
    refine ⟨(idGHom (localQuotientCone K w B)).f ((k : ℤ) + 2) ((k : ℤ) + 3 - 1) (by omega) y, ?_⟩
    have h := (idGHom (localQuotientCone K w B)).comm
      ((k : ℤ) + 2) ((k : ℤ) + 3) ((k : ℤ) + 3 - 1) ((k : ℤ) + 3)
      (by omega) (by omega) (by omega) rfl y
    rw [idGHom_f_self, hy] at h
    exact h.symm

/-- The finite source lifts are selected from the actual cone class maps and genuine source cohomology modules. -/
def liftData (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint) :
    FiniteSourceVerified.LiftData (localQuotientCone K w B)
      (SourceFirstCohomology.sourceOne K w B) (SourceSecondCohomology.sourceTwo K w B)
        (cohomologyData K w B) := by
  haveI := SourceFirstCohomology.sourceOne_finite K w B hM
  haveI := SourceFirstCohomology.sourceOne_free K w B hM
  haveI := SourceSecondCohomology.sourceTwo_moduleFinite K w B hF
  exact (FiniteSourceVerified.liftData_nonempty _ _ _ (cohomologyData K w B)).some

/-- The actual finite two-term source resolution, including its full quasi-isomorphism, is constructed without inverting the self-dual comparison. -/
def basedResolution (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hhigh : FinitePointHigherExact K w B) :
    ActualBasedComparison.TwoTermConeBasedResolution K w B
      ((liftData K w B hM hF).presentation.relations + (liftData K w B hM hF).rankOne)
      (liftData K w B hM hF).presentation.generators where
  differential := FiniteSourceVerified.differential (liftData K w B hM hF)
  realization := FiniteSourceVerified.realization (liftData K w B hM hF)
  quasiIso := FiniteSourceVerified.realization_quasiIso (liftData K w B hM hF)
    (cone_exactOutside K w B hF hhigh)

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSourceResolution

end

/-!
# The higher-degree specialization of finite local duality

Milne, Arithmetic Duality Theorems, second edition, Chapter I, Corollary 2.3,
printed page 28, states the finite coefficient duality for every degree r ≥ 1.
For r ≥ 3 the complementary group is in negative degree and is zero.
Specializing to elliptic torsion and to roots of unity gives the finite
support statements below. This is the all-degree part of the same cited
corollary, not a statement of integral Kummer self-duality.

The earlier low-degree parameter contains only its degrees one and two.
The omitted higher-degree part is recorded explicitly and separately here;
this parameter has no unconditional inhabitant. No integral contraction,
comparison bijectivity, or integral trace exactness is a field of it.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteLocalDegreeBound

open TauCeti TauCeti.ContCohomology NumberField IsDedekindDomain
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSupport

/-- The finite higher-degree part of Milne I.2.3 in the two actual coefficient families used here.
It is a printed Prop parameter, not a new global axiom or a premise about the comparison cone. -/
structure MilneFiniteDegreeBoundPrint : Prop where
  elliptic : ∀ (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (B : WeierstrassCurve F) [B.IsElliptic],
      FiniteHigherExact (Field.absoluteGaloisGroup F) (ZInQ.Manuscript.RC.CoefModules.PtAlg F B)
  cyclotomic : ∀ (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F],
      FiniteHigherExact (AbsoluteGaloisGroup F) (UnitsCoeff F)

/-- The actual elliptic finite coefficient modules satisfy the finiteness scope of the cited corollary. -/
theorem finite_elliptic_levels (F : Type) [Field F] [DecidableEq F] [CharZero F]
    (B : WeierstrassCurve F) [B.IsElliptic] (a : ℕ) :
    Finite (FiniteTateCoeff (Field.absoluteGaloisGroup F) (ZInQ.Manuscript.RC.CoefModules.PtAlg F B) a) := by
  change Finite (TateModuleLevel 2 (ZInQ.Manuscript.RC.CoefModules.PtAlg F B) a)
  exact Nat.finite_of_card_ne_zero (by rw [IntegralKummer.geometricLevel_card F B]; positivity)

/-- Every actual finite Tate coefficient level is killed by its prescribed two-power. -/
theorem finite_level_killed (G : Type) [Group G] (A : Type) [AddCommGroup A] [DistribMulAction G A]
    (a : ℕ) (x : FiniteTateCoeff G A a) : (2 ^ a : ℕ) • x = 0 := by
  apply Subtype.ext
  exact AddSubgroup.torsionBy.nsmul_iff.mp x.property

/-- Finite third-degree exactness for the actual trace target is the degree-three specialization of the cited finite support input. -/
theorem finiteThirdDegreeExact_of_print (hH : MilneFiniteDegreeBoundPrint)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] : TraceThirdDegree.FiniteThirdDegreeExact F := by
  intro a z hz
  exact hH.cyclotomic F a 0 z hz

/-- The independently proved primitive-class lifting turns that finite statement into genuine integral trace-target exactness. -/
theorem actualThirdDegreeExact_of_print (hH : MilneFiniteDegreeBoundPrint)
    (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] : FiniteCycleLift.ThirdDegreeExact F :=
  TraceThirdDegree.actual_third_exact_of_finite F (finiteThirdDegreeExact_of_print hH F)

/-- The actual source resolution now needs only the explicitly cited finite local-duality parameters; it has its genuine quasi-isomorphism field. -/
def basedResolution_of_print
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint) (hH : MilneFiniteDegreeBoundPrint)
    (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic] :=
  ActualSourceResolution.basedResolution K w B hM hF (hH.elliptic (w.adicCompletion K) B)

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteLocalDegreeBound

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.CoordinateReduction

open CategoryTheory TauCeti
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction

variable (G : Type) [Group G] (A : Type) [AddCommGroup A] [DistribMulAction G A]

/-- The actual first Tate projection has precisely the multiplication-by-two kernel. -/
theorem coefficient_first_kernel (x : IntegralTateCoeff G A) :
    coefficientProjection G A 1 x = 0 ↔ ∃ y : IntegralTateCoeff G A, (2 : ℤ_[2]) • y = x := by
  constructor
  · intro hx
    have hxraw : TateModule.proj (p := 2) (A := A) 1 (show TateModule 2 A from x) = 0 := hx
    obtain ⟨y, hy⟩ := TateModule.proj_eq_zero_iff.mp hxraw
    refine ⟨(show IntegralTateCoeff G A from y), ?_⟩
    change ((2 : ℕ) : ℤ_[2]) • (show IntegralTateCoeff G A from y) = x
    rw [Nat.cast_smul_eq_nsmul]
    exact hy.symm
  · rintro ⟨y, hy⟩
    have hyraw : (show TateModule 2 A from x) = (2 ^ 1 : ℕ) • (show TateModule 2 A from y) := by
      change ((2 : ℕ) : ℤ_[2]) • y = x at hy
      rw [Nat.cast_smul_eq_nsmul] at hy
      exact hy.symm
    exact TateModule.proj_eq_zero_iff.mpr ⟨(show TateModule 2 A from y), hyraw⟩

/-- The actual Tate coefficients have regular multiplication by two. -/
theorem coefficient_two_regular (x : IntegralTateCoeff G A) (hx : (2 : ℤ_[2]) • x = 0) : x = 0 := by
  change ((2 : ℕ) : ℤ_[2]) • x = 0 at hx
  rw [Nat.cast_smul_eq_nsmul] at hx
  have hraw : (2 ^ 1 : ℕ) • (show TateModule 2 A from x) = 0 := hx
  exact TateModule.eq_zero_of_pow_nsmul_eq_zero hraw

/-- Multiplication by two, with its actual first-projection kernel as codomain. -/
def twoIntoKernel : IntegralTateCoeff G A →ₗ[ℤ_[2]] LinearMap.ker (coefficientProjection G A 1) where
  toFun x := ⟨(2 : ℤ_[2]) • x, (coefficient_first_kernel G A _).mpr ⟨x, rfl⟩⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' r x := Subtype.ext (by
    change (2 : ℤ_[2]) • (r • x) = r • ((2 : ℤ_[2]) • x)
    rw [smul_smul, smul_smul, mul_comm])

/-- The specific multiplication map bijectively identifies the Tate module with the kernel of its actual finite projection. -/
theorem twoIntoKernel_bijective : Function.Bijective (twoIntoKernel G A) := by
  constructor
  · intro x y h
    have hv : (2 : ℤ_[2]) • (x - y) = 0 := by
      rw [smul_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val h)
    exact sub_eq_zero.mp (coefficient_two_regular G A _ hv)
  · intro x
    obtain ⟨y, hy⟩ := (coefficient_first_kernel G A x.val).mp x.property
    exact ⟨y, Subtype.ext hy⟩

/-- Canonical division by two on the kernel is the inverse of the actual multiplication map. -/
def divisionEquiv : IntegralTateCoeff G A ≃ₗ[ℤ_[2]] LinearMap.ker (coefficientProjection G A 1) :=
  LinearEquiv.ofBijective (twoIntoKernel G A) (twoIntoKernel_bijective G A)

variable [TopologicalSpace A] [DiscreteTopology A]

/-- The actual multiplication-to-kernel map is continuous in the inverse-limit topology. -/
theorem twoIntoKernel_continuous : Continuous (twoIntoKernel G A) := by
  have h : Continuous (fun x : IntegralTateCoeff G A => (2 : ℤ_[2]) • x) := by
    have hnat : Continuous (fun x : IntegralTateCoeff G A => (2 : ℕ) • x) := continuous_id.nsmul 2
    convert hnat using 1
    funext x
    exact Nat.cast_smul_eq_nsmul (R := ℤ_[2]) 2 x
  exact h.subtype_mk _

variable [CompactSpace (IntegralTateCoeff G A)]

/-- The inverse of this actual multiplication map is continuous, by compactness and the Hausdorff topology of the kernel. -/
theorem division_inverse_continuous : Continuous (divisionEquiv G A).symm := by
  haveI : T2Space (IntegralTateCoeff G A) := inferInstanceAs (T2Space (TateModule 2 A))
  let e := (divisionEquiv G A).toEquiv
  have h : Continuous e := twoIntoKernel_continuous G A
  exact (e.toHomeomorphOfContinuousClosed h h.isClosedMap).symm.continuous

variable [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousSMul G A]

/-- Actual integral cochain multiplication by two is regular in every degree. -/
theorem cochain_two_regular (k : ℕ) (c : (integralComplex G A).X k)
    (hc : (2 : ℤ_[2]) • c = 0) : c = 0 := by
  apply Subtype.ext
  funext s
  change cfun c s = 0
  apply coefficient_two_regular G A
  have h := congrArg (fun c => cfun c s) hc
  exact h

/-- The fixed actual cochain projection is onto whenever its actual coefficient projection is onto. -/
theorem first_cochain_surjective (k : ℕ)
    (hcoeff : Function.Surjective (coefficientProjection G A 1)) :
    Function.Surjective ((reduceCochains G A 1).f k).hom := by
  classical
  choose sec hsec using hcoeff
  intro c
  let b : (integralComplex G A).X k :=
    ⟨fun s => sec (cfun c s), (continuous_of_discreteTopology (f := sec)).comp c.property⟩
  exact ⟨b, Subtype.ext (funext fun s => hsec (cfun c s))⟩

/-- The kernel of the fixed actual finite cochain projection is exactly the actual multiplication-by-two image. -/
theorem first_cochain_kernel (k : ℕ) (c : (integralComplex G A).X k) :
    ((reduceCochains G A 1).f k).hom c = 0 ↔
      ∃ b : (integralComplex G A).X k, (2 : ℤ_[2]) • b = c := by
  constructor
  · intro hc
    let φ : (Fin k → G) → LinearMap.ker (coefficientProjection G A 1) := fun s =>
      ⟨cfun c s, by
        have h := congrArg (fun c => cfun c s) hc
        exact h⟩
    have hφ : Continuous φ := c.property.subtype_mk _
    let b : (integralComplex G A).X k :=
      ⟨fun s => (divisionEquiv G A).symm (φ s), (division_inverse_continuous G A).comp hφ⟩
    refine ⟨b, Subtype.ext (funext fun s => ?_)⟩
    have h := congrArg Subtype.val ((divisionEquiv G A).apply_symm_apply (φ s))
    exact h
  · rintro ⟨b, hb⟩
    apply Subtype.ext
    funext s
    have h := (coefficient_first_kernel G A (cfun c s)).mpr ⟨cfun b s, by
      exact congrArg (fun c => cfun c s) hb⟩
    exact h

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.CoordinateReduction

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedReduction

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion

variable {R S : Type} [CommRing R] [CommRing S] (π : R →+* S)

/-- Restriction of scalars preserves the actual carrier and differential of each cochain degree. -/
def restrictCx (C : GCx S) : GCx R where
  X n := (ModuleCat.restrictScalars π).obj (C.X n)
  d i j h := ((ModuleCat.restrictScalars π).map (ModuleCat.ofHom (C.d i j h))).hom
  d_d i j k hij hjk x := C.d_d i j k hij hjk x

/-- The same scalar restriction on a specified cochain map. -/
def restrictHom {C D : GCx S} (f : GHom C D) : GHom (restrictCx π C) (restrictCx π D) where
  f i j h := ((ModuleCat.restrictScalars π).map (ModuleCat.ofHom (f.f i j h))).hom
  comm i j i' j' h hi hj h' x := f.comm i j i' j' h hi hj h' x

variable {κe κo : Type} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]
  (C : BasedCx R κe κo)

/-- Reduction of the supported coordinates in a specified based degree. -/
def projection (n : ℤ) : C.toGCx.X n →ₗ[R] (restrictCx π (C.map π).toGCx).X n where
  toFun x := ⟨fun i => π (x.val i), by
    intro i hi
    change C.deg i ≠ n at hi
    have hz : x.val i = 0 := x.property i hi
    exact (congrArg π hz).trans (map_zero π)⟩
  map_add' x y := Subtype.ext (by funext i; exact map_add π _ _)
  map_smul' r x := Subtype.ext (by
    funext i
    change π (r * x.val i) = π r * π (x.val i)
    exact map_mul π _ _)

/-- The full differential matrix is reduced by the same actual coefficient map. -/
theorem total_matrix_map : (C.map π).dTot = C.dTot.map π := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change (0 : S) = π (0 : R)
    exact (map_zero π).symm
  · rfl
  · rfl
  · change (0 : S) = π (0 : R)
    exact (map_zero π).symm

/-- Fixed supported-coordinate reduction commutes with the actual based differential. -/
theorem projection_comm (i j : ℤ) (h : i + 1 = j) (x : C.toGCx.X i) :
    projection π C j (C.toGCx.d i j h x) =
      (restrictCx π (C.map π).toGCx).d i j h (projection π C i x) := by
  apply Subtype.ext
  change (fun k => π ((C.dTot *ᵥ x.val) k)) = (C.map π).dTot *ᵥ (fun k => π (x.val k))
  rw [total_matrix_map]
  funext k
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

/-- The actual based-source coefficient reduction is a cochain map in all degrees. -/
def projectionHom : GHom C.toGCx (restrictCx π (C.map π).toGCx) where
  f i j h := h ▸ projection π C i
  comm i j i' j' h hi hj h' x := by
    subst hi
    subst h'
    subst h
    exact projection_comm π C i (i + 1) hj x

/-- A ring reduction by two is required only on its prescribed scalar map. -/
structure TwoRingReduction : Prop where
  onto : Function.Surjective π
  kernel : ∀ r, π r = 0 ↔ ∃ s : R, (2 : R) * s = r
  regular : ∀ r : R, (2 : R) * r = 0 → r = 0

variable (P : TwoRingReduction π)

include P in
/-- The fixed coordinate projection of every actual based degree is onto. -/
theorem projection_surjective (n : ℤ) : Function.Surjective (projection π C n) := by
  classical
  choose sec hsec using P.onto
  intro x
  let y : C.toGCx.X n := ⟨fun i => if C.deg i = n then sec (x.val i) else 0, by
    intro i hi
    exact ite_eq_right hi⟩
  refine ⟨y, Subtype.ext (funext fun i => ?_)⟩
  by_cases hi : C.deg i = n
  · change π (if C.deg i = n then sec (x.val i) else 0) = x.val i
    rw [ite_eq_left hi, hsec]
  · change π (if C.deg i = n then sec (x.val i) else 0) = x.val i
    rw [ite_eq_right hi, map_zero]
    exact (x.property i hi).symm

include P in
/-- The fixed coordinate projection has exactly the actual multiplication-by-two kernel. -/
theorem projection_kernel (n : ℤ) (x : C.toGCx.X n) :
    projection π C n x = 0 ↔ ∃ y : C.toGCx.X n, (2 : R) • y = x := by
  classical
  constructor
  · intro hx
    have hvals : ∀ i, ∃ y : R, (2 : R) * y = x.val i := by
      intro i
      apply (P.kernel (x.val i)).mp
      exact congrArg (fun x => x.val i) hx
    choose vals hvals using hvals
    let y : C.toGCx.X n := ⟨vals, by
      intro i hi
      apply P.regular
      exact (hvals i).trans (x.property i hi)⟩
    refine ⟨y, Subtype.ext (funext fun i => ?_)⟩
    exact hvals i
  · rintro ⟨y, hy⟩
    apply Subtype.ext
    funext i
    apply (P.kernel (x.val i)).mpr
    exact ⟨y.val i, congrArg (fun x => x.val i) hy⟩

include P in
/-- Every finite based source degree has regular multiplication by two. -/
theorem projection_source_regular (n : ℤ) (x : C.toGCx.X n) (hx : (2 : R) • x = 0) : x = 0 := by
  apply Subtype.ext
  funext i
  exact P.regular (x.val i) (congrArg (fun x => x.val i) hx)

/-- The actual two-adic scalar reduction satisfies the required ring exactness and regularity. -/
theorem padic_ring_reduction : TwoRingReduction (PadicInt.toZMod (p := 2)) := by
  refine ⟨ZMod.ringHom_surjective PadicInt.toZMod, ?_, ?_⟩
  · intro r
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s, hs.symm⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, hs.symm⟩
  · intro r hr
    exact (mul_eq_zero.mp hr).resolve_left (two_ne_zero : (2 : ℤ_[2]) ≠ 0)

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedReduction

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.QuasiIsoReduction

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {R : Type} [CommRing R] {C D : GCx R}

/-- Exact reduction by two is recorded on a specified cochain map, not an unrelated quotient isomorphism. -/
structure ExactTwoReduction (p : GHom C D) : Prop where
  onto : ∀ n, Function.Surjective (p.f n n rfl)
  kernel : ∀ n x, p.f n n rfl x = 0 ↔ ∃ y : C.X n, (2 : R) • y = x
  regular : ∀ n (x : C.X n), (2 : R) • x = 0 → x = 0

/-- Acyclicity passes through the actual degreewise reduction by two by lifting and correcting cycles. -/
theorem acyclic_of_exact_reduction (p : GHom C D) (P : ExactTwoReduction p) (hC : GAcyclic C) : GAcyclic D := by
  intro i n k hin hnk z hz
  obtain ⟨x, hx⟩ := P.onto n z
  have hdx : p.f k k rfl (C.d n k hnk x) = 0 := by
    rw [p.comm n k n k rfl hnk hnk rfl x, hx]
    exact hz
  obtain ⟨w, hw⟩ := (P.kernel k _).mp hdx
  have hdw : C.d k (k + 1) rfl w = 0 := by
    apply P.regular (k + 1)
    have h : (2 : R) • C.d k (k + 1) rfl w = 0 := by
      rw [← map_smul, hw]
      exact C.d_d n k (k + 1) hnk rfl x
    exact h
  obtain ⟨u, hu⟩ := hC n k (k + 1) hnk rfl w hdw
  have hcorrected : C.d n k hnk (x - (2 : R) • u) = 0 := by
    rw [map_sub, map_smul, hu, ← hw, sub_self]
  obtain ⟨y, hy⟩ := hC i n k hin hnk (x - (2 : R) • u) hcorrected
  refine ⟨p.f i i rfl y, ?_⟩
  have hpu : p.f n n rfl ((2 : R) • u) = 0 := (P.kernel n _).mpr ⟨u, rfl⟩
  rw [← p.comm i n i n rfl hin hin rfl y, hy, map_sub, hpu, sub_zero]
  exact hx

variable {A B AF BF : GCx R} (f : GHom A B) (ff : GHom AF BF)
  (pA : GHom A AF) (pB : GHom B BF)
  (square : ∀ i j h (x : A.X i), pB.f j j rfl (f.f i j h x) = ff.f i j h (pA.f i i rfl x))

/-- The specified coefficient/source reduction square induces the actual cone reduction. -/
def coneReduction : GHom (coneCx f) (coneCx ff) where
  f i j h := (pA.f i j h).prodMap (pB.f (i - 1) (j - 1) (by omega))
  comm i j i' j' hsource hi hj htarget x := by
    subst hi
    subst htarget
    subst hsource
    obtain ⟨a, b⟩ := x
    apply Prod.ext
    · exact pA.comm i (i + 1) i (i + 1) rfl rfl hj rfl a
    · change pB.f (i + 1 - 1) (i + 1 - 1) rfl
        (f.f i (i + 1 - 1) (by omega) a - B.d (i - 1) (i + 1 - 1) (by omega) b) =
      ff.f i (i + 1 - 1) (by omega) (pA.f i i rfl a) -
        BF.d (i - 1) (i + 1 - 1) (by omega) (pB.f (i - 1) (i - 1) rfl b)
      rw [map_sub, square]
      rw [pB.comm (i - 1) (i + 1 - 1) (i - 1) (i + 1 - 1) rfl (by omega) (by omega) rfl b]

/-- Actual exactness and regularity of both specified degreewise projections prove the same facts for the cone reduction. -/
theorem coneReduction_exact (PA : ExactTwoReduction pA) (PB : ExactTwoReduction pB) :
    ExactTwoReduction (coneReduction f ff pA pB square) where
  onto n z := by
    obtain ⟨a, ha⟩ := PA.onto n z.1
    obtain ⟨b, hb⟩ := PB.onto (n - 1) z.2
    exact ⟨(a, b), Prod.ext ha hb⟩
  kernel n x := by
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := (PA.kernel n x.1).mp (congrArg Prod.fst hx)
      obtain ⟨b, hb⟩ := (PB.kernel (n - 1) x.2).mp (congrArg Prod.snd hx)
      exact ⟨(a, b), Prod.ext ha hb⟩
    · rintro ⟨⟨a, b⟩, hx⟩
      apply Prod.ext
      · exact (PA.kernel n _).mpr ⟨a, congrArg Prod.fst hx⟩
      · exact (PB.kernel (n - 1) _).mpr ⟨b, congrArg Prod.snd hx⟩
  regular n x hx :=
    Prod.ext (PA.regular n x.1 (congrArg Prod.fst hx))
      (PB.regular (n - 1) x.2 (congrArg Prod.snd hx))

include square in
/-- The actual reduced cochain map is a quasi-isomorphism, derived from the integral one and its fixed exact reduction square. -/
theorem quasiIso_of_exact_reduction_square
    (PA : ExactTwoReduction pA) (PB : ExactTwoReduction pB)
    (hf : QuasiIso (GHom.toCC f)) : QuasiIso (GHom.toCC ff) := by
  apply SourceAlgebra.quasiIso_of_cone_acyclic
  exact acyclic_of_exact_reduction (coneReduction f ff pA pB square)
    (coneReduction_exact f ff pA pB square PA PB) (coneCx_acyclic_of_quasiIso f hf)

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.QuasiIsoReduction

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.QuasiIsoReduction

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {R : Type} [CommRing R] {A B AF BF : GCx R}
  (f : GHom A B) (pA : GHom A AF) (pB : GHom B BF)
  (PA : ExactTwoReduction pA) (PB : ExactTwoReduction pB)

include PA PB in
/-- The actual integral map followed by target projection kills the source projection kernel. -/
theorem factorKernel (i j : ℤ) (h : i = j) :
    LinearMap.ker (pA.f i i rfl) ≤ LinearMap.ker ((pB.f j j rfl).comp (f.f i j h)) := by
  intro x hx
  obtain ⟨y, hy⟩ := (PA.kernel i x).mp hx
  change pB.f j j rfl (f.f i j h x) = 0
  rw [← hy, map_smul]
  exact (PB.kernel j _).mpr ⟨f.f i j h y, rfl⟩

/-- The prescribed reduced component descends from the actual integral map and the fixed source/target projections. -/
def factorComponent (i j : ℤ) (h : i = j) : AF.X i →ₗ[R] BF.X j :=
  ((LinearMap.ker (pA.f i i rfl)).liftQ ((pB.f j j rfl).comp (f.f i j h))
    (factorKernel f pA pB PA PB i j h)).comp
      (pA.f i i rfl |>.quotKerEquivOfSurjective (PA.onto i)).symm.toLinearMap

/-- The exact representative formula of the reduced component; its square is a theorem. -/
theorem factorComponent_projection (i j : ℤ) (h : i = j) (x : A.X i) :
    factorComponent f pA pB PA PB i j h (pA.f i i rfl x) = pB.f j j rfl (f.f i j h x) := by
  let e := (pA.f i i rfl).quotKerEquivOfSurjective (PA.onto i)
  have hx : pA.f i i rfl x = e (Submodule.Quotient.mk x) := rfl
  unfold factorComponent
  change (LinearMap.ker (pA.f i i rfl)).liftQ ((pB.f j j rfl).comp (f.f i j h))
    (factorKernel f pA pB PA PB i j h) (e.symm (pA.f i i rfl x)) = _
  rw [hx, e.symm_apply_apply, Submodule.liftQ_apply]
  rfl

/-- The reduced chain map is constructed by descent from the specified actual integral map. -/
def factorHom : GHom AF BF where
  f := factorComponent f pA pB PA PB
  comm i j i' j' h hi hj h' x := by
    subst hi
    subst h'
    subst h
    obtain ⟨y, rfl⟩ := PA.onto i x
    change factorComponent f pA pB PA PB (i + 1) (i + 1) rfl
        (AF.d i (i + 1) hj (pA.f i i rfl y)) =
      BF.d i (i + 1) hj (factorComponent f pA pB PA PB i i rfl (pA.f i i rfl y))
    rw [← pA.comm i (i + 1) i (i + 1) rfl rfl hj rfl y,
      factorComponent_projection, factorComponent_projection]
    rw [f.comm i (i + 1) i (i + 1) rfl rfl rfl rfl y,
      pB.comm i (i + 1) i (i + 1) rfl rfl hj rfl (f.f i i rfl y)]

/-- Its fixed actual projection square holds in every degree and on every cochain. -/
theorem factorHom_square (i j : ℤ) (h : i = j) (x : A.X i) :
    pB.f j j rfl (f.f i j h x) = (factorHom f pA pB PA PB).f i j h (pA.f i i rfl x) :=
  (factorComponent_projection f pA pB PA PB i j h x).symm

/-- This particular descended reduced map is a quasi-isomorphism whenever the actual integral source realization is. -/
theorem factorHom_quasiIso (hf : QuasiIso (GHom.toCC f)) :
    QuasiIso (GHom.toCC (factorHom f pA pB PA PB)) :=
  quasiIso_of_exact_reduction_square f (factorHom f pA pB PA PB) pA pB
    (factorHom_square f pA pB PA PB) PA PB hf

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.QuasiIsoReduction

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTraceCompatibility

open CategoryTheory TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.CoordinateReduction

variable (F : Type) [Field F] [DecidableEq F] [CharZero F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The actual finite cyclotomic Tate coefficients are finite roots-of-unity modules. -/
theorem finite_cyclotomic_levels (a : ℕ) :
    Finite (TateModuleLevel 2 (UnitsCoeff F) a) := by
  exact Finite.of_equiv (KummerCoeff F (2 ^ a)) (actualMuLevelEquiv F a).symm.toEquiv

/-- The actual integral cyclotomic Tate coefficient space is compact. -/
theorem cyclotomic_coefficients_compact :
    CompactSpace (IntegralTateCoeff (AbsoluteGaloisGroup F) (UnitsCoeff F)) := by
  haveI (a : ℕ) : Finite (TateModuleLevel 2 (UnitsCoeff F) a) := finite_cyclotomic_levels F a
  exact inferInstanceAs (CompactSpace (TateModule 2 (UnitsCoeff F)))

/-- The fixed class of the actual reduced two-cochain, when it is a finite cocycle. -/
def firstTraceClass (z : (actualTraceComplex F).X 2)
    (hz : ((finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).d 2 3).hom
      (((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).f 2).hom z) = 0) :
    H2 (AbsoluteGaloisGroup F) (KummerCoeff F 2) :=
  actualMuH2Equiv F 1 (kerToH2
    (⟨((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).f 2).hom z, hz⟩ :
      LinearMap.ker ((finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).d 2 3).hom))

/-- The actual all-cochain trace is canonically normalized modulo two on every cochain that is a cocycle after its fixed finite reduction. -/
theorem trv_normalized_on_finite_cycles
    (hthird : FiniteCycleLift.ThirdDegreeExact F) (z : (actualTraceComplex F).X 2)
    (hz : ((finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).d 2 3).hom
      (((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).f 2).hom z) = 0) :
    PadicInt.toZModPow 1 (AllCochainTrace.trv F z) =
      finiteInvariant F 2 (twoPower_isUnit F 1) (firstTraceClass F z hz) := by
  haveI := cyclotomic_coefficients_compact F
  have hproj : ((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).f 3).hom
      (((actualTraceComplex F).d 2 3).hom z) = 0 := by
    rw [reduceCochains_d]
    exact hz
  obtain ⟨t, ht⟩ := (first_cochain_kernel (AbsoluteGaloisGroup F) (UnitsCoeff F) 3 _).mp hproj
  have hdt : ((actualTraceComplex F).d 2 3).hom z = (2 : ℤ_[2]) ^ 1 • t := by
    rw [pow_one]
    exact ht.symm
  obtain ⟨w, y, hw⟩ := FiniteCycleLift.cycleLift_of_third_exact F hthird 1 z t hdt
  have h2 : ((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).f 2).hom
      ((2 : ℤ_[2]) ^ 1 • y) = 0 :=
    (first_cochain_kernel (AbsoluteGaloisGroup F) (UnitsCoeff F) 2 _).mpr ⟨y, by rw [pow_one]⟩
  have hzw : ((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).f 2).hom z =
      ((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).f 2).hom w.val := by
    rw [hw, map_add, h2, add_zero]
  have hcycles : reduceTwoCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) 1 w =
      (⟨((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).f 2).hom z, hz⟩ :
        LinearMap.ker ((finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).d 2 3).hom) :=
    Subtype.ext hzw.symm
  have hclass : actualMuH2Reduction F 1 w = firstTraceClass F z hz := by
    change actualMuH2Equiv F 1 (kerToH2 (reduceTwoCycle (AbsoluteGaloisGroup F) (UnitsCoeff F) 1 w)) = _
    rw [hcycles]
    rfl
  have hnormal := FiniteCycleLift.cycleLift_trace_normalization F 1 z w y hw
  rw [hclass] at hnormal
  exact hnormal

/-- In particular the finite-only cycle normalization follows from the explicitly scoped higher-degree Milne input, not from a compatibility premise. -/
theorem trv_normalized_on_finite_cycles_of_print
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint) (z : (actualTraceComplex F).X 2)
    (hz : ((finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).d 2 3).hom
      (((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).f 2).hom z) = 0) :
    PadicInt.toZModPow 1 (AllCochainTrace.trv F z) =
      finiteInvariant F 2 (twoPower_isUnit F 1) (firstTraceClass F z hz) :=
  trv_normalized_on_finite_cycles F (FiniteLocalDegreeBound.actualThirdDegreeExact_of_print hH F) z hz

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTraceCompatibility

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteCupCompatibility

open CategoryTheory TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.CoordinateReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTraceCompatibility

variable (F : Type) [Field F] [DecidableEq F] [CharZero F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (B : WeierstrassCurve F) [B.IsElliptic]

/-- The actual separable-closure point Tate coefficients are compact, via the canonical closure coefficient dictionary. -/
theorem point_coefficients_compact : CompactSpace (IntegralTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff) := by
  haveI (a : ℕ) : Finite (TateModuleLevel 2 B.PointCoeff a) := by
    haveI : Finite (TateModuleLevel 2 (PtAlg F B) a) := FiniteLocalDegreeBound.finite_elliptic_levels F B a
    let f : TateModuleLevel 2 B.PointCoeff a → TateModuleLevel 2 (PtAlg F B) a :=
      TateModule.levelMap (pointCoeffToAlg F B).toAddMonoidHom a
    apply Finite.of_injective f
    intro x y h
    apply Subtype.ext
    exact (pointCoeffToAlg F B).injective (congrArg Subtype.val h)
  exact inferInstanceAs (CompactSpace (TateModule 2 B.PointCoeff))

/-- The finite cycle of a specified integral point one-cochain under the fixed first projection. -/
def firstPointCycle (c : (pointComplex F B).X 1)
    (hc : ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 1).hom c) = 0) :
    LinearMap.ker ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 1 2).hom :=
  ⟨((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 1).hom c, hc⟩

/-- The specific finite point cocycle read from those prescribed cochain reductions. -/
def firstPointZ1 (c : (pointComplex F B).X 1)
    (hc : ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 1).hom c) = 0) :
    Z1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2) :=
  cocyclesMap1 (AbsoluteGaloisGroup F) (FiniteTateCoeff (AbsoluteGaloisGroup F) B.PointCoeff 1)
    (AbsoluteGaloisGroup F) (B.TorsionCoeff 2) (ContinuousMonoidHom.id _)
    (IntegralPairing.pointLevelEquiv F B 1).toAddMonoidHom continuous_of_discreteTopology
    (pointLevelEquiv_smul F B 1)
    ⟨fun σ => cfun (firstPointCycle F B c hc).val (fun _ => σ),
      mem_Z1_of_d_eq_zero _ (firstPointCycle F B c hc).property⟩

/-- The fixed actual first finite class of an integral cochain that is only a cycle after reduction. -/
def firstPointClass (c : (pointComplex F B).X 1)
    (hc : ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 1).hom c) = 0) :
    H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff 2) := H1pi _ _ (firstPointZ1 F B c hc)

/-- The actual cup of two finite-only cycles is itself a cycle under the prescribed finite projection. -/
theorem cup_first_cycle
    (c d : (pointComplex F B).X 1)
    (hc : ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 1).hom c) = 0)
    (hd : ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 1).hom d) = 0) :
    ((finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).d 2 3).hom
      (((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).f 2).hom (integralCupOne F B c d)) = 0 := by
  haveI := point_coefficients_compact F B
  haveI := cyclotomic_coefficients_compact F
  have hdc : ((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 2).hom
      (((pointComplex F B).d 1 2).hom c) = 0 := by rw [reduceCochains_d]; exact hc
  have hdd : ((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 2).hom
      (((pointComplex F B).d 1 2).hom d) = 0 := by rw [reduceCochains_d]; exact hd
  obtain ⟨u, hu⟩ := (first_cochain_kernel (AbsoluteGaloisGroup F) B.PointCoeff 2 _).mp hdc
  obtain ⟨v, hv⟩ := (first_cochain_kernel (AbsoluteGaloisGroup F) B.PointCoeff 2 _).mp hdd
  have h := (integralCupPair F B).leib 1 1 2 rfl c d
  rw [← hu, ← hv, map_smul, LinearMap.smul_apply, map_smul] at h
  simp only [pow_one, neg_one_smul] at h
  rw [← sub_eq_add_neg, ← smul_sub] at h
  rw [← reduceCochains_d]
  apply (first_cochain_kernel (AbsoluteGaloisGroup F) (UnitsCoeff F) 3 _).mpr
  exact ⟨_, h.symm⟩

/-- The specific finite class of the reduced integral cup is the genuine finite Weil cup of the specific point reductions. -/
theorem cup_first_class
    (c d : (pointComplex F B).X 1)
    (hc : ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 1).hom c) = 0)
    (hd : ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 1).hom d) = 0) :
    firstTraceClass F (integralCupOne F B c d) (cup_first_cycle F B c d hc hd) =
      ZInQ.Contrib.CloudB3RC53.Duality.localWeilCup B 2 (twoPower_isUnit F 1)
        (firstPointClass F B c hc) (firstPointClass F B d hd) := by
  change actualMuH2Equiv F 1 (kerToH2
      (⟨((reduceCochains (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).f 2).hom (integralCupOne F B c d),
        cup_first_cycle F B c d hc hd⟩ :
          LinearMap.ker ((finiteIntegralComplex (AbsoluteGaloisGroup F) (UnitsCoeff F) 1).d 2 3).hom)) = _
  erw [actualMuH2Equiv, kerToH2_apply, explicitCoeff2Equiv_apply, explicitCoeff2_mk]
  change H2pi (AbsoluteGaloisGroup F) (KummerCoeff F 2) _ =
    ZInQ.Contrib.CloudB3RC53.Duality.cupH (B.torsionCoeffWeilPairing 2 (twoPower_isUnit F 1))
      (fun σ x y => B.torsionCoeffWeilPairing_smul 2 (twoPower_isUnit F 1) σ x y)
      (H1pi _ _ (firstPointZ1 F B c hc)) (H1pi _ _ (firstPointZ1 F B d hd))
  rw [ZInQ.Contrib.CloudB3RC53.Duality.cupH_mk]
  apply congrArg (H2pi (AbsoluteGaloisGroup F) (KummerCoeff F 2))
  apply Subtype.ext
  funext p
  obtain ⟨σ, τ⟩ := p
  have hcup : cfun (integralCupOne F B c d) ![σ, τ] =
      coefficientWeilPairing F B (cfun c (fun _ => σ)) (σ • cfun d (fun _ => τ)) := by
    change ZInQ.Manuscript.RC.SelmerComplex.cupFun (coefficientWeilPairing F B) 1 1 2 rfl
      (cfun c) (cfun d) ![σ, τ] = _
    exact cupFun_one_one_apply (coefficientWeilPairing F B) (cfun c) (cfun d) ![σ, τ]
  change actualMuLevelEquiv F 1
      (coefficientProjection (AbsoluteGaloisGroup F) (UnitsCoeff F) 1 (cfun (integralCupOne F B c d) ![σ, τ])) =
    B.torsionCoeffWeilPairing 2 (twoPower_isUnit F 1)
      (IntegralPairing.pointLevelEquiv F B 1 (coefficientProjection (AbsoluteGaloisGroup F) B.PointCoeff 1
        (cfun c (fun _ => σ))))
      (σ • IntegralPairing.pointLevelEquiv F B 1 (coefficientProjection (AbsoluteGaloisGroup F) B.PointCoeff 1
        (cfun d (fun _ => τ))))
  rw [hcup, coefficientWeilPairing_projection, coefficientProjection_smul, pointLevelEquiv_smul]
  rfl

/-- Cup-invariant compatibility for all actual cochains that are cycles only after their fixed finite reductions. -/
theorem cup_invariant_compatibility_finite_cycles
    (hthird : FiniteCycleLift.ThirdDegreeExact F)
    (c d : (pointComplex F B).X 1)
    (hc : ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 1).hom c) = 0)
    (hd : ((finiteIntegralComplex (AbsoluteGaloisGroup F) B.PointCoeff 1).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup F) B.PointCoeff 1).f 1).hom d) = 0) :
    padicInvariant 1 (AllCochainTrace.trv F (integralCupOne F B c d)) =
      ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 (twoPower_isUnit F 1)
        (firstPointClass F B c hc) (firstPointClass F B d hd) := by
  have h := trv_normalized_on_finite_cycles F hthird (integralCupOne F B c d) (cup_first_cycle F B c d hc hd)
  rw [cup_first_class] at h
  have hi := congrArg (ZMod.toRatAddCircle 2) h
  rw [finiteInvariant_toRat] at hi
  exact hi

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteCupCompatibility

end


noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ModTwoComplexes

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.CoordinateReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.QuasiIsoReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore

/-- The specified finite coordinate module, with its actual two-adic action through reduction. -/
def finiteVector (r : ℕ) : ModuleCat ℤ_[2] :=
  (ModuleCat.restrictScalars (PadicInt.toZMod (p := 2))).obj (ModuleCat.of (ZMod 2) (Fin r → ZMod 2))

/-- The prescribed coordinate reduction, with no chosen abstract vector-space isomorphism. -/
def vectorProjection (r : ℕ) : (Fin r → ℤ_[2]) →ₗ[ℤ_[2]] finiteVector r where
  toFun x i := PadicInt.toZMod (x i)
  map_add' x y := funext (fun i => map_add PadicInt.toZMod _ _)
  map_smul' r x := by
    funext i
    change PadicInt.toZMod (r * x i) = PadicInt.toZMod r * PadicInt.toZMod (x i)
    exact map_mul PadicInt.toZMod _ _

/-- The specified finite coordinate projection is onto. -/
theorem vectorProjection_surjective (r : ℕ) : Function.Surjective (vectorProjection r) := by
  classical
  choose sec hsec using (padic_ring_reduction).onto
  intro y
  exact ⟨fun i => sec (y i), funext (fun i => hsec (y i))⟩

/-- The kernel of the specified coordinate projection is its actual multiplication-by-two image. -/
theorem vectorProjection_kernel (r : ℕ) (x : Fin r → ℤ_[2]) :
    vectorProjection r x = 0 ↔ ∃ y : Fin r → ℤ_[2], (2 : ℤ_[2]) • y = x := by
  classical
  constructor
  · intro hx
    have hvals : ∀ i, ∃ y : ℤ_[2], (2 : ℤ_[2]) * y = x i := by
      intro i
      apply (padic_ring_reduction.kernel (x i)).mp
      exact congrFun hx i
    choose vals hvals using hvals
    exact ⟨vals, funext (fun i => hvals i)⟩
  · rintro ⟨y, hy⟩
    funext i
    exact (padic_ring_reduction.kernel (x i)).mpr ⟨y i, congrFun hy i⟩

/-- Actual multiplication by two on the coordinate source is regular. -/
theorem vector_regular (r : ℕ) (x : Fin r → ℤ_[2]) (hx : (2 : ℤ_[2]) • x = 0) : x = 0 :=
  funext (fun i => padic_ring_reduction.regular (x i) (congrFun hx i))

/-- The actual coefficient-reduced finite presentation of the local point condition. -/
def finiteCondition {r1 r0 : ℕ} (f : (Fin r1 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin r0 → ℤ_[2])) : GCx ℤ_[2] :=
  restrictCx (PadicInt.toZMod (p := 2))
    (presentationCx r1 r0 (Matrix.toLin' ((LinearMap.toMatrix' f).map PadicInt.toZMod)))

/-- The finite relation matrix is precisely the reduction of the actual relation map in its prescribed bases. -/
theorem finiteRelation_projection {r1 r0 : ℕ}
    (f : (Fin r1 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin r0 → ℤ_[2])) (x : Fin r1 → ℤ_[2]) :
    (finiteCondition f).d 0 1 rfl (vectorProjection r1 x) = vectorProjection r0 (f x) := by
  change Matrix.toLin' ((LinearMap.toMatrix' f).map PadicInt.toZMod)
    (fun i => PadicInt.toZMod (x i)) = fun j => PadicInt.toZMod (f x j)
  rw [Matrix.toLin'_apply]
  have hf : LinearMap.toMatrix' f *ᵥ x = f x := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rw [← hf]
  funext j
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

/-- The actual finite-condition projection is formed from its specified coordinate maps. -/
def conditionProjection {r1 r0 : ℕ}
    (f : (Fin r1 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin r0 → ℤ_[2])) :
    GHom (presentationCx r1 r0 f) (finiteCondition f) :=
  presentationMap
    { zero := vectorProjection r1
      one := vectorProjection r0
      differential := finiteRelation_projection f
      cycle := fun _ => rfl }

/-- Both coordinate degrees and all zero degrees of the actual condition projection satisfy exact reduction by two. -/
def conditionProjection_exact {r1 r0 : ℕ}
    (f : (Fin r1 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin r0 → ℤ_[2])) :
    ExactTwoReduction (conditionProjection f) where
  onto n z := by
    by_cases h0 : n = 0
    · subst n
      exact vectorProjection_surjective r1 z
    · by_cases h1 : n = 1
      · subst n
        exact vectorProjection_surjective r0 z
      · haveI : Subsingleton ((finiteCondition f).X n) := by
          change Subsingleton ((presentationCx r1 r0 (Matrix.toLin' ((LinearMap.toMatrix' f).map PadicInt.toZMod))).X n)
          exact presentationCx_vanishes _ _ _ n (by omega)
        exact ⟨0, Subsingleton.elim _ _⟩
  kernel n x := by
    by_cases h0 : n = 0
    · subst n
      exact vectorProjection_kernel r1 x
    · by_cases h1 : n = 1
      · subst n
        exact vectorProjection_kernel r0 x
      · haveI : Subsingleton ((presentationCx r1 r0 f).X n) := presentationCx_vanishes _ _ _ n (by omega)
        haveI : Subsingleton ((finiteCondition f).X n) := by
          change Subsingleton ((presentationCx r1 r0 (Matrix.toLin' ((LinearMap.toMatrix' f).map PadicInt.toZMod))).X n)
          exact presentationCx_vanishes _ _ _ n (by omega)
        exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  regular n x hx := by
    by_cases h0 : n = 0
    · subst n
      exact vector_regular r1 x hx
    · by_cases h1 : n = 1
      · subst n
        exact vector_regular r0 x hx
      · haveI : Subsingleton ((presentationCx r1 r0 f).X n) := presentationCx_vanishes _ _ _ n (by omega)
        exact Subsingleton.elim _ _

/-- The prescribed coefficient reduction of every degree of a finite based source is exact by two. -/
def basedProjection_exact {κe κo : Type} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]
    (C : BasedCx ℤ_[2] κe κo) : ExactTwoReduction (projectionHom PadicInt.toZMod C) where
  onto := projection_surjective PadicInt.toZMod C padic_ring_reduction
  kernel := projection_kernel PadicInt.toZMod C padic_ring_reduction
  regular := projection_source_regular PadicInt.toZMod C padic_ring_reduction

section Cochains

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Type) [AddCommGroup A] [DistribMulAction G A]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A]
  [CompactSpace (IntegralTateCoeff G A)]

/-- The actual coefficient projection in all relation-indexed cochain degrees. -/
def cochainProjection : GHom (natCx (integralComplex G A)) (natCx (finiteIntegralComplex G A 1)) :=
  natHom (reduceCochains G A 1)

/-- Its actual coefficient exactness and regularity give exact reduction in every cochain degree. -/
def cochainProjection_exact (hcoeff : Function.Surjective (coefficientProjection G A 1)) :
    ExactTwoReduction (cochainProjection G A) where
  onto n z := by
    rcases n with n | n
    · exact first_cochain_surjective G A n hcoeff z
    · haveI : Subsingleton ((natCx (finiteIntegralComplex G A 1)).X (Int.negSucc n)) := by
        change Subsingleton PUnit
        infer_instance
      exact ⟨0, Subsingleton.elim _ _⟩
  kernel n x := by
    rcases n with n | n
    · exact first_cochain_kernel G A n x
    · haveI : Subsingleton ((natCx (integralComplex G A)).X (Int.negSucc n)) := by
        change Subsingleton PUnit
        infer_instance
      haveI : Subsingleton ((natCx (finiteIntegralComplex G A 1)).X (Int.negSucc n)) := by
        change Subsingleton PUnit
        infer_instance
      exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  regular n x hx := by
    rcases n with n | n
    · exact cochain_two_regular G A n x hx
    · haveI : Subsingleton ((natCx (integralComplex G A)).X (Int.negSucc n)) := by
        change Subsingleton PUnit
        infer_instance
      exact Subsingleton.elim _ _

end Cochains

section OrdinaryCone

variable {R : Type} [CommRing R] {U L UF LF : GCx R}
  (ι : GHom U L) (ιF : GHom UF LF) (pU : GHom U UF) (pL : GHom L LF)
  (square : ∀ i j h (u : U.X i), pL.f j j rfl (ι.f i j h u) = ιF.f i j h (pU.f i i rfl u))

/-- The fixed actual condition/Galois projection square gives the ordinary quotient-cone projection. -/
def ordinaryProjection : GHom (ordinaryCone ι) (ordinaryCone ιF) where
  f i j h := (pL.f i j h).prodMap (pU.f (i + 1) (j + 1) (by omega))
  comm i j i' j' h hi hj h' x := by
    subst hi
    subst h'
    subst h
    obtain ⟨l, u⟩ := x
    apply Prod.ext
    · change pL.f (i + 1) (i + 1) rfl (L.d i (i + 1) rfl l + ι.f (i + 1) (i + 1) rfl u) =
        LF.d i (i + 1) hj (pL.f i i rfl l) + ιF.f (i + 1) (i + 1) rfl (pU.f (i + 1) (i + 1) rfl u)
      rw [map_add, pL.comm i (i + 1) i (i + 1) rfl rfl hj rfl l, square]
    · change pU.f (i + 1 + 1) (i + 1 + 1) rfl (-(U.d (i + 1) (i + 1 + 1) rfl u)) =
        -(UF.d (i + 1) (i + 1 + 1) rfl (pU.f (i + 1) (i + 1) rfl u))
      rw [map_neg, pU.comm (i + 1) (i + 1 + 1) (i + 1) (i + 1 + 1) rfl rfl rfl rfl u]

/-- Genuine degreewise exactness and regularity of the prescribed projections descend to the ordinary cone. -/
def ordinaryProjection_exact (PU : ExactTwoReduction pU) (PL : ExactTwoReduction pL) :
    ExactTwoReduction (ordinaryProjection ι ιF pU pL square) where
  onto n z := by
    obtain ⟨l, hl⟩ := PL.onto n z.1
    obtain ⟨u, hu⟩ := PU.onto (n + 1) z.2
    exact ⟨(l, u), Prod.ext hl hu⟩
  kernel n x := by
    constructor
    · intro hx
      obtain ⟨l, hl⟩ := (PL.kernel n x.1).mp (congrArg Prod.fst hx)
      obtain ⟨u, hu⟩ := (PU.kernel (n + 1) x.2).mp (congrArg Prod.snd hx)
      exact ⟨(l, u), Prod.ext hl hu⟩
    · rintro ⟨⟨l, u⟩, hx⟩
      apply Prod.ext
      · exact (PL.kernel n _).mpr ⟨l, congrArg Prod.fst hx⟩
      · exact (PU.kernel (n + 1) _).mpr ⟨u, congrArg Prod.snd hx⟩
  regular n x hx :=
    Prod.ext (PL.regular n x.1 (congrArg Prod.fst hx))
      (PU.regular (n + 1) x.2 (congrArg Prod.snd hx))

end OrdinaryCone

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ModTwoComplexes

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualModTwoResolution

open CategoryTheory NumberField IsDedekindDomain TauCeti
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSelfDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTransport
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.QuasiIsoReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ModTwoComplexes
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- The genuine first point-coefficient projection is onto, through the fixed closure dictionary and actual geometric Tate projection. -/
theorem first_point_coefficients_surjective :
    Function.Surjective (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1) := by
  intro t
  let ta : FiniteTateCoeff (Field.absoluteGaloisGroup (w.adicCompletion K)) (PtAlg (w.adicCompletion K) B) 1 :=
    TateModule.levelMap (pointCoeffToAlg (w.adicCompletion K) B).toAddMonoidHom 1 t
  obtain ⟨v, hv⟩ := actualCoefficientProjection_surjective (w.adicCompletion K) B 1 ta
  refine ⟨toSepCoefficients (w.adicCompletion K) B v, ?_⟩
  apply Subtype.ext
  change (pointCoeffToAlg (w.adicCompletion K) B).symm (TateModule.proj 1 v).val = t.val
  have hval : (TateModule.proj 1 v).val = pointCoeffToAlg (w.adicCompletion K) B t.val :=
    congrArg Subtype.val hv
  exact (congrArg (pointCoeffToAlg (w.adicCompletion K) B).symm hval).trans
    ((pointCoeffToAlg (w.adicCompletion K) B).symm_apply_apply t.val)

/-- The actual local condition reduced in its prescribed finite free bases. -/
def finitePointCondition : GCx ℤ_[2] := finiteCondition (actualLocalPresentation K w B).f

/-- The actual finite Tate coefficient Galois cochains at the first level. -/
abbrev finitePointCochains := natCx (finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)

/-- The fixed actual finite coordinate projection of the completed local condition. -/
def pointConditionProjection : GHom (localCondition K w B) (finitePointCondition K w B) :=
  conditionProjection (actualLocalPresentation K w B).f

/-- The fixed coefficient/cochain projection of the genuine integral local Galois complex. -/
def pointCochainProjection : GHom (localCochains K w B) (finitePointCochains K w B) :=
  cochainProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff

/-- The coordinate projection of the actual local condition has its actual multiplication-by-two kernel. -/
def pointConditionProjection_exact : ExactTwoReduction (pointConditionProjection K w B) :=
  conditionProjection_exact (actualLocalPresentation K w B).f

/-- The genuine local cochain projection is onto with regular multiplication by two and its exact kernel. -/
def pointCochainProjection_exact : ExactTwoReduction (pointCochainProjection K w B) := by
  haveI := FiniteCupCompatibility.point_coefficients_compact (w.adicCompletion K) B
  exact cochainProjection_exact (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff
    (first_point_coefficients_surjective K w B)

/-- The actual reduced Kummer condition map is descended from the specified integral map and its actual projections. -/
def finiteConditionMap : GHom (finitePointCondition K w B) (finitePointCochains K w B) :=
  factorHom (localConditionMap K w B) (pointConditionProjection K w B) (pointCochainProjection K w B)
    (pointConditionProjection_exact K w B) (pointCochainProjection_exact K w B)

/-- The reduced-condition square is proved on each specified genuine cochain component. -/
theorem finiteConditionMap_square (i j : ℤ) (h : i = j) (u : (localCondition K w B).X i) :
    (pointCochainProjection K w B).f j j rfl ((localConditionMap K w B).f i j h u) =
      (finiteConditionMap K w B).f i j h ((pointConditionProjection K w B).f i i rfl u) :=
  factorHom_square _ _ _ _ _ i j h u

/-- The genuine finite quotient cone uses the reduced actual Kummer presentation map. -/
def finiteQuotientCone : GCx ℤ_[2] := SelfDualCore.ordinaryCone (finiteConditionMap K w B)

/-- The actual integral quotient cone projects through the fixed finite condition/Galois coefficient square. -/
def quotientProjection : GHom (localQuotientCone K w B) (finiteQuotientCone K w B) :=
  ordinaryProjection (localConditionMap K w B) (finiteConditionMap K w B)
    (pointConditionProjection K w B) (pointCochainProjection K w B) (finiteConditionMap_square K w B)

/-- That particular quotient-cone projection is onto and has exactly the genuine scalar-two kernel in every degree. -/
def quotientProjection_exact : ExactTwoReduction (quotientProjection K w B) :=
  ordinaryProjection_exact _ _ _ _ _ (pointConditionProjection_exact K w B) (pointCochainProjection_exact K w B)

variable {c1 c2 : ℕ} (I : ActualBasedComparison.TwoTermConeBasedResolution K w B c1 c2)

/-- The prescribed reduction of the actual finite source realization is constructed by descent, not supplied as a comparison-isomorphism premise. -/
def reducedRealization :
    GHom (restrictCx PadicInt.toZMod ((twoTermBased I.differential).map PadicInt.toZMod).toGCx)
      (finiteQuotientCone K w B) :=
  factorHom I.realization (projectionHom PadicInt.toZMod (twoTermBased I.differential))
    (quotientProjection K w B) (basedProjection_exact (twoTermBased I.differential))
    (quotientProjection_exact K w B)

/-- The exact finite source/Galois quotient projection square holds on all the specified actual source cochains. -/
theorem reducedRealization_square (i j : ℤ) (h : i = j) (x : (twoTermBased I.differential).toGCx.X i) :
    (quotientProjection K w B).f j j rfl (I.realization.f i j h x) =
      (reducedRealization K w B I).f i j h
        ((projectionHom PadicInt.toZMod (twoTermBased I.differential)).f i i rfl x) :=
  factorHom_square _ _ _ _ _ i j h x

/-- This actual reduced source realization is a quasi-isomorphism of the genuine finite quotient cone, by exact coefficient reduction. -/
theorem reducedRealization_quasiIso : QuasiIso (GHom.toCC (reducedRealization K w B I)) :=
  factorHom_quasiIso _ _ _ _ _ I.quasiIso

/-- The canonical integral source resolution yields its actual finite quasi-isomorphism from the explicitly cited finite arithmetic inputs. -/
def reducedRealization_of_print
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint) :=
  reducedRealization K w B (FiniteLocalDegreeBound.basedResolution_of_print hM hF hH K w B)

/-- The finite source realization from the genuine arithmetic construction has its proved quasi-isomorphism. -/
theorem reducedRealization_of_print_quasiIso
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint) :
    QuasiIso (GHom.toCC (reducedRealization_of_print K w B hM hF hH)) :=
  reducedRealization_quasiIso K w B _

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualModTwoResolution

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteConditionH0

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSelfDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualModTwoResolution
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.RetainedTorsionNaturality

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

abbrev cyclesZero := LinearMap.ker ((finitePointCondition K w B).d 0 1 rfl)

/-- The specific finite Kummer map sends actual degree-zero condition cycles to actual coefficient cycles. -/
def cycleMapZero : cyclesZero K w B →ₗ[ℤ_[2]]
    LinearMap.ker ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 0 1).hom where
  toFun v := ⟨(finiteConditionMap K w B).f 0 0 rfl v.val, by
    have hv : (finitePointCondition K w B).d 0 1 rfl v.val = 0 := v.property
    have h := (finiteConditionMap K w B).comm 0 1 0 1 rfl rfl rfl rfl v.val
    change ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 0 1).hom
      ((finiteConditionMap K w B).f 0 0 rfl v.val) = 0
    rw [hv, map_zero] at h
    exact h.symm⟩
  map_add' v u := Subtype.ext (map_add _ _ _)
  map_smul' r v := Subtype.ext (map_smul _ _ _)

/-- The actual degree-zero reduced-condition map, with the canonical finite coefficient dictionary. -/
def classMapZero : cyclesZero K w B →+ H0 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) :=
  ((IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1).toAddMonoidHom.comp
      ((H0 (AbsoluteGaloisGroup (w.adicCompletion K))
        (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)).subtype.comp
          (kerToH0.comp (cycleMapZero K w B).toAddMonoidHom))).codRestrict _ (fun v => by
    apply (FixedPoints.mem_addSubgroup _ _ _).mpr
    intro σ
    have h := (FixedPoints.mem_addSubgroup _ _ _).mp (kerToH0 (cycleMapZero K w B v)).property σ
    change σ • IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1
        (kerToH0 (cycleMapZero K w B v)).val =
      IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1 (kerToH0 (cycleMapZero K w B v)).val
    rw [← pointLevelEquiv_smul]
    exact congrArg (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1) h)

/-- Every prescribed finite degree-zero cycle lifts to an actual integral relation divisible by two. -/
theorem lift_zero_cycle (v : cyclesZero K w B) :
    ∃ (x : Fin (actualLocalPresentation K w B).rankOne → ℤ_[2])
      (y : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]),
      (actualLocalPresentation K w B).f x = (2 : ℤ_[2]) • y ∧
      (pointConditionProjection K w B).f 0 0 rfl x = v.val := by
  obtain ⟨x, hx⟩ := (pointConditionProjection_exact K w B).onto 0 v.val
  have hv : (finitePointCondition K w B).d 0 1 rfl v.val = 0 := v.property
  have h := (pointConditionProjection K w B).comm 0 1 0 1 rfl rfl rfl rfl x
  rw [hx, hv] at h
  obtain ⟨y, hy⟩ := ((pointConditionProjection_exact K w B).kernel 1 _).mp h
  exact ⟨x, y, hy.symm, hx⟩

/-- On an actual integral relation, this map is the previously proved retained-torsion coefficient square. -/
theorem classMapZero_relation
    (v : cyclesZero K w B)
    (x : Fin (actualLocalPresentation K w B).rankOne → ℤ_[2])
    (y : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2])
    (hxy : (actualLocalPresentation K w B).f x = (2 : ℤ_[2]) • y)
    (hx : (pointConditionProjection K w B).f 0 0 rfl x = v.val) :
    (classMapZero K w B v).val = B.baseTorsionCoeff 2
      (etaZero K w B (relationTorsion K w B x y hxy)) := by
  change IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1
    (cfun ((finiteConditionMap K w B).f 0 0 rfl v.val) Fin.elim0) = _
  erw [← hx, ← finiteConditionMap_square]
  exact degreeZeroReductionNaturality_proof K w B x y hxy

/-- The actual retained-degree-zero map is injective, by the integral presentation and actual completion torsion dictionary. -/
theorem classMapZero_kernel (v : cyclesZero K w B) (hv : classMapZero K w B v = 0) : v = 0 := by
  obtain ⟨x, y, hxy, hx⟩ := lift_zero_cycle K w B v
  have hval := congrArg Subtype.val hv
  rw [classMapZero_relation K w B v x y hxy hx] at hval
  have ht : etaZero K w B (relationTorsion K w B x y hxy) = 0 := by
    apply B.baseTorsionCoeff_injective 2
    rw [map_zero]
    exact hval
  have hrel : relationTorsion K w B x y hxy = 0 := (etaZero K w B).map_eq_zero_iff.mp ht
  have hgy : (actualLocalPresentation K w B).g y = 0 := congrArg Subtype.val hrel
  obtain ⟨z, hz⟩ := (actualLocalPresentation K w B).exact y hgy
  have hxz : x = (2 : ℤ_[2]) • z := by
    apply (actualLocalPresentation K w B).injective
    rw [map_smul, hz]
    exact hxy
  have hpx : (pointConditionProjection K w B).f 0 0 rfl x = 0 :=
    ((pointConditionProjection_exact K w B).kernel 0 x).mpr ⟨z, hxz.symm⟩
  apply Subtype.ext
  exact hx.symm.trans hpx

/-- Injectivity is for the specific reduced coefficient map, not for a selected abstract isomorphism. -/
theorem classMapZero_injective : Function.Injective (classMapZero K w B) := by
  intro v u h
  have hz : classMapZero K w B (v - u) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (classMapZero_kernel K w B _ hz)

/-- Every genuine rational torsion coefficient is represented by a degree-zero cycle of this actual reduced presentation. -/
theorem classMapZero_surjective : Function.Surjective (classMapZero K w B) := by
  intro q
  obtain ⟨t, ht⟩ := ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionToH0_bijective B 2 |>.surjective q
  let tc := torsionToCompletion B.toAffine.Point 1 t
  obtain ⟨y, hy⟩ := (actualLocalPresentation K w B).surjective tc.val
  have hgy : (actualLocalPresentation K w B).g ((2 : ℤ_[2]) • y) = 0 := by
    rw [map_smul, hy]
    exact tc.property
  obtain ⟨x, hxy⟩ := (actualLocalPresentation K w B).exact ((2 : ℤ_[2]) • y) hgy
  let xv := (pointConditionProjection K w B).f 0 0 rfl x
  have hxv : (finitePointCondition K w B).d 0 1 rfl xv = 0 := by
    have h := (pointConditionProjection K w B).comm 0 1 0 1 rfl rfl rfl rfl x
    have hz : (pointConditionProjection K w B).f 1 1 rfl ((actualLocalPresentation K w B).f x) = 0 :=
      ((pointConditionProjection_exact K w B).kernel 1 _).mpr ⟨y, hxy.symm⟩
    exact h.symm.trans hz
  let v : cyclesZero K w B := ⟨xv, hxv⟩
  have htc : relationTorsion K w B x y hxy = tc := Subtype.ext hy
  refine ⟨v, ?_⟩
  have hv : (classMapZero K w B v).val = B.baseTorsionCoeff 2 t := by
    rw [classMapZero_relation K w B v x y hxy rfl, htc, etaZero_torsionToCompletion]
  apply Subtype.ext
  have hq := congrArg Subtype.val ht
  exact hv.trans hq

/-- The genuine degree-zero finite Kummer map is the full fixed rational-torsion identification. -/
theorem classMapZero_bijective : Function.Bijective (classMapZero K w B) :=
  ⟨classMapZero_injective K w B, classMapZero_surjective K w B⟩

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteConditionH0

end


noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteConditionH1

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.Duality
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSelfDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualModTwoResolution
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTransport
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- The completed-point finite Kummer class vanishes exactly on the actual two-power multiplication image. -/
theorem completionClass_zero_iff (a : ℕ) (x : PointCompletion B.toAffine.Point) :
    completionKummerClass (w.adicCompletion K) B a x = 0 ↔
      ∃ y : PointCompletion B.toAffine.Point, (2 : ℤ_[2]) ^ a • y = x := by
  let f := (hOneToAlg (w.adicCompletion K) B (2 ^ a)).toAddMonoidHom.comp
    ((B.kummerClassMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).comp
      (completionQuotientEquiv B.toAffine.Point a).toAddMonoidHom)
  have hi : Function.Injective f :=
    (hOneToAlg (w.adicCompletion K) B (2 ^ a)).injective.comp
      ((B.kummerClassMap_injective (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).comp
        (completionQuotientEquiv B.toAffine.Point a).injective)
  have hiff : completionKummerClass (w.adicCompletion K) B a x = 0 ↔
      (Submodule.Quotient.mk x : PointCompletion B.toAffine.Point ⧸ nSub ((2 : ℤ_[2]) ^ a) (PointCompletion B.toAffine.Point)) = 0 := by
    constructor
    · intro hx
      apply hi
      change f (Submodule.Quotient.mk x) = f 0
      rw [map_zero]
      exact hx
    · intro hx
      change f (Submodule.Quotient.mk x) = 0
      rw [hx, map_zero]
  rw [hiff, Submodule.Quotient.mk_eq_zero, mem_nSub]

/-- The actual finite-condition one-cochain is a genuine finite Galois one-cycle. -/
def cycleMapOne : (finitePointCondition K w B).X 1 →ₗ[ℤ_[2]]
    LinearMap.ker ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 1 2).hom where
  toFun v := ⟨(finiteConditionMap K w B).f 1 1 rfl v, by
    have hv : (finitePointCondition K w B).d 1 2 rfl v = 0 := rfl
    have h := (finiteConditionMap K w B).comm 1 2 1 2 rfl rfl rfl rfl v
    change ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 1 2).hom
      ((finiteConditionMap K w B).f 1 1 rfl v) = 0
    rw [hv, map_zero] at h
    exact h.symm⟩
  map_add' v u := Subtype.ext (map_add _ _ _)
  map_smul' r v := Subtype.ext (map_smul _ _ _)

/-- The specific genuine finite Kummer class map of the reduced presentation. -/
def classMapOne : (finitePointCondition K w B).X 1 →+ H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) :=
  (explicitCoeff1Equiv (AbsoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)
    (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (pointLevelEquiv_smul (w.adicCompletion K) B 1)).toAddMonoidHom.comp
      (kerToH1.comp (cycleMapOne K w B).toAddMonoidHom)

/-- Its value on every actual integral source lift is the previously fixed actual class reduction. -/
theorem classMapOne_lift (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    classMapOne K w B ((pointConditionProjection K w B).f 1 1 rfl u) =
      pointH1Reduction (w.adicCompletion K) B 1 (localKummerOne K w B u) := by
  let e := explicitCoeff1Equiv (AbsoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)
    (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (pointLevelEquiv_smul (w.adicCompletion K) B 1)
  change e (kerToH1 (cycleMapOne K w B ((pointConditionProjection K w B).f 1 1 rfl u))) =
    e (kerToH1 (reduceOneCycle (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 (localKummerOne K w B u)))
  apply congrArg e
  apply congrArg kerToH1
  apply Subtype.ext
  exact (finiteConditionMap_square K w B 1 1 rfl u).symm

/-- The actual reduced-condition one-class image is precisely the genuine finite Kummer image. -/
theorem classMapOne_range : (classMapOne K w B).range =
    (B.kummerMap 2 (twoPower_isUnit (w.adicCompletion K) 1)).range := by
  ext z
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨u, hu⟩ := (pointConditionProjection_exact K w B).onto 1 v
    have h := classMapOne_lift K w B u
    rw [hu] at h
    have hz := localKummerOne_mem_genuine_Kummer K w B 1 u
    rw [← h, hv] at hz
    exact hz
  · rintro ⟨p, hp⟩
    obtain ⟨u, hu⟩ := (actualLocalPresentation K w B).surjective (completePoint B.toAffine.Point p)
    refine ⟨(pointConditionProjection K w B).f 1 1 rfl u, ?_⟩
    exact (classMapOne_lift K w B u).trans
      ((SourceIntegralImage.local_reduction_of_complete_point K w B 1 u p hu).trans hp)

/-- The actual finite-condition class kernel is exactly its specified degree-zero relation image. -/
theorem classMapOne_kernel (v : (finitePointCondition K w B).X 1) :
    classMapOne K w B v = 0 ↔ ∃ u : (finitePointCondition K w B).X 0,
      (finitePointCondition K w B).d 0 1 rfl u = v := by
  constructor
  · intro hv
    obtain ⟨u, hu⟩ := ModTwoComplexes.vectorProjection_surjective (actualLocalPresentation K w B).rankZero v
    change (pointConditionProjection K w B).f 1 1 rfl u = v at hu
    have h := classMapOne_lift K w B u
    rw [hu, hv] at h
    have hc : pointH1Reduction (w.adicCompletion K) B 1 (localKummerOne K w B u) = 0 := h.symm
    rw [localKummerOne_reduction] at hc
    change (hOneToAlg (w.adicCompletion K) B 2).symm
      (actualH1Reduction (w.adicCompletion K) B 1 (actualLocalKummerOne K w B u)) = 0 at hc
    rw [actualLocalKummerOne, basedKummerOne_reduction] at hc
    have hm := (hOneToAlg (w.adicCompletion K) B 2).symm.map_eq_zero_iff.mp hc
    obtain ⟨m, hm⟩ := (completionClass_zero_iff K w B 1 ((actualLocalPresentation K w B).g u)).mp hm
    rw [pow_one] at hm
    obtain ⟨t, ht⟩ := (actualLocalPresentation K w B).surjective m
    have hgt : (actualLocalPresentation K w B).g (u - (2 : ℤ_[2]) • t) = 0 := by
      rw [map_sub, map_smul, ht, ← hm, sub_self]
    obtain ⟨x, hx⟩ := (actualLocalPresentation K w B).exact _ hgt
    refine ⟨(pointConditionProjection K w B).f 0 0 rfl x, ?_⟩
    have h2 : (pointConditionProjection K w B).f 1 1 rfl ((2 : ℤ_[2]) • t) = 0 :=
      ((pointConditionProjection_exact K w B).kernel 1 _).mpr ⟨t, rfl⟩
    have hs := (pointConditionProjection K w B).comm 0 1 0 1 rfl rfl rfl rfl x
    change (pointConditionProjection K w B).f 1 1 rfl ((actualLocalPresentation K w B).f x) =
      (finitePointCondition K w B).d 0 1 rfl ((pointConditionProjection K w B).f 0 0 rfl x) at hs
    have hproj : (pointConditionProjection K w B).f 1 1 rfl ((actualLocalPresentation K w B).f x) = v := by
      change ModTwoComplexes.vectorProjection (actualLocalPresentation K w B).rankZero ((actualLocalPresentation K w B).f x) = v
      rw [hx, map_sub]
      have ht0 : ModTwoComplexes.vectorProjection (actualLocalPresentation K w B).rankZero ((2 : ℤ_[2]) • t) = 0 := h2
      rw [ht0, sub_zero]
      exact hu
    exact hs.symm.trans hproj
  · rintro ⟨u, rfl⟩
    let e := explicitCoeff1Equiv (AbsoluteGaloisGroup (w.adicCompletion K))
      (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)
      (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1)
      continuous_of_discreteTopology continuous_of_discreteTopology
      (pointLevelEquiv_smul (w.adicCompletion K) B 1)
    change e (kerToH1 (cycleMapOne K w B ((finitePointCondition K w B).d 0 1 rfl u))) = 0
    apply e.map_eq_zero_iff.mpr
    apply (kerToH1_eq_zero_iff _).mpr
    refine ⟨(finiteConditionMap K w B).f 0 0 rfl u, ?_⟩
    exact ((finiteConditionMap K w B).comm 0 1 0 1 rfl rfl rfl rfl u).symm

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteConditionH1

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ArithmeticTarget

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualModTwoResolution
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualBasedComparison

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- The standard finite relation kernel is the actual degree-zero reduced condition cycle space. -/
def kernelToConditionCycle : LinearMap.ker (pointDifferentialModTwo K w B) →+ FiniteConditionH0.cyclesZero K w B where
  toFun x := ⟨x.val, x.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- This identification preserves the actual coordinate vector and is bijective. -/
theorem kernelToConditionCycle_bijective : Function.Bijective (kernelToConditionCycle K w B) := by
  constructor
  · intro x y h
    exact Subtype.ext (congrArg Subtype.val h)
  · intro x
    exact ⟨⟨x.val, x.property⟩, rfl⟩

/-- The actual finite relation kernel maps to rational two-torsion through the specific reduced Kummer coefficient map. -/
def zeroIdentification : LinearMap.ker (pointDifferentialModTwo K w B) →+ AddSubgroup.torsionBy B.toAffine.Point 2 :=
  ((ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionH0Equiv B 2).symm.toAddMonoidHom.comp
    (FiniteConditionH0.classMapZero K w B)).comp (kernelToConditionCycle K w B)

/-- Its bijectivity follows from the actual coefficient map and the canonical rational-torsion inclusion. -/
theorem zeroIdentification_bijective : Function.Bijective (zeroIdentification K w B) :=
  (ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionH0Equiv B 2).symm.bijective.comp
    ((FiniteConditionH0.classMapZero_bijective K w B).comp (kernelToConditionCycle_bijective K w B))

/-- The same fixed actual identification as a coefficient-field linear equivalence. -/
def zeroLinearEquiv : LinearMap.ker (pointDifferentialModTwo K w B) ≃ₗ[ZMod 2] AddSubgroup.torsionBy B.toAffine.Point 2 :=
  LinearEquiv.ofBijective (zeroIdentification K w B |>.toZModLinearMap 2) (zeroIdentification_bijective K w B)

/-- The actual reduced degree-one Kummer map, read on its prescribed finite coordinate vector. -/
def kappaLinear : (Fin (actualLocalPresentation K w B).rankZero → ZMod 2) →ₗ[ZMod 2]
    H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) := by
  let f : (Fin (actualLocalPresentation K w B).rankZero → ZMod 2) →+
      H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) := FiniteConditionH1.classMapOne K w B
  exact f.toZModLinearMap 2

/-- The fixed rational-point quotient Kummer map, with its canonical coefficient-field action. -/
def deltaLinear : TateDualityData.pointMod (P := B.toAffine.Point) 2 →ₗ[ZMod 2]
    H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) :=
  (B.kummerClassMap 2 (twoPower_isUnit (w.adicCompletion K) 1)).toZModLinearMap 2

/-- The actual reduced relation image is exactly the kernel of the specified Kummer coordinate map. -/
theorem kappaLinear_kernel : LinearMap.ker (kappaLinear K w B) = LinearMap.range (pointDifferentialModTwo K w B) := by
  ext v
  change FiniteConditionH1.classMapOne K w B v = 0 ↔ ∃ u, pointDifferentialModTwo K w B u = v
  erw [FiniteConditionH1.classMapOne_kernel]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩

/-- The two prescribed Kummer maps have the same actual image. -/
theorem kappaLinear_range : LinearMap.range (kappaLinear K w B) = LinearMap.range (deltaLinear K w B) := by
  ext y
  constructor
  · rintro ⟨u, hu⟩
    have hy : y ∈ (B.kummerMap 2 (twoPower_isUnit (w.adicCompletion K) 1)).range := by
      rw [← FiniteConditionH1.classMapOne_range]
      exact ⟨u, hu⟩
    obtain ⟨p, hp⟩ := hy
    refine ⟨QuotientAddGroup.mk p, ?_⟩
    change B.kummerClassMap 2 (twoPower_isUnit (w.adicCompletion K) 1) (QuotientAddGroup.mk p) = y
    rw [B.kummerClassMap_mk]
    exact hp
  · rintro ⟨q, hq⟩
    have hqim : deltaLinear K w B q ∈ (FiniteConditionH1.classMapOne K w B).range := by
      induction q using QuotientAddGroup.induction_on with
      | H p =>
        rw [FiniteConditionH1.classMapOne_range]
        exact ⟨p, rfl⟩
    obtain ⟨u, hu⟩ := hqim
    exact ⟨u, hu.trans hq⟩

/-- The actual point-quotient Kummer map is injective independently of any local duality print. -/
theorem deltaLinear_injective : Function.Injective (deltaLinear K w B) :=
  B.kummerClassMap_injective 2 (twoPower_isUnit (w.adicCompletion K) 1)

/-- The actual point quotient identifies linearly with the specified Kummer coordinate image. -/
def deltaToKappaRange : TateDualityData.pointMod (P := B.toAffine.Point) 2 →ₗ[ZMod 2]
    LinearMap.range (kappaLinear K w B) :=
  (deltaLinear K w B).codRestrict _ (fun x => by
    rw [kappaLinear_range]
    exact ⟨x, rfl⟩)

/-- The range identification is onto and injective by the two actual Kummer maps, not by a freely chosen isomorphism. -/
theorem deltaToKappaRange_bijective : Function.Bijective (deltaToKappaRange K w B) := by
  constructor
  · intro x y h
    exact deltaLinear_injective K w B (congrArg Subtype.val h)
  · intro y
    have hy : y.val ∈ LinearMap.range (deltaLinear K w B) := by
      rw [← kappaLinear_range]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

/-- The canonical degree-one range equivalence is formed from the actual rational-point Kummer map. -/
def deltaRangeEquiv : TateDualityData.pointMod (P := B.toAffine.Point) 2 ≃ₗ[ZMod 2]
    LinearMap.range (kappaLinear K w B) :=
  LinearEquiv.ofBijective (deltaToKappaRange K w B) (deltaToKappaRange_bijective K w B)

/-- The actual reduced-condition cokernel is the actual rational point quotient, using its genuine Kummer image. -/
def oneLinearEquiv :
    ((Fin (actualLocalPresentation K w B).rankZero → ZMod 2) ⧸ LinearMap.range (pointDifferentialModTwo K w B)) ≃ₗ[ZMod 2]
      TateDualityData.pointMod (P := B.toAffine.Point) 2 :=
  ((LinearMap.range (pointDifferentialModTwo K w B)).quotEquivOfEq (LinearMap.ker (kappaLinear K w B))
      (kappaLinear_kernel K w B).symm).trans
    ((kappaLinear K w B).quotKerEquivRange.trans (deltaRangeEquiv K w B).symm)

/-- The actual kernel identification is the retained-torsion point of every specified integral relation lift. -/
theorem zeroLinearEquiv_relation
    (r : LinearMap.ker (pointDifferentialModTwo K w B))
    (x : Fin (actualLocalPresentation K w B).rankOne → ℤ_[2])
    (y : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2])
    (hxy : (actualLocalPresentation K w B).f x = (2 : ℤ_[2]) • y)
    (hx : (pointConditionProjection K w B).f 0 0 rfl x = r.val) :
    zeroLinearEquiv K w B r = etaZero K w B (RetainedTorsionNaturality.relationTorsion K w B x y hxy) := by
  let e := ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionH0Equiv B 2
  apply e.injective
  change e (e.symm (FiniteConditionH0.classMapZero K w B (kernelToConditionCycle K w B r))) = _
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact FiniteConditionH0.classMapZero_relation K w B (kernelToConditionCycle K w B r) x y hxy hx

/-- The actual cokernel identification commutes with the genuine rational-point Kummer map on each prescribed coordinate representative. -/
theorem oneLinearEquiv_kummer
    (u : Fin (actualLocalPresentation K w B).rankZero → ZMod 2) :
    deltaLinear K w B (oneLinearEquiv K w B (Submodule.Quotient.mk u)) = kappaLinear K w B u := by
  let e := (LinearMap.range (pointDifferentialModTwo K w B)).quotEquivOfEq (LinearMap.ker (kappaLinear K w B))
    (kappaLinear_kernel K w B).symm
  have he : e (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := rfl
  have h := (deltaRangeEquiv K w B).apply_symm_apply
    ((kappaLinear K w B).quotKerEquivRange (e (Submodule.Quotient.mk u)))
  have hv := congrArg Subtype.val h
  change deltaLinear K w B (oneLinearEquiv K w B (Submodule.Quotient.mk u)) = _ at hv
  rw [he] at hv
  exact hv

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ArithmeticTarget

end


noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteConeModels

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualModTwoResolution
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

abbrev gammaCyclesOne := LinearMap.ker
  ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 1 2).hom
abbrev gammaCyclesTwo := LinearMap.ker
  ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 2 3).hom

/-- The genuine first class map of the fixed finite Tate cochains. -/
def gammaClassOne : gammaCyclesOne K w B →+ H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) :=
  (explicitCoeff1Equiv (AbsoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)
    (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (pointLevelEquiv_smul (w.adicCompletion K) B 1)).toAddMonoidHom.comp kerToH1

/-- The genuine second class map of the same finite Tate cochains. -/
def gammaClassTwo : gammaCyclesTwo K w B →+ H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) :=
  (explicitCoeff2Equiv (AbsoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)
    (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (pointLevelEquiv_smul (w.adicCompletion K) B 1)).toAddMonoidHom.comp kerToH2

/-- Every genuine finite first cohomology class has an actual finite cochain representative. -/
theorem gammaClassOne_surjective : Function.Surjective (gammaClassOne K w B) :=
  (explicitCoeff1Equiv (AbsoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)
    (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (pointLevelEquiv_smul (w.adicCompletion K) B 1)).surjective.comp
      (kerToH1_surjective (k := ℤ_[2]) (G := AbsoluteGaloisGroup (w.adicCompletion K))
        (M := FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1))

/-- The genuine first class kernel is precisely the actual finite cochain boundary image. -/
theorem gammaClassOne_kernel (z : gammaCyclesOne K w B) : gammaClassOne K w B z = 0 ↔
    ∃ y : (finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).X 0,
      ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 0 1).hom y = z.val := by
  let e := explicitCoeff1Equiv (AbsoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)
    (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (pointLevelEquiv_smul (w.adicCompletion K) B 1)
  change e (kerToH1 z) = 0 ↔ _
  rw [e.map_eq_zero_iff]
  exact kerToH1_eq_zero_iff z

/-- Every genuine finite second cohomology class has an actual finite cochain representative. -/
theorem gammaClassTwo_surjective : Function.Surjective (gammaClassTwo K w B) :=
  (explicitCoeff2Equiv (AbsoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)
    (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (pointLevelEquiv_smul (w.adicCompletion K) B 1)).surjective.comp
      (kerToH2_surjective (k := ℤ_[2]) (G := AbsoluteGaloisGroup (w.adicCompletion K))
        (M := FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1))

/-- The genuine second class kernel is precisely the actual finite cochain boundary image. -/
theorem gammaClassTwo_kernel (z : gammaCyclesTwo K w B) : gammaClassTwo K w B z = 0 ↔
    ∃ y : (finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).X 1,
      ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 1 2).hom y = z.val := by
  let e := explicitCoeff2Equiv (AbsoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)
    (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (pointLevelEquiv_smul (w.adicCompletion K) B 1)
  change e (kerToH2 z) = 0 ↔ _
  rw [e.map_eq_zero_iff]
  exact kerToH2_eq_zero_iff z

/-- Degree zero of the genuine finite quotient-cone boundary uses the actual finite Kummer map. -/
theorem cone_d_zero (x : (finiteQuotientCone K w B).X 0) :
    (finiteQuotientCone K w B).d 0 1 rfl x =
      ((finitePointCochains K w B).d 0 1 rfl x.1 +
        (finiteConditionMap K w B).f 1 1 rfl x.2, 0) := by
  haveI : Subsingleton ((finitePointCondition K w B).X (1 + 1)) := by
    change Subsingleton PUnit
    infer_instance
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

/-- Above the local condition the actual finite cone differential is the actual coefficient cochain differential. -/
theorem cone_d_one (x : (finiteQuotientCone K w B).X 1) :
    (finiteQuotientCone K w B).d 1 2 rfl x =
      (((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 1 2).hom x.1, 0) := by
  haveI : Subsingleton ((finitePointCondition K w B).X (1 + 1)) := by change Subsingleton PUnit; infer_instance
  haveI : Subsingleton ((finitePointCondition K w B).X (2 + 1)) := by change Subsingleton PUnit; infer_instance
  apply Prod.ext
  · have hx : x.2 = 0 := Subsingleton.elim _ _
    change (finitePointCochains K w B).d 1 2 rfl x.1 + (finiteConditionMap K w B).f 2 2 rfl x.2 =
      (finitePointCochains K w B).d 1 2 rfl x.1
    rw [hx, map_zero, add_zero]
  · exact Subsingleton.elim _ _

/-- The same specified cone differential in degree two. -/
theorem cone_d_two (x : (finiteQuotientCone K w B).X 2) :
    (finiteQuotientCone K w B).d 2 3 rfl x =
      (((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 2 3).hom x.1, 0) := by
  haveI : Subsingleton ((finitePointCondition K w B).X (2 + 1)) := by change Subsingleton PUnit; infer_instance
  haveI : Subsingleton ((finitePointCondition K w B).X (3 + 1)) := by change Subsingleton PUnit; infer_instance
  apply Prod.ext
  · have hx : x.2 = 0 := Subsingleton.elim _ _
    change (finitePointCochains K w B).d 2 3 rfl x.1 + (finiteConditionMap K w B).f 3 3 rfl x.2 =
      (finitePointCochains K w B).d 2 3 rfl x.1
    rw [hx, map_zero, add_zero]
  · exact Subsingleton.elim _ _

/-- Actual finite quotient-cone cycles project to their specified first Galois cycles. -/
def cycleOneProjection : LinearMap.ker ((finiteQuotientCone K w B).d 1 2 rfl) →ₗ[ℤ_[2]] gammaCyclesOne K w B where
  toFun z := ⟨z.val.1, by
    have h := congrArg Prod.fst z.property
    erw [cone_d_one] at h
    exact h⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Actual second quotient-cone cycles project to their specified Galois cycles. -/
def cycleTwoProjection : LinearMap.ker ((finiteQuotientCone K w B).d 2 3 rfl) →ₗ[ℤ_[2]] gammaCyclesTwo K w B where
  toFun z := ⟨z.val.1, by
    have h := congrArg Prod.fst z.property
    erw [cone_d_two] at h
    exact h⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The specific first arithmetic class map of the finite quotient cone. -/
def classOne : LinearMap.ker ((finiteQuotientCone K w B).d 1 2 rfl) →+
    (H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) ⧸
      (B.kummerMap 2 (twoPower_isUnit (w.adicCompletion K) 1)).range) :=
  (QuotientAddGroup.mk' _).comp ((gammaClassOne K w B).comp (cycleOneProjection K w B).toAddMonoidHom)

/-- The specific second arithmetic class map of the same actual finite quotient cone. -/
def classTwo : LinearMap.ker ((finiteQuotientCone K w B).d 2 3 rfl) →+
    H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) :=
  (gammaClassTwo K w B).comp (cycleTwoProjection K w B).toAddMonoidHom

/-- Every genuine quotient by the actual finite Kummer image has a specified finite cone-cycle representative. -/
theorem classOne_surjective : Function.Surjective (classOne K w B) := by
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H y =>
    obtain ⟨c, hc⟩ := gammaClassOne_surjective K w B y
    have hz : (finiteQuotientCone K w B).d 1 2 rfl (c.val, 0) = 0 := by
      erw [cone_d_one]
      apply Prod.ext
      · change ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 1 2).hom c.val = 0
        exact c.property
      · rfl
    refine ⟨⟨(c.val, 0), hz⟩, ?_⟩
    change QuotientAddGroup.mk (gammaClassOne K w B c) = QuotientAddGroup.mk y
    rw [hc]

/-- The actual finite first class kernel is exactly the actual ordinary-cone boundary image. -/
theorem classOne_kernel (z : LinearMap.ker ((finiteQuotientCone K w B).d 1 2 rfl)) :
    classOne K w B z = 0 ↔ ∃ y : (finiteQuotientCone K w B).X 0,
      (finiteQuotientCone K w B).d 0 1 rfl y = z.val := by
  haveI : Subsingleton ((finitePointCondition K w B).X (1 + 1)) := by change Subsingleton PUnit; infer_instance
  change QuotientAddGroup.mk (gammaClassOne K w B (cycleOneProjection K w B z)) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · intro hz
    have hm : gammaClassOne K w B (cycleOneProjection K w B z) ∈ (FiniteConditionH1.classMapOne K w B).range := by
      rw [FiniteConditionH1.classMapOne_range]
      exact hz
    obtain ⟨u, hu⟩ := hm
    let c := cycleOneProjection K w B z
    let ku := FiniteConditionH1.cycleMapOne K w B u
    have hk : gammaClassOne K w B ku = FiniteConditionH1.classMapOne K w B u := rfl
    have hzero : gammaClassOne K w B (c - ku) = 0 := by
      rw [map_sub, hk, hu, sub_self]
    obtain ⟨b, hb⟩ := (gammaClassOne_kernel K w B _).mp hzero
    refine ⟨(b, u), ?_⟩
    erw [cone_d_zero]
    apply Prod.ext
    · change (finitePointCochains K w B).d 0 1 rfl b +
        (finiteConditionMap K w B).f 1 1 rfl u = z.val.1
      change (finitePointCochains K w B).d 0 1 rfl b =
        z.val.1 - (finiteConditionMap K w B).f 1 1 rfl u at hb
      rw [hb, sub_add_cancel]
    · exact Subsingleton.elim _ _
  · rintro ⟨⟨b, u⟩, hb⟩
    let c := cycleOneProjection K w B z
    let ku := FiniteConditionH1.cycleMapOne K w B u
    have hdb : ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 0 1).hom b =
        (c - ku).val := by
      have h := congrArg Prod.fst hb
      erw [cone_d_zero] at h
      change _ = z.val.1 - (finiteConditionMap K w B).f 1 1 rfl u
      exact eq_sub_of_add_eq h
    have hzero := (gammaClassOne_kernel K w B (c - ku)).mpr ⟨b, hdb⟩
    rw [map_sub] at hzero
    have hclass : gammaClassOne K w B c = gammaClassOne K w B ku := sub_eq_zero.mp hzero
    change gammaClassOne K w B c ∈ _
    rw [hclass]
    have hk : gammaClassOne K w B ku = FiniteConditionH1.classMapOne K w B u := rfl
    rw [hk, ← FiniteConditionH1.classMapOne_range]
    exact ⟨u, rfl⟩

/-- Every genuine finite second cohomology class has a representative in the specified actual quotient cone. -/
theorem classTwo_surjective : Function.Surjective (classTwo K w B) := by
  intro y
  obtain ⟨c, hc⟩ := gammaClassTwo_surjective K w B y
  have hz : (finiteQuotientCone K w B).d 2 3 rfl (c.val, 0) = 0 := by
    erw [cone_d_two]
    apply Prod.ext
    · change ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 2 3).hom c.val = 0
      exact c.property
    · rfl
  exact ⟨⟨(c.val, 0), hz⟩, hc⟩

/-- The actual finite second class kernel is exactly the specified cone boundary image. -/
theorem classTwo_kernel (z : LinearMap.ker ((finiteQuotientCone K w B).d 2 3 rfl)) :
    classTwo K w B z = 0 ↔ ∃ y : (finiteQuotientCone K w B).X 1,
      (finiteQuotientCone K w B).d 1 2 rfl y = z.val := by
  haveI : Subsingleton ((finitePointCondition K w B).X (2 + 1)) := by change Subsingleton PUnit; infer_instance
  change gammaClassTwo K w B (cycleTwoProjection K w B z) = 0 ↔ _
  rw [gammaClassTwo_kernel]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(b, 0), ?_⟩
    erw [cone_d_one]
    apply Prod.ext
    · exact hb
    · exact Subsingleton.elim _ _
  · rintro ⟨y, hy⟩
    refine ⟨y.1, ?_⟩
    have h := congrArg Prod.fst hy
    erw [cone_d_one] at h
    exact h

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteConeModels

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.QuasiIsoCycleComparisons

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {R : Type} [CommRing R] {A B : GCx R} (f : GHom A B)

/-- The actual quasi-isomorphism is onto on genuine cycle classes, with specified cochain representatives and boundaries. -/
theorem cycles_surjective (hf : QuasiIso (GHom.toCC f)) (n : ℤ) (z : B.X n)
    (hz : B.d n (n + 1) rfl z = 0) :
    ∃ (x : A.X n) (y : B.X (n - 1)), A.d n (n + 1) rfl x = 0 ∧
      f.f n n rfl x + B.d (n - 1) n (by omega) y = z := by
  let z' := (idGHom B).f n (n + 1 - 1) (by omega) z
  have hdz : B.d (n + 1 - 1) (n + 2 - 1) (by omega) z' = 0 := by
    have h := (idGHom B).comm n (n + 1) (n + 1 - 1) (n + 2 - 1)
      (by omega) rfl (by omega) (by omega) z
    rw [hz, map_zero] at h
    exact h.symm
  have hc : (coneCx f).d (n + 1) (n + 2) (by omega) ((0 : A.X (n + 1)), z') = 0 := by
    apply Prod.ext
    · exact map_zero _
    · change f.f (n + 1) (n + 2 - 1) (by omega) 0 - B.d (n + 1 - 1) (n + 2 - 1) (by omega) z' = 0
      rw [map_zero, hdz, sub_self]
  obtain ⟨⟨x, b⟩, hxb⟩ := coneCx_acyclic_of_quasiIso f hf n (n + 1) (n + 2) rfl (by omega) (0, z') hc
  have hx : A.d n (n + 1) rfl x = 0 := congrArg Prod.fst hxb
  have hb := congrArg Prod.snd hxb
  have h := congrArg ((idGHom B).f (n + 1 - 1) n (by omega)) hb
  change (idGHom B).f (n + 1 - 1) n (by omega)
      (f.f n (n + 1 - 1) (by omega) x - B.d (n - 1) (n + 1 - 1) (by omega) b) =
    (idGHom B).f (n + 1 - 1) n (by omega) z' at h
  rw [map_sub, SourceAlgebra.component_reindex] at h
  have hd := (idGHom B).comm (n - 1) (n + 1 - 1) (n - 1) n
    rfl (by omega) (by omega) (by omega) b
  rw [hd, idGHom_f_self] at h
  have hid : (idGHom B).f (n + 1 - 1) n (by omega) z' = z :=
    (idGHom_f_f B n (n + 1 - 1) n (by omega) (by omega) z).trans (idGHom_f_self B n rfl z)
  rw [hid] at h
  refine ⟨x, -b, hx, ?_⟩
  rw [map_neg, ← sub_eq_add_neg]
  exact h

/-- The actual quasi-isomorphism detects genuine cycle boundaries, without a class-count assumption. -/
theorem cycles_injective (hf : QuasiIso (GHom.toCC f)) (n : ℤ) (x : A.X n)
    (hx : A.d n (n + 1) rfl x = 0)
    (hb : ∃ b : B.X (n - 1), B.d (n - 1) n (by omega) b = f.f n n rfl x) :
    ∃ y : A.X (n - 1), A.d (n - 1) n (by omega) y = x := by
  obtain ⟨b, hb⟩ := hb
  have hfb : f.f n (n + 1 - 1) (by omega) x = B.d (n - 1) (n + 1 - 1) (by omega) b := by
    have h := congrArg ((idGHom B).f n (n + 1 - 1) (by omega)) hb
    have hd := (idGHom B).comm (n - 1) n (n - 1) (n + 1 - 1)
      rfl (by omega) (by omega) (by omega) b
    rw [hd, idGHom_f_self, SourceAlgebra.component_reindex] at h
    exact h.symm
  have hc : (coneCx f).d n (n + 1) rfl (x, b) = 0 := by
    apply Prod.ext hx
    exact sub_eq_zero.mpr hfb
  obtain ⟨⟨y, _⟩, hy⟩ := coneCx_acyclic_of_quasiIso f hf (n - 1) n (n + 1) (by omega) rfl (x, b) hc
  exact ⟨y, congrArg Prod.fst hy⟩

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.QuasiIsoCycleComparisons

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ArithmeticSourceModels

open CategoryTheory Matrix NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualModTwoResolution
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteConeModels

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]
  {c1 c2 : ℕ} (I : ActualBasedComparison.TwoTermConeBasedResolution K w B c1 c2)

abbrev source := (twoTermBased I.differential).map (PadicInt.toZMod (p := 2))

/-- The actual degree-two finite source coordinate inclusion. -/
def evenInclusion : (Fin c2 → ZMod 2) →ₗ[ZMod 2] (source K w B I).toGCx.X 2 where
  toFun x := ⟨Sum.elim x 0, by
    rintro (i | j) h
    · exact (h rfl).elim
    · rfl⟩
  map_add' x y := Subtype.ext (by
    change Sum.elim (x + y) (0 : Fin c1 → ZMod 2) =
      Sum.elim x (0 : Fin c1 → ZMod 2) + Sum.elim y (0 : Fin c1 → ZMod 2)
    funext i
    rcases i with i | i <;> simp)
  map_smul' r x := Subtype.ext (by
    change Sum.elim (r • x) (0 : Fin c1 → ZMod 2) = r • Sum.elim x (0 : Fin c1 → ZMod 2)
    funext i
    rcases i with i | i <;> simp)

/-- The actual degree-one finite source coordinate inclusion. -/
def oddInclusion : (Fin c1 → ZMod 2) →ₗ[ZMod 2] (source K w B I).toGCx.X 1 where
  toFun x := ⟨Sum.elim 0 x, by
    rintro (i | j) h
    · rfl
    · exact (h rfl).elim⟩
  map_add' x y := Subtype.ext (by
    change Sum.elim (0 : Fin c2 → ZMod 2) (x + y) =
      Sum.elim (0 : Fin c2 → ZMod 2) x + Sum.elim (0 : Fin c2 → ZMod 2) y
    funext i
    rcases i with i | i <;> simp)
  map_smul' r x := Subtype.ext (by
    change Sum.elim (0 : Fin c2 → ZMod 2) (r • x) = r • Sum.elim (0 : Fin c2 → ZMod 2) x
    funext i
    rcases i with i | i <;> simp)

/-- Exact reading of the source coordinates in degree two. -/
def evenValues : (source K w B I).toGCx.X 2 →ₗ[ZMod 2] (Fin c2 → ZMod 2) where
  toFun x i := x.val (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact reading of the source coordinates in degree one. -/
def oddValues : (source K w B I).toGCx.X 1 →ₗ[ZMod 2] (Fin c1 → ZMod 2) where
  toFun x i := x.val (Sum.inr i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem even_reconstruct (x : (source K w B I).toGCx.X 2) : evenInclusion K w B I (evenValues K w B I x) = x := by
  apply Subtype.ext
  funext i
  rcases i with i | i
  · rfl
  · exact (x.property (Sum.inr i) (by change (1 : ℤ) ≠ 2; norm_num)).symm

theorem odd_reconstruct (x : (source K w B I).toGCx.X 1) : oddInclusion K w B I (oddValues K w B I x) = x := by
  apply Subtype.ext
  funext i
  rcases i with i | i
  · exact (x.property (Sum.inl i) (by change (2 : ℤ) ≠ 1; norm_num)).symm
  · rfl

/-- All unsupported finite source terms are actually zero. -/
theorem source_subsingleton (n : ℤ) (hn1 : n ≠ 1) (hn2 : n ≠ 2) : Subsingleton ((source K w B I).toGCx.X n) := by
  refine ⟨fun x y => Subtype.ext (funext fun i => ?_)⟩
  rcases i with i | i
  · exact (x.property (Sum.inl i) (by change (2 : ℤ) ≠ n; exact hn2.symm)).trans
      (y.property (Sum.inl i) (by change (2 : ℤ) ≠ n; exact hn2.symm)).symm
  · exact (x.property (Sum.inr i) (by change (1 : ℤ) ≠ n; exact hn1.symm)).trans
      (y.property (Sum.inr i) (by change (1 : ℤ) ≠ n; exact hn1.symm)).symm

/-- The source's even-to-odd matrix is exactly zero after the prescribed reduction. -/
theorem source_dOE_zero : (source K w B I).dOE = 0 := by
  change (0 : Matrix (Fin c1) (Fin c2) ℤ_[2]).map PadicInt.toZMod = 0
  exact Matrix.map_zero _ (map_zero PadicInt.toZMod)

/-- The actual finite source differential in its prescribed coordinate maps. -/
theorem odd_d (x : Fin c1 → ZMod 2) :
    (source K w B I).toGCx.d 1 2 rfl (oddInclusion K w B I x) =
      evenInclusion K w B I ((source K w B I).dEO *ᵥ x) := by
  apply Subtype.ext
  change (source K w B I).dTot *ᵥ Sum.elim 0 x = Sum.elim ((source K w B I).dEO *ᵥ x) 0
  rw [BasedCx.dTot, fromBlocks_mulVec]
  change Sum.elim ((0 : Matrix (Fin c2) (Fin c2) (ZMod 2)) *ᵥ 0 + (source K w B I).dEO *ᵥ x)
      ((source K w B I).dOE *ᵥ 0 + (0 : Matrix (Fin c1) (Fin c1) (ZMod 2)) *ᵥ x) = _
  rw [zero_mulVec, zero_add, mulVec_zero, zero_mulVec, add_zero]

/-- The outgoing source differential in degree two is actually zero. -/
theorem even_cycle (x : Fin c2 → ZMod 2) : (source K w B I).toGCx.d 2 3 rfl (evenInclusion K w B I x) = 0 := by
  haveI := source_subsingleton K w B I 3 (by norm_num) (by norm_num)
  exact Subsingleton.elim _ _

/-- The actual realized even source cycle in the finite Kummer quotient cone. -/
def evenConeCycle : cyclesE (source K w B I) →+ LinearMap.ker ((finiteQuotientCone K w B).d 2 3 rfl) where
  toFun x := ⟨(reducedRealization K w B I).f 2 2 rfl (evenInclusion K w B I x.val), by
    have hs : (restrictCx PadicInt.toZMod (source K w B I).toGCx).d 2 3 rfl (evenInclusion K w B I x.val) = 0 :=
      even_cycle K w B I x.val
    have h := (reducedRealization K w B I).comm 2 3 2 3 rfl rfl rfl rfl (evenInclusion K w B I x.val)
    change (finiteQuotientCone K w B).d 2 3 rfl ((reducedRealization K w B I).f 2 2 rfl (evenInclusion K w B I x.val)) = 0
    rw [hs, map_zero] at h
    exact h.symm⟩
  map_zero' := Subtype.ext (by
    change (reducedRealization K w B I).f 2 2 rfl (evenInclusion K w B I (0 : Fin c2 → ZMod 2)) = 0
    erw [map_zero, map_zero])
  map_add' x y := Subtype.ext (by
    change (reducedRealization K w B I).f 2 2 rfl (evenInclusion K w B I (x.val + y.val)) =
      (reducedRealization K w B I).f 2 2 rfl (evenInclusion K w B I x.val) +
        (reducedRealization K w B I).f 2 2 rfl (evenInclusion K w B I y.val)
    erw [map_add, map_add])

/-- The actual realized odd finite source cycle in the same quotient cone. -/
def oddConeCycle : cyclesO (source K w B I) →+ LinearMap.ker ((finiteQuotientCone K w B).d 1 2 rfl) where
  toFun x := ⟨(reducedRealization K w B I).f 1 1 rfl (oddInclusion K w B I x.val), by
    have hs : (restrictCx PadicInt.toZMod (source K w B I).toGCx).d 1 2 rfl (oddInclusion K w B I x.val) = 0 := by
      change (source K w B I).toGCx.d 1 2 rfl (oddInclusion K w B I x.val) = 0
      rw [odd_d, (show (source K w B I).dEO *ᵥ x.val = 0 from x.property), map_zero]
    have h := (reducedRealization K w B I).comm 1 2 1 2 rfl rfl rfl rfl (oddInclusion K w B I x.val)
    change (finiteQuotientCone K w B).d 1 2 rfl ((reducedRealization K w B I).f 1 1 rfl (oddInclusion K w B I x.val)) = 0
    rw [hs, map_zero] at h
    exact h.symm⟩
  map_zero' := Subtype.ext (by
    change (reducedRealization K w B I).f 1 1 rfl (oddInclusion K w B I (0 : Fin c1 → ZMod 2)) = 0
    erw [map_zero, map_zero])
  map_add' x y := Subtype.ext (by
    change (reducedRealization K w B I).f 1 1 rfl (oddInclusion K w B I (x.val + y.val)) =
      (reducedRealization K w B I).f 1 1 rfl (oddInclusion K w B I x.val) +
        (reducedRealization K w B I).f 1 1 rfl (oddInclusion K w B I y.val)
    erw [map_add, map_add])

/-- The prescribed arithmetic even class map of the actual reduced source. -/
def evenClass : cyclesE (source K w B I) →ₗ[ZMod 2] H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) :=
  ((FiniteConeModels.classTwo K w B).comp (evenConeCycle K w B I)).toZModLinearMap 2

/-- The prescribed arithmetic odd class map of the same actual source. -/
def oddClass : cyclesO (source K w B I) →ₗ[ZMod 2]
    (H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) ⧸
      (B.kummerMap 2 (ZInQ.Contrib.RC53Assist.DerivedKummer.twoPower_isUnit (w.adicCompletion K) 1)).range) :=
  ((FiniteConeModels.classOne K w B).comp (oddConeCycle K w B I)).toZModLinearMap 2

/-- The actual finite even arithmetic class map respects precisely the specified cone boundaries. -/
theorem finiteClassTwo_eq_of_boundary
    (x y : LinearMap.ker ((finiteQuotientCone K w B).d 2 3 rfl))
    (h : ∃ z : (finiteQuotientCone K w B).X 1, (finiteQuotientCone K w B).d 1 2 rfl z = x.val - y.val) :
    FiniteConeModels.classTwo K w B x = FiniteConeModels.classTwo K w B y := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (FiniteConeModels.classTwo_kernel K w B _).mpr h

/-- The odd arithmetic class map has the same actual boundary recognition property. -/
theorem finiteClassOne_eq_of_boundary
    (x y : LinearMap.ker ((finiteQuotientCone K w B).d 1 2 rfl))
    (h : ∃ z : (finiteQuotientCone K w B).X 0, (finiteQuotientCone K w B).d 0 1 rfl z = x.val - y.val) :
    FiniteConeModels.classOne K w B x = FiniteConeModels.classOne K w B y := by
  have hz : FiniteConeModels.classOne K w B (x - y) = 0 :=
    (FiniteConeModels.classOne_kernel K w B _).mpr h
  have hm := map_sub (FiniteConeModels.classOne K w B) x y
  exact sub_eq_zero.mp (hm.symm.trans hz)

/-- Actual surjectivity of the reduced realization proves onto for the prescribed even arithmetic class map. -/
theorem evenClass_surjective : Function.Surjective (evenClass K w B I) := by
  intro y
  obtain ⟨c, hc⟩ := FiniteConeModels.classTwo_surjective K w B y
  obtain ⟨x, b, hx, hxb⟩ := QuasiIsoCycleComparisons.cycles_surjective
    (reducedRealization K w B I) (reducedRealization_quasiIso K w B I) 2 c.val c.property
  let u := evenValues K w B I x
  have hu : (source K w B I).dOE *ᵥ u = 0 := by rw [source_dOE_zero, zero_mulVec]
  let z : cyclesE (source K w B I) := ⟨u, hu⟩
  have he : (evenConeCycle K w B I z).val = (reducedRealization K w B I).f 2 2 rfl x :=
    congrArg ((reducedRealization K w B I).f 2 2 rfl) (even_reconstruct K w B I x)
  have hb : ∃ v : (finiteQuotientCone K w B).X 1,
      (finiteQuotientCone K w B).d 1 2 rfl v = c.val - (evenConeCycle K w B I z).val := by
    refine ⟨b, ?_⟩
    have h : (finiteQuotientCone K w B).d 1 2 rfl b + (evenConeCycle K w B I z).val = c.val := by
      rw [he, add_comm]
      exact hxb
    exact eq_sub_of_add_eq h
  have hclass := finiteClassTwo_eq_of_boundary K w B c (evenConeCycle K w B I z) hb
  exact ⟨z, hclass.symm.trans hc⟩

/-- Actual surjectivity of the reduced realization proves onto for the prescribed odd arithmetic class map. -/
theorem oddClass_surjective : Function.Surjective (oddClass K w B I) := by
  intro y
  obtain ⟨c, hc⟩ := FiniteConeModels.classOne_surjective K w B y
  obtain ⟨x, b, hx, hxb⟩ := QuasiIsoCycleComparisons.cycles_surjective
    (reducedRealization K w B I) (reducedRealization_quasiIso K w B I) 1 c.val c.property
  have hds : (source K w B I).dEO *ᵥ oddValues K w B I x = 0 := by
    change (source K w B I).toGCx.d 1 2 rfl x = 0 at hx
    erw [← odd_reconstruct K w B I x, odd_d] at hx
    exact congrArg (evenValues K w B I) hx
  let z : cyclesO (source K w B I) := ⟨oddValues K w B I x, hds⟩
  have he : (oddConeCycle K w B I z).val = (reducedRealization K w B I).f 1 1 rfl x :=
    congrArg ((reducedRealization K w B I).f 1 1 rfl) (odd_reconstruct K w B I x)
  have hb : ∃ v : (finiteQuotientCone K w B).X 0,
      (finiteQuotientCone K w B).d 0 1 rfl v = c.val - (oddConeCycle K w B I z).val := by
    refine ⟨b, ?_⟩
    have h : (finiteQuotientCone K w B).d 0 1 rfl b + (oddConeCycle K w B I z).val = c.val := by
      rw [he, add_comm]
      exact hxb
    exact eq_sub_of_add_eq h
  have hclass := finiteClassOne_eq_of_boundary K w B c (oddConeCycle K w B I z) hb
  exact ⟨z, hclass.symm.trans hc⟩

/-- The prescribed even arithmetic class map has exactly the actual source matrix boundary kernel. -/
theorem evenClass_kernel (x : cyclesE (source K w B I)) :
    evenClass K w B I x = 0 ↔ ∃ b : Fin c1 → ZMod 2, (source K w B I).dEO *ᵥ b = x.val := by
  constructor
  · intro hx
    have hclass : FiniteConeModels.classTwo K w B (evenConeCycle K w B I x) = 0 := hx
    obtain ⟨b, hb⟩ := (FiniteConeModels.classTwo_kernel K w B _).mp hclass
    obtain ⟨y, hy⟩ := QuasiIsoCycleComparisons.cycles_injective
      (reducedRealization K w B I) (reducedRealization_quasiIso K w B I) 2
      (evenInclusion K w B I x.val) (even_cycle K w B I x.val) ⟨b, hb⟩
    change (source K w B I).toGCx.d 1 2 rfl y = evenInclusion K w B I x.val at hy
    erw [← odd_reconstruct K w B I y, odd_d] at hy
    exact ⟨oddValues K w B I y, congrArg (evenValues K w B I) hy⟩
  · rintro ⟨b, hb⟩
    have hds : (restrictCx PadicInt.toZMod (source K w B I).toGCx).d 1 2 rfl (oddInclusion K w B I b) =
        evenInclusion K w B I x.val := by
      change (source K w B I).toGCx.d 1 2 rfl (oddInclusion K w B I b) = _
      rw [odd_d, hb]
    have h := (reducedRealization K w B I).comm 1 2 1 2 rfl rfl rfl rfl (oddInclusion K w B I b)
    rw [hds] at h
    change FiniteConeModels.classTwo K w B (evenConeCycle K w B I x) = 0
    apply (FiniteConeModels.classTwo_kernel K w B _).mpr
    exact ⟨(reducedRealization K w B I).f 1 1 rfl (oddInclusion K w B I b), h.symm⟩

/-- The prescribed odd arithmetic class map has exactly the actual source matrix boundary kernel. -/
theorem oddClass_kernel (x : cyclesO (source K w B I)) :
    oddClass K w B I x = 0 ↔ ∃ b : Fin c2 → ZMod 2, (source K w B I).dOE *ᵥ b = x.val := by
  constructor
  · intro hx
    have hclass : FiniteConeModels.classOne K w B (oddConeCycle K w B I x) = 0 := hx
    obtain ⟨b, hb⟩ := (FiniteConeModels.classOne_kernel K w B _).mp hclass
    have hds : (restrictCx PadicInt.toZMod (source K w B I).toGCx).d 1 2 rfl (oddInclusion K w B I x.val) = 0 := by
      change (source K w B I).toGCx.d 1 2 rfl (oddInclusion K w B I x.val) = 0
      rw [odd_d, (show (source K w B I).dEO *ᵥ x.val = 0 from x.property), map_zero]
    obtain ⟨y, hy⟩ := QuasiIsoCycleComparisons.cycles_injective
      (reducedRealization K w B I) (reducedRealization_quasiIso K w B I) 1
      (oddInclusion K w B I x.val) hds ⟨b, hb⟩
    haveI : Subsingleton ((restrictCx PadicInt.toZMod (source K w B I).toGCx).X 0) := by
      change Subsingleton ((source K w B I).toGCx.X 0)
      exact source_subsingleton K w B I 0 (by norm_num) (by norm_num)
    have hy0 : y = 0 := (source_subsingleton K w B I 0 (by norm_num) (by norm_num)).elim y 0
    rw [hy0, map_zero] at hy
    have hx0 : x.val = 0 := (congrArg (oddValues K w B I) hy).symm
    exact ⟨0, by rw [mulVec_zero, hx0]⟩
  · rintro ⟨b, hb⟩
    rw [source_dOE_zero, zero_mulVec] at hb
    have hx0 : x = 0 := Subtype.ext hb.symm
    rw [hx0, map_zero]

/-- The full cohomology model of the actual reduced source has the genuine finite Galois arithmetic class groups. -/
def model : CohomologyModel (source K w B I)
    (H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2))
    (H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) ⧸
      (B.kummerMap 2 (ZInQ.Contrib.RC53Assist.DerivedKummer.twoPower_isUnit (w.adicCompletion K) 1)).range) where
  classE := evenClass K w B I
  ontoE := evenClass_surjective K w B I
  kernelE := evenClass_kernel K w B I
  classO := oddClass K w B I
  ontoO := oddClass_surjective K w B I
  kernelO := oddClass_kernel K w B I

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ArithmeticSourceModels

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ArithmeticTargetModels

open CategoryTheory Matrix NumberField IsDedekindDomain TauCeti
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualBasedComparison

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

abbrev target := (dualPresentationCx (actualLocalPresentation K w B).f).map PadicInt.toZMod
abbrev coordinateTarget := dualPresentationCx (pointDifferentialModTwo K w B)

/-- The literal target relation matrix is the prescribed finite dual relation matrix. -/
theorem dEO_eq : (target K w B).dEO = (coordinateTarget K w B).dEO :=
  congrArg (fun C => C.dEO) (dualPresentationCx_map PadicInt.toZMod (actualLocalPresentation K w B).f)

/-- The other matrix has the same literal zero-coordinate description. -/
theorem dOE_eq : (target K w B).dOE = (coordinateTarget K w B).dOE :=
  congrArg (fun C => C.dOE) (dualPresentationCx_map PadicInt.toZMod (actualLocalPresentation K w B).f)

/-- The target even cycle map preserves its actual finite coordinate vector. -/
def evenCycle : cyclesE (target K w B) →ₗ[ZMod 2] cyclesE (coordinateTarget K w B) where
  toFun x := ⟨x.val, by
    have hx : (target K w B).dOE *ᵥ x.val = 0 := x.property
    rw [dOE_eq] at hx
    exact hx⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The target odd cycle map preserves its actual finite coordinate vector. -/
def oddCycle : cyclesO (target K w B) →ₗ[ZMod 2] cyclesO (coordinateTarget K w B) where
  toFun x := ⟨x.val, by
    have hx : (target K w B).dEO *ᵥ x.val = 0 := x.property
    rw [dEO_eq] at hx
    exact hx⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem evenCycle_surjective : Function.Surjective (evenCycle K w B) := by
  intro x
  have hx : (target K w B).dOE *ᵥ x.val = 0 := by
    rw [dOE_eq]
    exact x.property
  exact ⟨⟨x.val, hx⟩, rfl⟩

theorem oddCycle_surjective : Function.Surjective (oddCycle K w B) := by
  intro x
  have hx : (target K w B).dEO *ᵥ x.val = 0 := by
    rw [dEO_eq]
    exact x.property
  exact ⟨⟨x.val, hx⟩, rfl⟩

/-- The literal reduced dual target has its full canonical finite cohomology model, with no equality-transported class-value ambiguity. -/
def model : CohomologyModel (target K w B)
    (Module.Dual (ZMod 2) (LinearMap.ker (pointDifferentialModTwo K w B)))
    (Module.Dual (ZMod 2)
      ((Fin (actualLocalPresentation K w B).rankZero → ZMod 2) ⧸ LinearMap.range (pointDifferentialModTwo K w B))) where
  classE := (dualPresentationModel (pointDifferentialModTwo K w B)).classE.comp (evenCycle K w B)
  ontoE := (dualPresentationModel (pointDifferentialModTwo K w B)).ontoE.comp (evenCycle_surjective K w B)
  kernelE x := by
    have h := (dualPresentationModel (pointDifferentialModTwo K w B)).kernelE (evenCycle K w B x)
    change (dualPresentationModel (pointDifferentialModTwo K w B)).classE (evenCycle K w B x) = 0 ↔ _
    rw [dEO_eq]
    exact h
  classO := (dualPresentationModel (pointDifferentialModTwo K w B)).classO.comp (oddCycle K w B)
  ontoO := (dualPresentationModel (pointDifferentialModTwo K w B)).ontoO.comp (oddCycle_surjective K w B)
  kernelO x := by
    have h := (dualPresentationModel (pointDifferentialModTwo K w B)).kernelO (oddCycle K w B x)
    change (dualPresentationModel (pointDifferentialModTwo K w B)).classO (oddCycle K w B x) = 0 ↔ _
    rw [dOE_eq]
    exact h

/-- The even class map is exactly restriction of the standard coordinate dual to the actual reduced relation kernel. -/
theorem classE_value (x : cyclesE (target K w B)) (r : LinearMap.ker (pointDifferentialModTwo K w B)) :
    (model K w B).classE x r = vectorDual (actualLocalPresentation K w B).rankOne x.val r.val := rfl

/-- The odd class map is exactly the standard coordinate dual on quotient representatives. -/
theorem classO_value (x : cyclesO (target K w B))
    (r : Fin (actualLocalPresentation K w B).rankZero → ZMod 2) :
    (model K w B).classO x (Submodule.Quotient.mk r) = vectorDual (actualLocalPresentation K w B).rankZero x.val r := rfl

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ArithmeticTargetModels

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ArithmeticComparisons

open NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualBasedComparison
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ArithmeticTarget

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- The finite second-degree Milne comparison with its specified invariant evaluation, not an unrelated group isomorphism. -/
def milneEven (hF : MilneFiniteLocalDualityPrint) :
    H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) (AddSubgroup.torsionBy B.toAffine.Point 2) :=
  (kummer_modTwo_torsion_comparison_of_print hF (w.adicCompletion K) B
    (twoPower_isUnit (w.adicCompletion K) 1)).choose

/-- The selected comparison is computed by the actual finite cup and local invariant. -/
theorem milneEven_value (hF : MilneFiniteLocalDualityPrint)
    (y : H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2))
    (t : AddSubgroup.torsionBy B.toAffine.Point 2) :
    ZMod.toRatAddCircle 2 (milneEven K w B hF y t) =
      localH2TorsionValue B 2 (twoPower_isUnit (w.adicCompletion K) 1) y t :=
  (kummer_modTwo_torsion_comparison_of_print hF (w.adicCompletion K) B
    (twoPower_isUnit (w.adicCompletion K) 1)).choose_spec y t

/-- The finite first-degree Milne quotient comparison with its exact Kummer cup evaluation. -/
def milneOdd (hM : MilneLocalDualityPrint) :
    (H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) ⧸
      (B.kummerMap 2 (twoPower_isUnit (w.adicCompletion K) 1)).range) ≃ₗ[ZMod 2]
        Module.Dual (ZMod 2) (TateDualityData.pointMod (P := B.toAffine.Point) 2) :=
  (kummer_modTwo_linear_comparison_of_print hM (w.adicCompletion K) B
    (twoPower_isUnit (w.adicCompletion K) 1)).choose

/-- Its evaluation is the genuine finite local Tate pairing on actual rational points. -/
theorem milneOdd_value (hM : MilneLocalDualityPrint)
    (y : H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2)) (p : B.toAffine.Point) :
    ZMod.toRatAddCircle 2 (milneOdd K w B hM (QuotientAddGroup.mk y) (QuotientAddGroup.mk p)) =
      ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 (twoPower_isUnit (w.adicCompletion K) 1)
        (B.kummerMap 2 (twoPower_isUnit (w.adicCompletion K) 1) p) y :=
  (kummer_modTwo_linear_comparison_of_print hM (w.adicCompletion K) B
    (twoPower_isUnit (w.adicCompletion K) 1)).choose_spec y p

/-- The actual arithmetic even comparison to the dual reduced point-presentation kernel. -/
def alphaEven (hF : MilneFiniteLocalDualityPrint) :
    H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) (LinearMap.ker (pointDifferentialModTwo K w B)) :=
  (milneEven K w B hF).trans (zeroLinearEquiv K w B).dualMap

/-- The actual arithmetic odd comparison to the dual reduced point-presentation cokernel. -/
def alphaOdd (hM : MilneLocalDualityPrint) :
    (H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) ⧸
      (B.kummerMap 2 (twoPower_isUnit (w.adicCompletion K) 1)).range) ≃ₗ[ZMod 2]
        Module.Dual (ZMod 2)
          ((Fin (actualLocalPresentation K w B).rankZero → ZMod 2) ⧸ LinearMap.range (pointDifferentialModTwo K w B)) :=
  (milneOdd K w B hM).trans (oneLinearEquiv K w B).dualMap

/-- The even comparison is bijective because the actual retained-torsion map and the finite Milne map are. -/
theorem alphaEven_bijective (hF : MilneFiniteLocalDualityPrint) : Function.Bijective (alphaEven K w B hF) :=
  (alphaEven K w B hF).bijective

/-- The odd comparison is bijective because the actual completed-point quotient map and the finite Milne map are. -/
theorem alphaOdd_bijective (hM : MilneLocalDualityPrint) : Function.Bijective (alphaOdd K w B hM) :=
  (alphaOdd K w B hM).bijective

/-- The actual even arithmetic comparison evaluates through the specified rational-torsion map. -/
theorem alphaEven_value (hF : MilneFiniteLocalDualityPrint)
    (y : H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2))
    (r : LinearMap.ker (pointDifferentialModTwo K w B)) :
    ZMod.toRatAddCircle 2 (alphaEven K w B hF y r) =
      localH2TorsionValue B 2 (twoPower_isUnit (w.adicCompletion K) 1) y (zeroLinearEquiv K w B r) :=
  milneEven_value K w B hF y (zeroLinearEquiv K w B r)

/-- The actual odd arithmetic comparison evaluates through the specified completed-point quotient map. -/
theorem alphaOdd_value (hM : MilneLocalDualityPrint)
    (y : H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2))
    (r : (Fin (actualLocalPresentation K w B).rankZero → ZMod 2) ⧸ LinearMap.range (pointDifferentialModTwo K w B))
    (p : B.toAffine.Point) (hr : oneLinearEquiv K w B r = QuotientAddGroup.mk p) :
    ZMod.toRatAddCircle 2 (alphaOdd K w B hM (QuotientAddGroup.mk y) r) =
      ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 (twoPower_isUnit (w.adicCompletion K) 1)
        (B.kummerMap 2 (twoPower_isUnit (w.adicCompletion K) 1) p) y := by
  change ZMod.toRatAddCircle 2 (milneOdd K w B hM (QuotientAddGroup.mk y) (oneLinearEquiv K w B r)) = _
  rw [hr]
  exact milneOdd_value K w B hM y p

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ArithmeticComparisons

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteCupSymmetry

open TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.CloudB3RC53.Duality

variable {G M P : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P] [IsTopologicalAddGroup P]
  [DistribMulAction G P] [ContinuousSMul G P]
  (e : M →+ M →+ P)
  (he : ∀ (σ : G) x y, e (σ • x) (σ • y) = σ • e x y)
  (halt : ∀ x, e x x = 0)

include halt in
/-- Alternation gives the precise coefficient skew-symmetry, without a finite characteristic assumption. -/
theorem coefficient_skew (x y : M) : e x y = -e y x := by
  have h := halt (x + y)
  simp only [map_add, AddMonoidHom.add_apply, halt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

include he halt in
/-- The difference of the two actual degree-one cups is the displayed continuous coboundary. -/
theorem cup_swap_differential (f g : Z1 G M) :
    cupFun e f g - cupFun e g f = d1 G P (fun σ => -e (f.val σ) (g.val σ)) := by
  funext q
  obtain ⟨σ, τ⟩ := q
  have hf := (mem_Z1_iff.mp f.property).2 σ τ
  have hg := (mem_Z1_iff.mp g.property).2 σ τ
  simp only [Pi.sub_apply, cupFun, d1_apply, smul_neg, neg_neg]
  rw [hf, hg]
  simp only [map_add, AddMonoidHom.add_apply]
  rw [he, coefficient_skew e halt (σ • f.val τ) (g.val σ)]
  abel

include halt in
/-- The two genuine cup cocycles differ by an actual continuous boundary. -/
theorem cup_difference_boundary (f g : Z1 G M) :
    (cupZ e he f g - cupZ e he g f : G × G → P) ∈ B2 G P := by
  rw [mem_B2_iff]
  refine ⟨fun σ => -e (f.val σ) (g.val σ), ?_, ?_⟩
  · exact ((continuous_uncurry_of_discrete (fun x y : M => e x y)).comp
      ((mem_Z1_iff.mp f.property).1.prodMk (mem_Z1_iff.mp g.property).1)).neg
  · exact (cup_swap_differential e he halt f g).symm

include halt in
/-- The actual cohomological Weil cup is symmetric in degree one. -/
theorem cupH_symmetric (f g : H1 G M) : cupH e he f g = cupH e he g f := by
  induction f using QuotientAddGroup.induction_on with
  | H f =>
    induction g using QuotientAddGroup.induction_on with
    | H g =>
      apply sub_eq_zero.mp
      change H2pi G P (cupZ e he f g) - H2pi G P (cupZ e he g f) = 0
      rw [← map_sub]
      exact H2pi_eq_zero_of_mem_B2 (cup_difference_boundary e he halt f g)

/-- The specific finite local Tate pairing has the resulting symmetry, with its genuine invariant normalization. -/
theorem localTatePairing_symmetric
    (F : Type) [Field F] [DecidableEq F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
    (n : ℕ) (hn : IsUnit (n : F)) (f g : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff n)) :
    localTatePairing B n hn f g = localTatePairing B n hn g f := by
  have h := cupH_symmetric (B.torsionCoeffWeilPairing n hn)
    (fun σ x y => B.torsionCoeffWeilPairing_smul n hn σ x y)
    (fun x => B.torsionCoeffWeilPairing_self n hn x) f g
  exact congrArg (fun z => TauCeti.ClassFieldTheory.invMap F (kummerToBr n z)) h

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteCupSymmetry

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.SecondCupCompatibility

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTraceCompatibility
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteCupCompatibility
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.CoordinateReduction

/-- The first-power residue map is the prescribed mod-two scalar map. -/
theorem first_residue_eq : PadicInt.toZModPow (p := 2) 1 = PadicInt.toZMod := by
  apply ZMod.ringHom_eq_of_ker_eq
  rw [PadicInt.ker_toZModPow, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, pow_one]

/-- The actual two-zero cup value includes the product of the first two Galois elements, in its prescribed order. -/
theorem cupFun_two_zero_apply {G A T : Type} [Group G] [AddCommGroup A] [Module ℤ_[2] A]
    [DistribMulAction G A] [AddCommGroup T] [Module ℤ_[2] T]
    (β : A →ₗ[ℤ_[2]] A →ₗ[ℤ_[2]] T) (a : (Fin 2 → G) → A) (b : (Fin 0 → G) → A)
    (g : Fin 2 → G) :
    ZInQ.Manuscript.RC.SelmerComplex.cupFun β 2 0 2 rfl a b g = β (a g) ((g 0 * g 1) • b Fin.elim0) := by
  rw [cupFun_apply]
  have ha : (fun i : Fin 2 => g (Fin.castLE (by omega) i)) = g := by
    funext i
    rfl
  have hb : (fun j : Fin 0 => g ⟨2 + j, by omega⟩) = Fin.elim0 := Subsingleton.elim _ _
  have hp : headProd 2 2 (by omega) g = g 0 * g 1 := by
    rw [headProd_succ, headProd_succ, headProd_zero, one_mul]
    rfl
  rw [ha, hb, hp]

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- The genuine integral cup in bidegree two-zero. -/
def cupTwoZero : (pointComplex (w.adicCompletion K) B).X 2 →ₗ[ℤ_[2]]
    (pointComplex (w.adicCompletion K) B).X 0 →ₗ[ℤ_[2]] (actualTraceComplex (w.adicCompletion K)).X 2 :=
  (integralCupPair (w.adicCompletion K) B).P 2 0 2 rfl

/-- An actual finite zero-cochain with the prescribed rational-torsion value is an actual finite Galois cycle. -/
theorem zero_first_cycle (a : (pointComplex (w.adicCompletion K) B).X 0)
    (t : AddSubgroup.torsionBy B.toAffine.Point 2)
    (ha : IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 (cfun a Fin.elim0)) = B.baseTorsionCoeff 2 t) :
    ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 0 1).hom
      (((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).f 0).hom a) = 0 := by
  apply contCochains_ext
  intro s
  have hs : s = fun _ => s 0 := by funext i; rw [Subsingleton.elim i 0]
  rw [hs, contFun_d01]
  apply (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1).injective
  change IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1
      ((s 0) • coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 (cfun a Fin.elim0) -
        coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 (cfun a Fin.elim0)) = _
  rw [map_sub, pointLevelEquiv_smul, ha, B.smul_baseTorsionCoeff, sub_self]
  change (0 : B.TorsionCoeff 2) = IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1 0
  exact (map_zero (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1)).symm

/-- The actual two-zero cup is a finite cycle under the prescribed projection when the second factor represents rational torsion. -/
theorem cup_two_zero_first_cycle
    (z : LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 2 3).hom)
    (a : (pointComplex (w.adicCompletion K) B).X 0)
    (t : AddSubgroup.torsionBy B.toAffine.Point 2)
    (ha : IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 (cfun a Fin.elim0)) = B.baseTorsionCoeff 2 t) :
    ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) (UnitsCoeff (w.adicCompletion K)) 1).d 2 3).hom
      (((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) (UnitsCoeff (w.adicCompletion K)) 1).f 2).hom
        (cupTwoZero K w B z.val a)) = 0 := by
  haveI := point_coefficients_compact (w.adicCompletion K) B
  haveI := cyclotomic_coefficients_compact (w.adicCompletion K)
  have hda : ((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).f 1).hom
      (((pointComplex (w.adicCompletion K) B).d 0 1).hom a) = 0 := by
    rw [reduceCochains_d]
    exact zero_first_cycle K w B a t ha
  obtain ⟨b, hb⟩ := (first_cochain_kernel (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 _).mp hda
  have hz : ((pointComplex (w.adicCompletion K) B).d 2 3).hom z.val = 0 := z.property
  have h := (integralCupPair (w.adicCompletion K) B).leib 2 0 2 rfl z.val a
  rw [hz, LinearMap.map_zero₂, zero_add] at h
  simp only [neg_one_sq, one_smul] at h
  rw [← hb, map_smul] at h
  rw [← reduceCochains_d]
  apply (first_cochain_kernel (AbsoluteGaloisGroup (w.adicCompletion K)) (UnitsCoeff (w.adicCompletion K)) 3 _).mpr
  exact ⟨_, h.symm⟩

/-- The specific first finite second point class of an actual integral two-cycle. -/
def pointSecondClass (z : LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 2 3).hom) :
    H2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) :=
  FiniteConeModels.gammaClassTwo K w B (reduceTwoCycle (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 z)

/-- The specific finite two-cocycle of the integral point-class reduction. -/
def pointSecondZ2 (z : LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 2 3).hom) :
    Z2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) :=
  cocyclesMap2 (AbsoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1)
    (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2) (ContinuousMonoidHom.id _)
    (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1).toAddMonoidHom continuous_of_discreteTopology
    (pointLevelEquiv_smul (w.adicCompletion K) B 1)
    ⟨fun p => cfun (reduceTwoCycle (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 z).val ![p.1, p.2],
      mem_Z2_of_d_eq_zero _ (reduceTwoCycle (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 z).property⟩

/-- The finite point class uses this very cocycle, not a selected independent class representative. -/
theorem pointSecondClass_cocycle (z : LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 2 3).hom) :
    pointSecondClass K w B z = H2pi _ _ (pointSecondZ2 K w B z) := rfl

/-- The actual finite trace-target cocycle of a prescribed finite-cycle cochain. -/
def traceSecondZ2 (c : (actualTraceComplex (w.adicCompletion K)).X 2)
    (hc : ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) (UnitsCoeff (w.adicCompletion K)) 1).d 2 3).hom
      (((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) (UnitsCoeff (w.adicCompletion K)) 1).f 2).hom c) = 0) :
    Z2 (AbsoluteGaloisGroup (w.adicCompletion K)) (KummerCoeff (w.adicCompletion K) 2) :=
  cocyclesMap2 (AbsoluteGaloisGroup (w.adicCompletion K))
    (FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K)) (UnitsCoeff (w.adicCompletion K)) 1)
    (AbsoluteGaloisGroup (w.adicCompletion K)) (KummerCoeff (w.adicCompletion K) 2) (ContinuousMonoidHom.id _)
    (actualMuLevelEquiv (w.adicCompletion K) 1).toAddMonoidHom continuous_of_discreteTopology
    (actualMuLevelEquiv_smul (w.adicCompletion K) 1)
    ⟨fun p => cfun (((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) (UnitsCoeff (w.adicCompletion K)) 1).f 2).hom c) ![p.1, p.2],
      mem_Z2_of_d_eq_zero _ hc⟩

omit [B.IsElliptic] in
/-- The specific finite trace class is the class of that independently defined cocycle. -/
theorem traceSecondClass_cocycle (c : (actualTraceComplex (w.adicCompletion K)).X 2)
    (hc : ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) (UnitsCoeff (w.adicCompletion K)) 1).d 2 3).hom
      (((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) (UnitsCoeff (w.adicCompletion K)) 1).f 2).hom c) = 0) :
    firstTraceClass (w.adicCompletion K) c hc = H2pi _ _ (traceSecondZ2 K w c hc) := rfl

/-- The finite two-zero cup class is the actual coefficient-valued Weil evaluation at the prescribed rational torsion point. -/
theorem cup_two_zero_class
    (z : LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 2 3).hom)
    (a : (pointComplex (w.adicCompletion K) B).X 0)
    (t : AddSubgroup.torsionBy B.toAffine.Point 2)
    (ha : IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 (cfun a Fin.elim0)) = B.baseTorsionCoeff 2 t) :
    firstTraceClass (w.adicCompletion K) (cupTwoZero K w B z.val a) (cup_two_zero_first_cycle K w B z a t ha) =
      explicitCoeff2 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2)
        (B.weilPairingCoeff 2 (twoPower_isUnit (w.adicCompletion K) 1) t) continuous_of_discreteTopology (pointSecondClass K w B z) := by
  rw [traceSecondClass_cocycle, pointSecondClass_cocycle]
  erw [explicitCoeff2_mk]
  apply congrArg (H2pi (AbsoluteGaloisGroup (w.adicCompletion K)) (KummerCoeff (w.adicCompletion K) 2))
  apply Subtype.ext
  funext p
  obtain ⟨σ, τ⟩ := p
  have hcup : cfun (cupTwoZero K w B z.val a) ![σ, τ] =
      coefficientWeilPairing (w.adicCompletion K) B (cfun z.val ![σ, τ]) ((σ * τ) • cfun a Fin.elim0) := by
    change ZInQ.Manuscript.RC.SelmerComplex.cupFun (coefficientWeilPairing (w.adicCompletion K) B) 2 0 2 rfl
      (cfun z.val) (cfun a) ![σ, τ] = _
    exact cupFun_two_zero_apply _ _ _ _
  change actualMuLevelEquiv (w.adicCompletion K) 1
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) (UnitsCoeff (w.adicCompletion K)) 1
        (cfun (cupTwoZero K w B z.val a) ![σ, τ])) =
    B.weilPairingCoeff 2 (twoPower_isUnit (w.adicCompletion K) 1) t
      (IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1
        (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 (cfun z.val ![σ, τ])))
  rw [hcup, coefficientWeilPairing_projection, coefficientProjection_smul, pointLevelEquiv_smul,
    ha, B.smul_baseTorsionCoeff, B.weilPairingCoeff_apply]
  rfl

/-- The actual integral trace in bidegree two-zero has the genuine finite Milne invariant evaluation, including retained rational torsion. -/
theorem cup_two_zero_invariant
    (hthird : FiniteCycleLift.ThirdDegreeExact (w.adicCompletion K))
    (z : LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 2 3).hom)
    (a : (pointComplex (w.adicCompletion K) B).X 0)
    (t : AddSubgroup.torsionBy B.toAffine.Point 2)
    (ha : IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 (cfun a Fin.elim0)) = B.baseTorsionCoeff 2 t) :
    padicInvariant 1 (AllCochainTrace.trv (w.adicCompletion K) (cupTwoZero K w B z.val a)) =
      localH2TorsionValue B 2 (twoPower_isUnit (w.adicCompletion K) 1) (pointSecondClass K w B z) t := by
  have h := trv_normalized_on_finite_cycles (w.adicCompletion K) hthird (cupTwoZero K w B z.val a)
    (cup_two_zero_first_cycle K w B z a t ha)
  rw [cup_two_zero_class K w B z a t ha] at h
  have hi := congrArg (ZMod.toRatAddCircle 2) h
  rw [FiniteTrace.finiteInvariant_toRat] at hi
  exact hi

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.SecondCupCompatibility

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.CoordinateEvaluation

open Matrix
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual

variable {R S : Type} [CommRing R] [CommRing S]

/-- The standard basis dual has exactly the coordinate dot-product evaluation. -/
theorem vectorDual_value (r : ℕ) (v w : Fin r → R) : vectorDual r v w = dotProduct v w := by
  have hw : (∑ i : Fin r, w i • (Pi.single i 1 : Fin r → R)) = w := by
    funext j
    simp [Pi.single_apply]
  calc
    vectorDual r v w = ∑ i : Fin r, w i • vectorDual r v (Pi.single i 1) := by
      conv_lhs => rw [← hw]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact map_smul _ _ _
    _ = dotProduct v w := by
      simp only [vectorDual_basis, smul_eq_mul, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _

/-- The prescribed scalar projection commutes with the standard coordinate dual evaluation. -/
theorem vectorDual_reduction (π : R →+* S) (r : ℕ) (v w : Fin r → R) :
    π (vectorDual r v w) = vectorDual r (fun i => π (v i)) (fun i => π (w i)) := by
  rw [vectorDual_value, vectorDual_value]
  simp only [dotProduct, map_sum, map_mul]

/-- The actual finite matrix projection commutes with coordinate application. -/
theorem matrix_reduction {a b : Type} [Fintype b] (π : R →+* S) (M : Matrix a b R) (v : b → R) :
    M.map π *ᵥ (fun i => π (v i)) = fun i => π ((M *ᵥ v) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.CoordinateEvaluation

end

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.ComparisonEvaluation

open ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison
open CategoryTheory Matrix NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedBridge
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSelfDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualBasedComparison
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualModTwoResolution
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.CoordinateEvaluation

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]
  {c1 c2 : ℕ} (I : TwoTermConeBasedResolution K w B c1 c2)

/-- The actual degree-two Galois cochain realized from the fixed source coordinate vector. -/
def evenGamma (u : Fin c2 → ℤ_[2]) : (pointComplex (w.adicCompletion K) B).X 2 :=
  (I.realization.f 2 2 rfl (evenCoordinates I.differential u)).1

/-- The actual degree-one Galois cochain realized from the same finite source. -/
def oddGamma (u : Fin c1 → ℤ_[2]) : (pointComplex (w.adicCompletion K) B).X 1 :=
  (I.realization.f 1 1 rfl (oddCoordinates I.differential u)).1

/-- The realized even source cochain is an actual integral cocycle. -/
theorem evenGamma_cycle (u : Fin c2 → ℤ_[2]) :
    ((pointComplex (w.adicCompletion K) B).d 2 3).hom (evenGamma K w B I u) = 0 := by
  have h := I.realization.comm 2 3 2 3 rfl rfl rfl rfl (evenCoordinates I.differential u)
  have hs := FiniteSourceCoordinates.even_d_zero I.differential u
  rw [hs, map_zero] at h
  have hg := congrArg Prod.fst h.symm
  erw [ActualConeModels.cone_d_two] at hg
  exact hg

/-- The actual even cocycle carries its genuine continuous cycle witness. -/
def evenGammaCycle (u : Fin c2 → ℤ_[2]) : LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 2 3).hom :=
  ⟨evenGamma K w B I u, evenGamma_cycle K w B I u⟩

/-- The integral even comparison matrix evaluates by the actual two-zero trace-cup adjoint. -/
theorem evenMatrix_value (hM : MilneLocalDualityPrint) (u : Fin c2 → ℤ_[2])
    (r : Fin (actualLocalPresentation K w B).rankOne → ℤ_[2]) :
    vectorDual (actualLocalPresentation K w B).rankOne ((actualBasedMap K w B I hM).fE *ᵥ u) r =
      AllCochainTrace.trv (w.adicCompletion K) (SecondCupCompatibility.cupTwoZero K w B (evenGamma K w B I u) (localKummerZero K w B r)) := by
  have hm := BasedBridge.basedComparison_two I.differential (actualLocalPresentation K w B).f
    (ghomComp I.realization (localSelfDualComparison K w B hM)) u
  change (actualBasedMap K w B I hM).fE *ᵥ u = _ at hm
  rw [hm]
  change vectorDual (actualLocalPresentation K w B).rankOne
    ((vectorDual (actualLocalPresentation K w B).rankOne).symm
      (BasedBridge.comparisonTwo I.differential (actualLocalPresentation K w B).f
        (ghomComp I.realization (localSelfDualComparison K w B hM)) u)) r = _
  rw [LinearEquiv.apply_symm_apply]
  exact localSelfDualComparison_formula K w B hM 2 (I.realization.f 2 2 rfl (evenCoordinates I.differential u)) r

/-- The integral odd comparison matrix evaluates by the actual one-one trace-cup adjoint. -/
theorem oddMatrix_value (hM : MilneLocalDualityPrint) (u : Fin c1 → ℤ_[2])
    (r : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2]) :
    vectorDual (actualLocalPresentation K w B).rankZero ((actualBasedMap K w B I hM).fO *ᵥ u) r =
      AllCochainTrace.trv (w.adicCompletion K) (integralCupOne (w.adicCompletion K) B (oddGamma K w B I u) (localKummerOne K w B r).val) := by
  have hm := BasedBridge.basedComparison_one I.differential (actualLocalPresentation K w B).f
    (ghomComp I.realization (localSelfDualComparison K w B hM)) u
  change (actualBasedMap K w B I hM).fO *ᵥ u = _ at hm
  rw [hm]
  change vectorDual (actualLocalPresentation K w B).rankZero
    ((vectorDual (actualLocalPresentation K w B).rankZero).symm
      (BasedBridge.comparisonOne I.differential (actualLocalPresentation K w B).f
        (ghomComp I.realization (localSelfDualComparison K w B hM)) u)) r = _
  rw [LinearEquiv.apply_symm_apply]
  exact localSelfDualComparison_formula K w B hM 1 (I.realization.f 1 1 rfl (oddCoordinates I.differential u)) r

/-- The prescribed source projection commutes with its even coordinate inclusion. -/
theorem evenSource_projection (u : Fin c2 → ℤ_[2]) :
    (projectionHom PadicInt.toZMod (twoTermBased I.differential)).f 2 2 rfl (evenCoordinates I.differential u) =
      ArithmeticSourceModels.evenInclusion K w B I (fun i => PadicInt.toZMod (u i)) := by
  apply Subtype.ext
  funext i
  rcases i with i | i
  · rfl
  · exact map_zero PadicInt.toZMod

/-- The prescribed source projection commutes with its odd coordinate inclusion. -/
theorem oddSource_projection (u : Fin c1 → ℤ_[2]) :
    (projectionHom PadicInt.toZMod (twoTermBased I.differential)).f 1 1 rfl (oddCoordinates I.differential u) =
      ArithmeticSourceModels.oddInclusion K w B I (fun i => PadicInt.toZMod (u i)) := by
  apply Subtype.ext
  funext i
  rcases i with i | i
  · exact map_zero PadicInt.toZMod
  · rfl

/-- The prescribed quotient-cone projection carries the even realized Galois cochain to the same finite source realization. -/
theorem evenGamma_projection (u : Fin c2 → ℤ_[2]) :
    ((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).f 2).hom (evenGamma K w B I u) =
      ((reducedRealization K w B I).f 2 2 rfl
        (ArithmeticSourceModels.evenInclusion K w B I (fun i => PadicInt.toZMod (u i)))).1 := by
  have h := reducedRealization_square K w B I 2 2 rfl (evenCoordinates I.differential u)
  rw [evenSource_projection] at h
  exact congrArg Prod.fst h

/-- The same prescribed projection square on degree-one Galois cochains. -/
theorem oddGamma_projection (u : Fin c1 → ℤ_[2]) :
    ((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).f 1).hom (oddGamma K w B I u) =
      ((reducedRealization K w B I).f 1 1 rfl
        (ArithmeticSourceModels.oddInclusion K w B I (fun i => PadicInt.toZMod (u i)))).1 := by
  have h := reducedRealization_square K w B I 1 1 rfl (oddCoordinates I.differential u)
  rw [oddSource_projection] at h
  exact congrArg Prod.fst h

/-- The actual even source cohomology model reads the prescribed finite Galois class of every integral vector lift. -/
theorem evenModel_value (x : cyclesE (ArithmeticSourceModels.source K w B I))
    (u : Fin c2 → ℤ_[2]) (hu : (fun i => PadicInt.toZMod (u i)) = x.val) :
    (ArithmeticSourceModels.model K w B I).classE x =
      SecondCupCompatibility.pointSecondClass K w B (evenGammaCycle K w B I u) := by
  have h := evenGamma_projection K w B I u
  rw [hu] at h
  change FiniteConeModels.gammaClassTwo K w B
      (FiniteConeModels.cycleTwoProjection K w B (ArithmeticSourceModels.evenConeCycle K w B I x)) =
    FiniteConeModels.gammaClassTwo K w B
      (reduceTwoCycle (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 (evenGammaCycle K w B I u))
  apply congrArg (FiniteConeModels.gammaClassTwo K w B)
  apply Subtype.ext
  exact h.symm

/-- Every prescribed lift of an odd reduced source cycle is a cycle under the actual finite coefficient projection. -/
theorem oddGamma_first_cycle (x : cyclesO (ArithmeticSourceModels.source K w B I))
    (u : Fin c1 → ℤ_[2]) (hu : (fun i => PadicInt.toZMod (u i)) = x.val) :
    ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).f 1).hom (oddGamma K w B I u)) = 0 := by
  have h := oddGamma_projection K w B I u
  rw [hu] at h
  rw [h]
  exact (FiniteConeModels.cycleOneProjection K w B (ArithmeticSourceModels.oddConeCycle K w B I x)).property

/-- The actual odd cohomology model reads the genuine finite Kummer-quotient class of that very lift. -/
theorem oddModel_value (x : cyclesO (ArithmeticSourceModels.source K w B I))
    (u : Fin c1 → ℤ_[2]) (hu : (fun i => PadicInt.toZMod (u i)) = x.val) :
    (ArithmeticSourceModels.model K w B I).classO x =
      QuotientAddGroup.mk (FiniteCupCompatibility.firstPointClass (w.adicCompletion K) B
        (oddGamma K w B I u) (oddGamma_first_cycle K w B I x u hu)) := by
  have h := oddGamma_projection K w B I u
  rw [hu] at h
  change QuotientAddGroup.mk (FiniteConeModels.gammaClassOne K w B
      (FiniteConeModels.cycleOneProjection K w B (ArithmeticSourceModels.oddConeCycle K w B I x))) =
    QuotientAddGroup.mk (FiniteConeModels.gammaClassOne K w B
      (FiniteCupCompatibility.firstPointCycle (w.adicCompletion K) B (oddGamma K w B I u)
        (oddGamma_first_cycle K w B I x u hu)))
  apply congrArg QuotientAddGroup.mk
  apply congrArg (FiniteConeModels.gammaClassOne K w B)
  apply Subtype.ext
  exact h.symm

/-- The finite-only class map agrees with the original fixed reduction on every actual integral one-cycle. -/
theorem firstPointClass_integral_cycle
    (d : LinearMap.ker ((pointComplex (w.adicCompletion K) B).d 1 2).hom)
    (hd : ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 1 2).hom
      (((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).f 1).hom d.val) = 0) :
    FiniteCupCompatibility.firstPointClass (w.adicCompletion K) B d.val hd = pointH1Reduction (w.adicCompletion K) B 1 d := rfl

/-- Every prescribed finite coordinate vector has an actual integral coordinate lift. -/
theorem vector_lift (r : ℕ) (v : Fin r → ZMod 2) : ∃ u : Fin r → ℤ_[2], (fun i => PadicInt.toZMod (u i)) = v :=
  ModTwoComplexes.vectorProjection_surjective r v

/-- The actual retained-torsion coordinate class has a lift with the specified genuine rational coefficient value. -/
theorem zero_coordinate_lift (r : LinearMap.ker (pointDifferentialModTwo K w B)) :
    ∃ u : Fin (actualLocalPresentation K w B).rankOne → ℤ_[2],
      (fun i => PadicInt.toZMod (u i)) = r.val ∧
      IntegralPairing.pointLevelEquiv (w.adicCompletion K) B 1
        (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1
          (ZInQ.Manuscript.RC.CoefModules.cfun (localKummerZero K w B u) Fin.elim0)) =
        B.baseTorsionCoeff 2 (ArithmeticTarget.zeroLinearEquiv K w B r) := by
  obtain ⟨u, y, huy, hu⟩ := FiniteConditionH0.lift_zero_cycle K w B (ArithmeticTarget.kernelToConditionCycle K w B r)
  refine ⟨u, hu, ?_⟩
  have hzero := ArithmeticTarget.zeroLinearEquiv_relation K w B r u y huy hu
  rw [hzero]
  exact RetainedTorsionNaturality.degreeZeroReductionNaturality_proof K w B u y huy

/-- The odd Milne comparison is evaluated on the actual coordinate Kummer class, not an existential point witness. -/
theorem alphaOdd_kappa_value (hM : MilneLocalDualityPrint)
    (y : H1 (AbsoluteGaloisGroup (w.adicCompletion K)) (B.TorsionCoeff 2))
    (r : Fin (actualLocalPresentation K w B).rankZero → ZMod 2) :
    ZMod.toRatAddCircle 2 (ArithmeticComparisons.alphaOdd K w B hM (QuotientAddGroup.mk y) (Submodule.Quotient.mk r)) =
      ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 (twoPower_isUnit (w.adicCompletion K) 1)
        (ArithmeticTarget.kappaLinear K w B r) y := by
  have hvalue : ∀ q : TateDualityData.pointMod (P := B.toAffine.Point) 2,
      ZMod.toRatAddCircle 2 (ArithmeticComparisons.milneOdd K w B hM (QuotientAddGroup.mk y) q) =
        ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 (twoPower_isUnit (w.adicCompletion K) 1)
          (ArithmeticTarget.deltaLinear K w B q) y := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H p => exact ArithmeticComparisons.milneOdd_value K w B hM y p
  change ZMod.toRatAddCircle 2 (ArithmeticComparisons.milneOdd K w B hM (QuotientAddGroup.mk y)
    (ArithmeticTarget.oneLinearEquiv K w B (Submodule.Quotient.mk r))) = _
  rw [hvalue, ArithmeticTarget.oneLinearEquiv_kummer]

/-- The prescribed lift of a point-generator vector has exactly the fixed coordinate Kummer class. -/
theorem point_coordinate_kummer_lift
    (r : Fin (actualLocalPresentation K w B).rankZero → ZMod 2)
    (u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2])
    (hu : (fun i => PadicInt.toZMod (u i)) = r) :
    pointH1Reduction (w.adicCompletion K) B 1 (localKummerOne K w B u) = ArithmeticTarget.kappaLinear K w B r := by
  have h := FiniteConditionH1.classMapOne_lift K w B u
  change ArithmeticTarget.kappaLinear K w B (fun i => PadicInt.toZMod (u i)) = _ at h
  rw [hu] at h
  exact h.symm

/-- The even arithmetic model square for the specific actual trace-adjoint matrix comparison. -/
theorem commE (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hthird : FiniteCycleLift.ThirdDegreeExact (w.adicCompletion K))
    (x : cyclesE (ArithmeticSourceModels.source K w B I)) :
    (ArithmeticTargetModels.model K w B).classE
        (cycleMapE ((actualBasedMap K w B I hM).map PadicInt.toZMod) x) =
      (ArithmeticComparisons.alphaEven K w B hF).toLinearMap ((ArithmeticSourceModels.model K w B I).classE x) := by
  apply LinearMap.ext
  intro r
  apply ZMod.toRatAddCircle_injective 2
  obtain ⟨u, hu⟩ := ModTwoComplexes.vectorProjection_surjective c2 x.val
  change (fun i => PadicInt.toZMod (u i)) = x.val at hu
  obtain ⟨v, hv, ha⟩ := zero_coordinate_lift K w B r
  let f := actualBasedMap K w B I hM
  have hm : (f.map PadicInt.toZMod).fE *ᵥ x.val = fun i => PadicInt.toZMod ((f.fE *ᵥ u) i) := by
    change f.fE.map PadicInt.toZMod *ᵥ x.val = _
    rw [← hu, CoordinateEvaluation.matrix_reduction]
  have hp : vectorDual (actualLocalPresentation K w B).rankOne ((f.map PadicInt.toZMod).fE *ᵥ x.val) r.val =
      PadicInt.toZMod (vectorDual (actualLocalPresentation K w B).rankOne (f.fE *ᵥ u) v) := by
    rw [hm, ← hv]
    exact (CoordinateEvaluation.vectorDual_reduction PadicInt.toZMod _ _ _).symm
  calc
    ZMod.toRatAddCircle 2 ((ArithmeticTargetModels.model K w B).classE
        (cycleMapE (f.map PadicInt.toZMod) x) r) =
      ZMod.toRatAddCircle 2 (vectorDual (actualLocalPresentation K w B).rankOne
        ((f.map PadicInt.toZMod).fE *ᵥ x.val) r.val) := by
          rw [ArithmeticTargetModels.classE_value]
          rfl
    _ = ZMod.toRatAddCircle 2 (PadicInt.toZMod
        (vectorDual (actualLocalPresentation K w B).rankOne (f.fE *ᵥ u) v)) := congrArg (ZMod.toRatAddCircle 2) hp
    _ = padicInvariant 1 (AllCochainTrace.trv (w.adicCompletion K)
        (SecondCupCompatibility.cupTwoZero K w B (evenGamma K w B I u) (localKummerZero K w B v))) := by
          rw [evenMatrix_value K w B I hM u v, ← SecondCupCompatibility.first_residue_eq]
          rfl
    _ = localH2TorsionValue B 2 (twoPower_isUnit (w.adicCompletion K) 1)
        (SecondCupCompatibility.pointSecondClass K w B (evenGammaCycle K w B I u))
        (ArithmeticTarget.zeroLinearEquiv K w B r) :=
      SecondCupCompatibility.cup_two_zero_invariant K w B hthird (evenGammaCycle K w B I u)
        (localKummerZero K w B v) (ArithmeticTarget.zeroLinearEquiv K w B r) ha
    _ = ZMod.toRatAddCircle 2 (ArithmeticComparisons.alphaEven K w B hF
        ((ArithmeticSourceModels.model K w B I).classE x) r) := by
      rw [evenModel_value K w B I x u hu]
      exact (ArithmeticComparisons.alphaEven_value K w B hF _ r).symm

/-- The odd arithmetic model square for the same specific actual matrix comparison, with its genuine finite Kummer evaluation. -/
theorem commO (hM : MilneLocalDualityPrint)
    (hthird : FiniteCycleLift.ThirdDegreeExact (w.adicCompletion K))
    (x : cyclesO (ArithmeticSourceModels.source K w B I)) :
    (ArithmeticTargetModels.model K w B).classO
        (cycleMapO ((actualBasedMap K w B I hM).map PadicInt.toZMod) x) =
      (ArithmeticComparisons.alphaOdd K w B hM).toLinearMap ((ArithmeticSourceModels.model K w B I).classO x) := by
  apply LinearMap.ext
  intro r
  induction r using Submodule.Quotient.induction_on with
  | H r =>
    apply ZMod.toRatAddCircle_injective 2
    obtain ⟨u, hu⟩ := ModTwoComplexes.vectorProjection_surjective c1 x.val
    change (fun i => PadicInt.toZMod (u i)) = x.val at hu
    obtain ⟨v, hv⟩ := ModTwoComplexes.vectorProjection_surjective (actualLocalPresentation K w B).rankZero r
    change (fun i => PadicInt.toZMod (v i)) = r at hv
    let f := actualBasedMap K w B I hM
    let c := oddGamma K w B I u
    let hc := oddGamma_first_cycle K w B I x u hu
    let d := localKummerOne K w B v
    have hd : ((finiteIntegralComplex (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).d 1 2).hom
        (((reduceCochains (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1).f 1).hom d.val) = 0 :=
      (reduceOneCycle (AbsoluteGaloisGroup (w.adicCompletion K)) B.PointCoeff 1 d).property
    have hm : (f.map PadicInt.toZMod).fO *ᵥ x.val = fun i => PadicInt.toZMod ((f.fO *ᵥ u) i) := by
      change f.fO.map PadicInt.toZMod *ᵥ x.val = _
      rw [← hu, CoordinateEvaluation.matrix_reduction]
    have hp : vectorDual (actualLocalPresentation K w B).rankZero ((f.map PadicInt.toZMod).fO *ᵥ x.val) r =
        PadicInt.toZMod (vectorDual (actualLocalPresentation K w B).rankZero (f.fO *ᵥ u) v) := by
      rw [hm, ← hv]
      exact (CoordinateEvaluation.vectorDual_reduction PadicInt.toZMod _ _ _).symm
    have hcup := FiniteCupCompatibility.cup_invariant_compatibility_finite_cycles (w.adicCompletion K) B hthird c d.val hc hd
    rw [firstPointClass_integral_cycle K w B d hd, point_coordinate_kummer_lift K w B r v hv] at hcup
    calc
      ZMod.toRatAddCircle 2 ((ArithmeticTargetModels.model K w B).classO
          (cycleMapO (f.map PadicInt.toZMod) x) (Submodule.Quotient.mk r)) =
        ZMod.toRatAddCircle 2 (vectorDual (actualLocalPresentation K w B).rankZero
          ((f.map PadicInt.toZMod).fO *ᵥ x.val) r) := by
            rw [ArithmeticTargetModels.classO_value]
            rfl
      _ = ZMod.toRatAddCircle 2 (PadicInt.toZMod
          (vectorDual (actualLocalPresentation K w B).rankZero (f.fO *ᵥ u) v)) := congrArg (ZMod.toRatAddCircle 2) hp
      _ = padicInvariant 1 (AllCochainTrace.trv (w.adicCompletion K)
          (integralCupOne (w.adicCompletion K) B c d.val)) := by
            rw [oddMatrix_value K w B I hM u v, ← SecondCupCompatibility.first_residue_eq]
            rfl
      _ = ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 (twoPower_isUnit (w.adicCompletion K) 1)
          (FiniteCupCompatibility.firstPointClass (w.adicCompletion K) B c hc) (ArithmeticTarget.kappaLinear K w B r) := hcup
      _ = ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 (twoPower_isUnit (w.adicCompletion K) 1)
          (ArithmeticTarget.kappaLinear K w B r) (FiniteCupCompatibility.firstPointClass (w.adicCompletion K) B c hc) :=
        FiniteCupSymmetry.localTatePairing_symmetric (w.adicCompletion K) B 2 (twoPower_isUnit (w.adicCompletion K) 1) _ _
      _ = ZMod.toRatAddCircle 2 (ArithmeticComparisons.alphaOdd K w B hM
          (QuotientAddGroup.mk (FiniteCupCompatibility.firstPointClass (w.adicCompletion K) B c hc)) (Submodule.Quotient.mk r)) :=
        (alphaOdd_kappa_value K w B hM _ r).symm
      _ = ZMod.toRatAddCircle 2 (ArithmeticComparisons.alphaOdd K w B hM
          ((ArithmeticSourceModels.model K w B I).classO x) (Submodule.Quotient.mk r)) := by
        rw [oddModel_value K w B I x u hu]

/-- The actual hred-free integral comparison contraction follows from its genuine source resolution, the actual finite arithmetic model maps and trace support. -/
theorem contraction_of_actual_models
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hthird : FiniteCycleLift.ThirdDegreeExact (w.adicCompletion K)) :
    Nonempty (Contraction (BasedCx.coneR (actualBasedMap K w B I hM))) :=
  ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.nakayama_comparison_of_modTwo_models
    (actualBasedMap K w B I hM) (ArithmeticSourceModels.model K w B I) (ArithmeticTargetModels.model K w B)
    (ArithmeticComparisons.alphaEven K w B hF).toLinearMap (ArithmeticComparisons.alphaOdd K w B hM).toLinearMap
    (ArithmeticComparisons.alphaEven_bijective K w B hF) (ArithmeticComparisons.alphaOdd_bijective K w B hM)
    (commE K w B I hM hF hthird) (commO K w B I hM hthird)

/-- The constructed genuine completion source gives the integral comparison contraction from the explicitly cited finite Milne inputs, with no hred premise. -/
theorem contraction_of_print
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint) :
    Nonempty (Contraction (BasedCx.coneR (actualBasedMap K w B
      (FiniteLocalDegreeBound.basedResolution_of_print hM hF hH K w B) hM))) :=
  contraction_of_actual_models K w B (FiniteLocalDegreeBound.basedResolution_of_print hM hF hH K w B)
    hM hF (FiniteLocalDegreeBound.actualThirdDegreeExact_of_print hH (w.adicCompletion K))

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.ComparisonEvaluation

end
