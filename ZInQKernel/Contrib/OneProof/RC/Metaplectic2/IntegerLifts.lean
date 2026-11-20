import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.CentralTensor

/-! Integer pullback of the common finite cover, with the literal inverse
generators (tex 8991–9004). The pullback is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex OldStageLaw Filter
open scoped MatrixGroups

private theorem int_in_range (g : SL(2, ℤ)) (p : Place) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ_[p.val]) g ∈ (includeIntegral p).range := by
  refine ⟨Matrix.SpecialLinearGroup.map (Int.castRingHom ℤ_[p.val]) g, ?_⟩
  apply Subtype.ext
  rw [includeIntegral, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  simp [RingHom.mapMatrix_apply]

def integerDiagonal : SL(2, ℤ) →* FiniteSL where
  toFun g := ⟨fun p => Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ_[p.val]) g,
    .of_forall (int_in_range g)⟩
  map_one' := by apply RestrictedProduct.ext; intro p; exact map_one (Matrix.SpecialLinearGroup.map _)
  map_mul' g h := by apply RestrictedProduct.ext; intro p; exact map_mul (Matrix.SpecialLinearGroup.map _) g h

private theorem step_inverse_trans (n : ℤ) :
    (Step.trans n).matrix⁻¹ = upperMatrix (-n) := by
  apply Subtype.ext
  rw [Step.matrix, ← zpow_neg, ModularGroup.coe_T_zpow]
  rfl

private theorem step_inverse_weyl : Step.inv.matrix⁻¹ = weylMatrix := by decide

variable (a b : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)] [∀ i, NeZero (2 * b i)]

abbrev IntegerCommon :=
  (integerDiagonal.comp (MonoidHom.fst (SL(2, ℤ)) (FiniteCommon a b))).eqLocus
    ((commonProjection a b).comp (MonoidHom.snd _ _))

def integerProjection : IntegerCommon a b →* SL(2, ℤ) :=
  (MonoidHom.fst _ _).comp (IntegerCommon a b).subtype

def integerLiftFinite : IntegerCommon a b →* FiniteCommon a b :=
  (MonoidHom.snd _ _).comp (IntegerCommon a b).subtype

theorem integerProjection_surjective : Function.Surjective (integerProjection a b) := by
  intro g
  obtain ⟨x, hx⟩ := commonProjection_surjective a b (integerDiagonal g)
  exact ⟨⟨(g, x), hx.symm⟩, rfl⟩

def integerSign : IntegerCommon a b :=
  ⟨(1, finiteSign a b), (map_one integerDiagonal).trans
    (((commonProjection_kernel a b).2 _).2 (Or.inr rfl)).symm⟩

theorem integerSign_central (g : IntegerCommon a b) : Commute (integerSign a b) g := by
  apply Subtype.ext
  exact Prod.ext ((Commute.one_left g.1.1).eq) ((finiteSign_central a b g.1.2).eq)

theorem integerProjection_kernel :
    integerSign a b ≠ 1 ∧
      ∀ g, integerProjection a b g = 1 ↔ g = 1 ∨ g = integerSign a b := by
  refine ⟨fun h => (commonProjection_kernel a b).1 (congrArg (integerLiftFinite a b) h),
    fun g => ⟨?_, ?_⟩⟩
  · intro h
    change g.1.1 = 1 at h
    have hg : commonProjection a b g.1.2 = 1 := by
      have e : integerDiagonal g.1.1 = commonProjection a b g.1.2 := g.2
      rw [h, map_one] at e
      exact e.symm
    rcases ((commonProjection_kernel a b).2 _).mp hg with h' | h'
    · exact Or.inl (Subtype.ext (Prod.ext h h'))
    · exact Or.inr (Subtype.ext (Prod.ext h h'))
  · rintro (rfl | rfl) <;> rfl

def integerFirst : IntegerCommon a b →* Module.End ℂ RestrictedTensor :=
  (commonFirst a b).comp (integerLiftFinite a b)

def integerSecond : IntegerCommon a b →* Module.End ℂ RestrictedTensor :=
  (commonSecond a b).comp (integerLiftFinite a b)

theorem integerSign_actions :
    integerFirst a b (integerSign a b) = -(1 : Module.End ℂ RestrictedTensor) ∧
    integerSecond a b (integerSign a b) = -(1 : Module.End ℂ RestrictedTensor) :=
  ⟨commonFirst_sign a b, commonSecond_sign a b⟩

private def restrictedLiftStep : Step → FiniteLocalCover a b
  | .inv => ⟨fun p => liftWeyl p a b, by
      filter_upwards [eventually_good a b] with p h
      change liftWeyl p a b ∈ sectionSubgroup a b p
      rw [sectionSubgroup, dite_eq_left h]
      exact ⟨weylMatrix, commonSection_weyl a b p h⟩⟩
  | .trans n => ⟨fun p => liftUpper p a b (-(n : ℚ_[p.val])), by
      filter_upwards [eventually_good a b] with p h
      change liftUpper p a b _ ∈ sectionSubgroup a b p
      rw [sectionSubgroup, dite_eq_left h]
      refine ⟨upperMatrix (-(n : ℤ_[p.val])), ?_⟩
      rw [commonSection_upper]
      congr 1⟩

private theorem restrictedLiftStep_projection (s : Step) :
    finiteProjection a b (restrictedLiftStep a b s) = integerDiagonal s.matrix⁻¹ := by
  apply RestrictedProduct.ext
  intro p
  cases s with
  | inv =>
    change weylMatrix = Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ_[p.val]) Step.inv.matrix⁻¹
    rw [step_inverse_weyl, map_weylMatrix]
  | trans n =>
    change upperMatrix (-(n : ℚ_[p.val])) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ_[p.val]) (Step.trans n).matrix⁻¹
    rw [step_inverse_trans, map_upperMatrix]
    simp

/-- One inverse lift per manuscript step, used on both finite tensors. -/
def integerLiftStep (s : Step) : IntegerCommon a b :=
  ⟨(s.matrix⁻¹, finiteQuotient a b (restrictedLiftStep a b s)),
    (restrictedLiftStep_projection a b s).symm⟩

theorem integerLiftStep_projection (s : Step) :
    integerProjection a b (integerLiftStep a b s) = s.matrix⁻¹ := rfl

theorem integerLiftStep_first (s : Step) :
    integerFirst a b (integerLiftStep a b s) = restrictedAction (forgetUnits (operatorStep a s)) := by
  change firstTensorAction a b (restrictedLiftStep a b s) = _
  change restrictedAction (forgetUnits (firstTuple a b (restrictedLiftStep a b s))) = _
  congr 2
  cases s <;> (apply RestrictedProduct.ext; intro p; rfl)

theorem integerLiftStep_second (s : Step) :
    integerSecond a b (integerLiftStep a b s) = restrictedAction (forgetUnits (operatorStep b s)) := by
  change secondTensorAction a b (restrictedLiftStep a b s) = _
  change restrictedAction (forgetUnits (secondTuple a b (restrictedLiftStep a b s))) = _
  congr 2
  cases s <;> (apply RestrictedProduct.ext; intro p; rfl)

theorem common_first_generatorTensorAction :
    GeneratorTensorAction (gridTensor a) evaluate (integerFirst a b)
      (integerLiftStep a b) (fun p => gaussIndex a p) := by
  have h := restricted_generatorTensorAction a
  exact ⟨fun n r x => by rw [integerLiftStep_first]; exact h.1 n r x,
    fun r y => by rw [integerLiftStep_first]; exact h.2 r y⟩

theorem common_second_generatorTensorAction :
    GeneratorTensorAction (gridTensor b) evaluate (integerSecond a b)
      (integerLiftStep a b) (fun p => gaussIndex b p) := by
  have h := restricted_generatorTensorAction b
  exact ⟨fun n r x => by rw [integerLiftStep_second]; exact h.1 n r x,
    fun r y => by rw [integerLiftStep_second]; exact h.2 r y⟩

#print axioms int_in_range
#print axioms step_inverse_trans
#print axioms step_inverse_weyl
#print axioms integerProjection_surjective
#print axioms integerSign_central
#print axioms integerProjection_kernel
#print axioms integerSign_actions
#print axioms restrictedLiftStep_projection
#print axioms integerLiftStep_projection
#print axioms integerLiftStep_first
#print axioms integerLiftStep_second
#print axioms common_first_generatorTensorAction
#print axioms common_second_generatorTensorAction

end ZInQ.Manuscript.RC.Metaplectic2
