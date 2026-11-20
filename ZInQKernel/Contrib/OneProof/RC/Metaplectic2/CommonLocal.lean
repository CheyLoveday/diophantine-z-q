import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.SignedRelations
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.CentralCover
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.IntegralAction
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.TensorComparison

/-! A single local cover for the two literal actions, with central sign
and a common good-prime section. Pullback and splitting are on-the-spot
(c), tex 8788–8807 and 8944–8946. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex Visibility
open scoped MatrixGroups

variable (p : Place)

abbrev OperatorPair := (LocalEnd p)ˣ × (LocalEnd p)ˣ

def diagonalScalar : ℂˣ →* OperatorPair p :=
  (scalarOp (A := LocalEnd p)).prod (scalarOp (A := LocalEnd p))

theorem diagonalScalar_central (z : ℂˣ) (g : OperatorPair p) :
    Commute (diagonalScalar p z) g := by
  exact Prod.ext (scalarOp_comm (A := LocalEnd p) z g.1)
    (scalarOp_comm (A := LocalEnd p) z g.2)

def negativeOperator : (LocalEnd p)ˣ := scalarOp (A := LocalEnd p) (-1 : ℂˣ)

theorem negativeOperator_apply (f : SchwartzBruhat p) :
    (negativeOperator p : LocalEnd p) f = -f := by
  rw [negativeOperator, coe_scalarOp, Algebra.algebraMap_eq_smul_one]
  simp

theorem negativeOperator_not_fixed :
    (negativeOperator p : LocalEnd p) (spherical p) ≠ spherical p := by
  intro h
  rw [negativeOperator_apply] at h
  have e := congrArg (fun f : SchwartzBruhat p => f.1 (0 : LocalVectors p)) h
  change -(spherical p).1 0 = (spherical p).1 0 at e
  rw [spherical_apply, if_pos (by simp [localLattice])] at e
  norm_num at e

theorem negativeOperator_ne_one : negativeOperator p ≠ 1 := by
  intro e
  exact negativeOperator_not_fixed p
    (congrArg (fun T : (LocalEnd p)ˣ => (T : LocalEnd p) (spherical p)) e)

private theorem diagonalSign_square : diagonalScalar p (-1) * diagonalScalar p (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

def diagonalSign : Subgroup (OperatorPair p) where
  carrier := {g | g = 1 ∨ g = diagonalScalar p (-1)}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul _)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (diagonalSign_square p)
  inv_mem' := by
    rintro x (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right (diagonalSign_square p))

private theorem diagonalSign_central (z : diagonalSign p) (g : OperatorPair p) :
    Commute (z : OperatorPair p) g := by
  rcases z.property with h | h
  · rw [h]; exact Commute.one_left g
  · rw [h]; exact diagonalScalar_central p _ _

instance diagonalSign_normal : (diagonalSign p).Normal where
  conj_mem z hz g := by
    rw [← (diagonalSign_central p ⟨z, hz⟩ g).eq, mul_assoc, mul_inv_cancel, mul_one]
    exact hz

abbrev pairProject := QuotientGroup.mk' (diagonalSign p)

private theorem pairProject_eq {X Y : OperatorPair p} {z : ℂˣ}
    (hz : z = 1 ∨ z = -1)
    (h₁ : (X.1 : LocalEnd p) = (z : ℂ) • (Y.1 : LocalEnd p))
    (h₂ : (X.2 : LocalEnd p) = (z : ℂ) • (Y.2 : LocalEnd p)) :
    pairProject p X = pairProject p Y := by
  have e : X = diagonalScalar p z * Y := by
    apply Prod.ext
    · apply Units.ext
      change (X.1 : LocalEnd p) = ((scalarOp (A := LocalEnd p) z * Y.1) : (LocalEnd p)ˣ).val
      rw [coe_scalarOp_mul]
      exact h₁
    · apply Units.ext
      change (X.2 : LocalEnd p) = ((scalarOp (A := LocalEnd p) z * Y.2) : (LocalEnd p)ˣ).val
      rw [coe_scalarOp_mul]
      exact h₂
  have hmem : diagonalScalar p z ∈ diagonalSign p := by
    rcases hz with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr rfl
  have hm : pairProject p (diagonalScalar p z) = 1 := (QuotientGroup.eq_one_iff _).2 hmem
  rw [e, map_mul, hm, one_mul]

variable (a b : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)] [∀ i, NeZero (2 * b i)]

def pairUpper (x : ℚ_[p.val]) : OperatorPair p := (upperUnit p a x, upperUnit p b x)
def pairDiagonal (t : ℚ_[p.val]ˣ) : OperatorPair p := (diagonalUnit p a t, diagonalUnit p b t)
def pairWeyl : OperatorPair p := (weylUnit p a, weylUnit p b)

private theorem pairRelations :
    NormalForm.Relations (fun x => pairProject p (pairUpper p a b x))
      (fun t => pairProject p (pairDiagonal p a b t)) (pairProject p (pairWeyl p a b)) where
  upper_zero := by
    rw [← map_one (pairProject p)]
    congr 1
    exact Prod.ext (Units.ext (upper_zero a p)) (Units.ext (upper_zero b p))
  diagonal_one := by
    rw [← map_one (pairProject p)]
    congr 1
    apply Prod.ext <;> apply Units.ext <;> simp [pairDiagonal, diagonal_one]
  upper_add x y := by
    rw [← map_mul]
    congr 1
    exact Prod.ext (Units.ext (upper_mul a p x y)) (Units.ext (upper_mul b p x y))
  diagonal_mul s t := by
    rw [← map_mul]
    apply pairProject_eq p (hilbertSign_cases p s t)
    all_goals
      simp only [pairDiagonal, Prod.fst_mul, Prod.snd_mul, Units.val_mul, coe_diagonalUnit]
      rw [diagonal_mul, diagonal_defect_sign]
  diagonal_upper t x := by
    simp only [← map_mul]
    congr 1
    apply Prod.ext <;> apply Units.ext <;>
      simpa only [pairUpper, pairDiagonal, Prod.fst_mul, Prod.snd_mul, Units.val_mul,
        coe_diagonalUnit, coe_upperUnit] using diagonal_upper _ p t x
  weyl_diagonal t := by
    simp only [← map_mul]
    congr 1
    apply Prod.ext <;> apply Units.ext <;>
      simpa only [pairDiagonal, pairWeyl, Prod.fst_mul, Prod.snd_mul, Units.val_mul,
        coe_diagonalUnit, coe_weylUnit] using weyl_diagonal _ p t
  weyl_square := by
    rw [← map_mul]
    apply pairProject_eq p (hilbertSign_cases p (-1) (-1))
    all_goals
      simp only [pairWeyl, pairDiagonal, Prod.fst_mul, Prod.snd_mul, Units.val_mul,
        coe_weylUnit, coe_diagonalUnit]
      rw [weyl_square_scalar, ← Units.val_pow_eq_pow_val, ← Units.val_div_eq_div_val,
        weyl_square_defect_sign]
  weyl_upper x := by
    simp only [← map_mul]
    apply pairProject_eq p (hilbertSign_cases p (-x) (-1))
    all_goals
      simp only [pairUpper, pairDiagonal, pairWeyl, Prod.fst_mul, Prod.snd_mul, Units.val_mul,
        coe_upperUnit, coe_diagonalUnit, coe_weylUnit]
      rw [weyl_upper_bruhat, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
        ← Units.val_div_eq_div_val, weyl_upper_defect_sign]

def pairProjective : SL(2, ℚ_[p.val]) →* OperatorPair p ⧸ diagonalSign p :=
  (NormalForm.representation_of_relations (pairRelations p a b)).choose

theorem pairProjective_generators :
    (∀ x, pairProjective p a b (upperMatrix x) = pairProject p (pairUpper p a b x)) ∧
    (∀ t, pairProjective p a b (diagonalMatrix t) = pairProject p (pairDiagonal p a b t)) ∧
    pairProjective p a b weylMatrix = pairProject p (pairWeyl p a b) :=
  (NormalForm.representation_of_relations (pairRelations p a b)).choose_spec

abbrev LocalCommon := Cover (diagonalSign p) (pairProjective p a b)
abbrev localProjection := coverProjection (diagonalSign p) (pairProjective p a b)
abbrev localOperators := coverOperator (diagonalSign p) (pairProjective p a b)

def localFirst : LocalCommon p a b →* (LocalEnd p)ˣ :=
  (MonoidHom.fst _ _).comp (localOperators p a b)

def localSecond : LocalCommon p a b →* (LocalEnd p)ˣ :=
  (MonoidHom.snd _ _).comp (localOperators p a b)

def liftUpper (x : ℚ_[p.val]) : LocalCommon p a b :=
  coverLift _ _ _ _ ((pairProjective_generators p a b).1 x)

def liftDiagonal (t : ℚ_[p.val]ˣ) : LocalCommon p a b :=
  coverLift _ _ _ _ ((pairProjective_generators p a b).2.1 t)

def liftWeyl : LocalCommon p a b :=
  coverLift _ _ _ _ (pairProjective_generators p a b).2.2

def localSign : LocalCommon p a b :=
  coverKernelElement _ _ ⟨diagonalScalar p (-1), Or.inr rfl⟩

theorem localSign_central (g : LocalCommon p a b) : Commute (localSign p a b) g :=
  cover_kernel_central _ _ _ (diagonalScalar_central p (-1)) g

theorem localSign_square : localSign p a b * localSign p a b = 1 :=
  Subtype.ext (Prod.ext (one_mul _) (diagonalSign_square p))

theorem localProjection_kernel :
    localSign p a b ≠ 1 ∧
      ∀ g, localProjection p a b g = 1 ↔ g = 1 ∨ g = localSign p a b := by
  apply cover_kernel_pair
  · intro e
    exact negativeOperator_ne_one p (congrArg Prod.fst e)
  · intro g
    rcases g.property with h | h
    · exact Or.inl h
    · exact Or.inr (Subtype.ext h)

theorem localProjection_surjective : Function.Surjective (localProjection p a b) :=
  coverProjection_surjective _ _

#print axioms diagonalScalar_central
#print axioms negativeOperator_apply
#print axioms negativeOperator_not_fixed
#print axioms negativeOperator_ne_one
#print axioms diagonalSign_square
#print axioms diagonalSign_central
#print axioms pairProject_eq
#print axioms pairRelations
#print axioms pairProjective_generators
#print axioms localSign_central
#print axioms localSign_square
#print axioms localProjection_kernel
#print axioms localProjection_surjective

end ZInQ.Manuscript.RC.Metaplectic2
