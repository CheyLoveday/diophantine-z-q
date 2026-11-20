import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.CommonLocal

/-! The two spherical actions give the same lift of the integral group.
Agreement is checked on integral generators (on-the-spot (c),
tex 8884–8886 and 8944–8946). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex Filter
open scoped MatrixGroups

section MapMatrices

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)

theorem map_upperMatrix (x : A) :
    Matrix.SpecialLinearGroup.map f (upperMatrix x) = upperMatrix (f x) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperMatrix, RingHom.mapMatrix_apply]

theorem map_diagonalMatrix (t : Aˣ) :
    Matrix.SpecialLinearGroup.map f (diagonalMatrix t) = diagonalMatrix (Units.map f t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalMatrix, RingHom.mapMatrix_apply, ← map_inv]

theorem map_weylMatrix :
    Matrix.SpecialLinearGroup.map f weylMatrix = weylMatrix := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMatrix, RingHom.mapMatrix_apply]

end MapMatrices

variable (a b : Fin 3 → ℕ)

def Good (p : Place) : Prop :=
  p ≠ dyadicPlace ∧ p ∉ badPlaces (determinant a) ∧ p ∉ badPlaces (determinant b)

theorem eventually_good : ∀ᶠ p in cofinite, Good a b p := by
  have h := (((badPlaces (determinant a)).finite_toSet.union
    (badPlaces (determinant b)).finite_toSet).union (Set.finite_singleton dyadicPlace)).compl_mem_cofinite
  filter_upwards [h] with p hp
  simpa only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Finset.mem_coe,
    not_or, Good, and_comm, and_left_comm, and_assoc] using hp

variable [∀ i, NeZero (2 * a i)] [∀ i, NeZero (2 * b i)]
variable (p : Place) (h : Good a b p)

private def integralOperatorPair : SL(2, ℤ_[p.val]) →* OperatorPair p :=
  (local_integral_action p a h.1 h.2.1).choose.prod (local_integral_action p b h.1 h.2.2).choose

private theorem integralOperatorPair_generators :
    (∀ x : ℤ_[p.val], integralOperatorPair a b p h (upperMatrix x) =
      pairUpper p a b (x : ℚ_[p.val])) ∧
    (∀ t : ℤ_[p.val]ˣ, integralOperatorPair a b p h (diagonalMatrix t) =
      pairDiagonal p a b (Units.map (PadicInt.Coe.ringHom (p := p.val)) t)) ∧
    integralOperatorPair a b p h weylMatrix = pairWeyl p a b := by
  obtain ⟨haU, haM, haW, _⟩ := (local_integral_action p a h.1 h.2.1).choose_spec
  obtain ⟨hbU, hbM, hbW, _⟩ := (local_integral_action p b h.1 h.2.2).choose_spec
  exact ⟨fun x => Prod.ext (haU x) (hbU x), fun t => Prod.ext (haM t) (hbM t), Prod.ext haW hbW⟩

private theorem pairIntegral_agree (k : SL(2, ℤ_[p.val])) :
    pairProjective p a b (includeIntegral p k) =
      pairProject p (integralOperatorPair a b p h k) := by
  let E := ((pairProjective p a b).comp (includeIntegral p)).eqLocus
    ((pairProject p).comp (integralOperatorPair a b p h))
  obtain ⟨hu, hm, hw⟩ := integralOperatorPair_generators a b p h
  obtain ⟨HU, HM, HW⟩ := pairProjective_generators p a b
  have hg : k ∈ E := integral_generators E
    (fun x => by
      change pairProjective p a b (includeIntegral p (upperMatrix x)) =
        pairProject p (integralOperatorPair a b p h (upperMatrix x))
      rw [includeIntegral, map_upperMatrix, HU, hu]
      rfl)
    (fun t => by
      change pairProjective p a b (includeIntegral p (diagonalMatrix t)) =
        pairProject p (integralOperatorPair a b p h (diagonalMatrix t))
      rw [includeIntegral, map_diagonalMatrix, HM, hm])
    (by
      change pairProjective p a b (includeIntegral p weylMatrix) =
        pairProject p (integralOperatorPair a b p h weylMatrix)
      rw [includeIntegral, map_weylMatrix, HW, hw]) k
  exact hg

/-- One section, whose images in both operator groups are the spherical
representatives. Its projection is the inclusion of the integral group. -/
def commonSection : SL(2, ℤ_[p.val]) →* LocalCommon p a b where
  toFun k := coverLift _ _ _ _ (pairIntegral_agree a b p h k)
  map_one' := by
    apply Subtype.ext
    exact Prod.ext (map_one _) (map_one _)
  map_mul' x y := by
    apply Subtype.ext
    exact Prod.ext (map_mul _ x y) (map_mul _ x y)

theorem commonSection_first (k : SL(2, ℤ_[p.val])) :
    (localFirst p a b (commonSection a b p h k) : LocalEnd p) (spherical p) = spherical p :=
  (local_integral_action p a h.1 h.2.1).choose_spec.2.2.2 k

theorem commonSection_second (k : SL(2, ℤ_[p.val])) :
    (localSecond p a b (commonSection a b p h k) : LocalEnd p) (spherical p) = spherical p :=
  (local_integral_action p b h.1 h.2.2).choose_spec.2.2.2 k

theorem commonSection_upper (x : ℤ_[p.val]) :
    commonSection a b p h (upperMatrix x) = liftUpper p a b (x : ℚ_[p.val]) := by
  apply Subtype.ext
  exact Prod.ext (map_upperMatrix _ x) ((integralOperatorPair_generators a b p h).1 x)

theorem commonSection_weyl :
    commonSection a b p h weylMatrix = liftWeyl p a b := by
  apply Subtype.ext
  exact Prod.ext (map_weylMatrix _) (integralOperatorPair_generators a b p h).2.2


end ZInQ.Manuscript.RC.Metaplectic2
