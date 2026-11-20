import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Ambient

/-! Realize the two level orientations and the single maximal split orientation. Tex 9136–9156. -/

noncomputable section

set_option maxHeartbeats 450000

namespace ZInQ.Manuscript.RC.LocalTorus

open Eichler Adelic O7Actual O7Orbits PicardFibers Matrix LocalWeights

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}
variable {F : Type} [Field F] [NumberField F]

theorem eq_of_two_distinct_bits {a b c : Bool} (hab : a ≠ b) (hac : a ≠ c) :
    b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem conj_map_equiv {A C : Type*} [Ring A] [Ring C] (g : A ≃+* C)
    (w : Cˣ) (x : A) :
    g (unitConjRing (Units.map g.symm.toMonoidHom w)⁻¹ x) =
      unitConjRing w⁻¹ (g x) := by
  have he : Units.map g.toMonoidHom (Units.map g.symm.toMonoidHom w) = w :=
    Units.ext (g.apply_symm_apply _)
  calc
    _ = unitConjRing (Units.map g.toMonoidHom (Units.map g.symm.toMonoidHom w)⁻¹)
        (g x) := unitConjRing_map g.toRingHom _ _
    _ = _ := by rw [map_inv, he]

private theorem split_of_model (s : StageAt O N M hN m) {D c : ℤ}
    (A : AdmissibleD s D) (Q : QuadraticBasis F (disc s D))
    (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) (hc : disc s D = 1 - 4 * c)
    (p : Prime) (hp : p.val ≠ s.ell) (Y : eichler p.val (N.factorization p.val))
    (ht : Y.val.trace = 1) (hd : Y.val.det = (c : ℤ_[p.val])) :
    ∃ u : (Bp p.val (-1) (-(s.ell : ℚ)))ˣ,
      unitConjRing u⁻¹ (toLocal p.val (referenceAffine s Q ι)) =
        ((splitOrderChart s p hp).symm Y).val := by
  let g := splitChart s.ell s.mod_four p hp
  let Z := matrixCast p.val Y.val
  have htr : Z.trace = 1 := by
    rw [Matrix.trace_fin_two] at ht ⊢
    change (↑(Y.val 0 0) : ℚ_[p.val]) + ↑(Y.val 1 1) = 1
    simpa only [PadicInt.coe_add, PadicInt.coe_one] using
      congrArg (fun x : ℤ_[p.val] => (x : ℚ_[p.val])) ht
  have hdet : Z.det = (c : ℚ_[p.val]) := by
    change (PadicInt.Coe.ringHom.mapMatrix Y.val).det = _
    rw [← RingHom.map_det, hd, map_intCast]
  have hn (a : ℚ_[p.val]) : Z ≠ algebraMap ℚ_[p.val] (Mat ℚ_[p.val]) a := by
    intro h
    have he : (2 : ℚ_[p.val]) * a = 1 := by
      rw [h, Matrix.trace_fin_two] at htr
      simpa [Matrix.algebraMap_matrix_apply, two_mul] using htr
    have ha : a * a = (c : ℚ_[p.val]) := by
      rw [h, Matrix.det_fin_two] at hdet
      simpa [Matrix.algebraMap_matrix_apply] using hdet
    have hz : (disc s D : ℚ_[p.val]) = 0 := by
      rw [hc]
      push_cast
      linear_combination -(2 * a + 1) * he + 4 * ha
    exact A.disc_neg.ne (Int.cast_eq_zero.mp hz)
  obtain ⟨hx, he, hnx⟩ := split_reference s A Q ι hc p hp
  obtain ⟨w, hw⟩ := split_ambient_conj hx htr (he.trans hdet.symm) hnx hn
  let u := Units.map g.symm.toMonoidHom w
  refine ⟨u, g.injective ?_⟩
  have hmap := conj_map_equiv g.toRingEquiv w (toLocal p.val (referenceAffine s Q ι))
  change g (unitConjRing u⁻¹ (toLocal p.val (referenceAffine s Q ι))) = _ at hmap
  rw [hmap]
  change unitConjRing w⁻¹ (g _) = g ((splitOrderChart s p hp).symm Y).val
  have hw' : unitConjRing w⁻¹ (g (toLocal p.val (referenceAffine s Q ι))) = Z := by
    simpa only [unitConjRing_apply, inv_inv] using hw
  let e := splitOrderChart s p hp
  have hy := splitOrderChart_compatible s p hp (e.symm Y)
  change matrixCast p.val (e (e.symm Y)).val = g (e.symm Y).val at hy
  rw [e.apply_symm_apply] at hy
  exact hw'.trans hy

private theorem levelPrime_injective : Function.Injective (levelPrime N) := by
  intro i j h
  apply (N.primeFactors.orderIsoOfFin rfl).injective
  exact Subtype.ext (congrArg (fun q : Prime => q.val) h)

/-- At each prime away from the detecting place, the companion matrix
at exponent zero and the two integral branches at positive exponent
produce the required local conjugate. This includes the place two. -/
theorem realize_split (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (Q : QuadraticBasis F (disc s D))
    (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ)))
    (t : Orientations N.primeFactors.card) (p : Prime) (hp : p.val ≠ s.ell) :
    ∃ u : (Bp p.val (-1) (-(s.ell : ℚ)))ˣ,
    ∃ h : unitConjRing u⁻¹ (toLocal p.val (referenceAffine s Q ι)) ∈
      (ActualOrder s).completion p.val, LabelAt s t p ⟨_, h⟩ := by
  let c := (1 - disc s D) / 4
  have h8 := A.mod_eight
  have hc : disc s D = 1 - 4 * c := by dsimp [c]; omega
  have finish (Y : eichler p.val (N.factorization p.val)) (ht : Y.val.trace = 1)
      (hd : Y.val.det = (c : ℤ_[p.val]))
      (hb : LabelAt s t p ((splitOrderChart s p hp).symm Y)) :
      ∃ u : (Bp p.val (-1) (-(s.ell : ℚ)))ˣ,
      ∃ h : unitConjRing u⁻¹ (toLocal p.val (referenceAffine s Q ι)) ∈
        (ActualOrder s).completion p.val, LabelAt s t p ⟨_, h⟩ := by
    obtain ⟨u, hu⟩ := split_of_model s A Q ι hc p hp Y ht hd
    let Y' := (splitOrderChart s p hp).symm Y
    have hm : unitConjRing u⁻¹ (toLocal p.val (referenceAffine s Q ι)) ∈
        (ActualOrder s).completion p.val := hu.symm ▸ Y'.prop
    have hs : (⟨_, hm⟩ : (ActualOrder s).completion p.val) = Y' := Subtype.ext hu
    exact ⟨u, hm, hs.symm ▸ hb⟩
  by_cases hlev : ∃ j : Fin N.primeFactors.card, p = levelPrime N j
  · obtain ⟨j, rfl⟩ := hlev
    let p := levelPrime N j
    have hpN : p.val ∣ N :=
      Nat.dvd_of_mem_primeFactors ((N.primeFactors.orderIsoOfFin rfl) j).prop
    obtain ⟨a, ha, hu⟩ := split_branch_of_splitsIn hc
      (A.split p.val p.prop (dvd_mul_of_dvd_right hpN 2))
    obtain ⟨Y, Z, hYt, hZt, hYd, hZd, hY, hZ, hne⟩ :=
      split_level_labels (levelPrime_exp hN j) a hu
    have hdet : a * (1 - a) = (c : ℤ_[p.val]) := by linear_combination -ha
    let f := level p.val (N.factorization p.val)
    have hcomp : f Z = 1 - f Y := by rw [hZ, hY, map_sub, map_one]
    have hcomp' : 1 - f Z = f Y := by rw [hcomp, sub_sub_cancel]
    have chooseW : ∃ W : eichler p.val (N.factorization p.val),
        W.val.trace = 1 ∧ W.val.det = (c : ℤ_[p.val]) ∧
          residueBit (f W) (1 - f W) = t j.castSucc := by
      by_cases h : residueBit (f Y) (1 - f Y) = t j.castSucc
      · exact ⟨Y, hYt, hYd.trans hdet, h⟩
      · refine ⟨Z, hZt, hZd.trans hdet, ?_⟩
        rw [hcomp']
        rw [← hcomp] at h
        exact eq_of_two_distinct_bits (residueBit_swap_ne hne) h
    obtain ⟨W, hWt, hWd, hW⟩ := chooseW
    apply finish W hWt hWd
    constructor
    · intro k hk
      have hjk : k = j := levelPrime_injective hk.symm
      subst k
      change levelBit s j ((splitOrderChart s p hp).symm W) = _
      let e := splitOrderChart s p hp
      change residueBit (f (e (e.symm W))) (1 - f (e (e.symm W))) = _
      rw [e.apply_symm_apply]
      exact hW
    · intro he
      exact (hp (congrArg Subtype.val he)).elim
  · have he : N.factorization p.val = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      apply hlev
      let q : N.primeFactors := ⟨p.val, Nat.mem_primeFactors.mpr ⟨p.prop, hd, hN.ne'⟩⟩
      let j := (N.primeFactors.orderIsoOfFin rfl).symm q
      exact ⟨j, Subtype.ext (congrArg Subtype.val
        ((N.primeFactors.orderIsoOfFin rfl).apply_symm_apply q)).symm⟩
    let C : Mat ℤ_[p.val] := !![0, -(c : ℤ_[p.val]); 1, 1]
    let Y : eichler p.val (N.factorization p.val) :=
      ⟨C, by change (p.val : ℤ_[p.val]) ^ N.factorization p.val ∣ C 1 0; rw [he, pow_zero]; exact one_dvd _⟩
    apply finish Y (by simp [Y, C, trace_fin_two]) (by simp [Y, C, det_fin_two])
    exact ⟨fun j h => (hlev ⟨j, h⟩).elim, fun h => (hp (congrArg Subtype.val h)).elim⟩

end ZInQ.Manuscript.RC.LocalTorus
