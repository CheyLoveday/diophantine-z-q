import ZInQKernel.Contrib.OneProof.RC.LocalTorus.SplitRealization

/-! Realize the two detecting orientations and assemble the placewise witnesses. Tex 9136–9156. -/

noncomputable section

set_option maxHeartbeats 450000

namespace ZInQ.Manuscript.RC.LocalTorus

open Eichler Adelic O7Actual O7Orbits PicardFibers Matrix LocalWeights

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}
variable {F : Type} [Field F] [NumberField F]

private theorem affine_cancel {K B : Type*} [Field K] [CharZero K] [Ring B] [Algebra K B]
    {X Y : B} (h : 2 * X - 1 = 2 * Y - 1) : X = Y := by
  have htwo : IsUnit (2 : B) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : K) ≠ 0)).map (algebraMap K B)
  exact htwo.mul_left_cancel (sub_left_inj.mp h)

private theorem division_order_eq (s : StageAt O N M hN m) :
    (ActualOrder s).completion s.ell = DivisionJoin.completedOrder s.ell s.mod_four := by
  let p : Prime := ⟨s.ell, Fact.out⟩
  change (ActualOrder s).completion p.val = _
  rw [Adelic.levelOrder_completion, Adelic.levelLocal, dite_eq_right (not_not.mpr rfl)]

private theorem division_chart_eq (s : StageAt O N M hN m) :
    divisionOrderChart s = (Subalgebra.equivOfEq _ _ (division_order_eq s)).toRingEquiv.trans
      (DivisionJoin.orderEquiv s.ell s.mod_four).toRingEquiv := by
  unfold divisionOrderChart
  rfl

private theorem transported_chart_val {R A B : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] {S T : Subalgebra R A} {U : Subalgebra R B}
    (e : S ≃+* U) (h : S = T) (f : T ≃+* U)
    (he : e = (Subalgebra.equivOfEq S T h).toRingEquiv.trans f)
    (g : A → B) (hf : ∀ z : T, (f z).val = g z.val) (x : S) :
    (e x).val = g x.val := by
  rw [he, RingEquiv.trans_apply]
  exact hf ((Subalgebra.equivOfEq S T h) x)

set_option maxHeartbeats 140000 in
private theorem division_chart_val (s : StageAt O N M hN m)
    (X : (ActualOrder s).completion s.ell) :
    (divisionOrderChart s X).val = DivisionJoin.ambientEquiv s.ell X.val :=
  transported_chart_val (divisionOrderChart s) (division_order_eq s)
    (DivisionJoin.orderEquiv s.ell s.mod_four).toRingEquiv (division_chart_eq s)
    (DivisionJoin.ambientEquiv s.ell)
    (fun z => (DivisionJoin.order_compatible s.ell s.mod_four z).symm) X

private theorem noncentral_of_nonsquare {K A : Type*} [Field K] [Ring A] [Algebra K A]
    {X : A} {d : K} (hd : ¬ IsSquare d) (hs : X * X = algebraMap K A d)
    (hcenter : ∀ X : A, (∀ w : A, X * w = w * X) → ∃ c : K, X = algebraMap K A c)
    [Nontrivial A] : ∃ w : A, X * w ≠ w * X := by
  by_contra! h
  obtain ⟨c, hc⟩ := hcenter X h
  rw [hc, ← map_mul] at hs
  exact hd ⟨c, (algebraMap K A).injective hs.symm⟩

private theorem division_root_for_bit {ell : ℕ} [Fact ell.Prime]
    [Fact (ell % 4 = 3)] {d : ℤ} (hd : legendreSym ell d = -1) (b : Bool) :
    ∃ W : LocalDivision.order ell, W * W = (d : LocalDivision.order ell) ∧
      residueBit (LocalDivision.red W) (-LocalDivision.red W) = b := by
  obtain ⟨y, _, hy, hred⟩ := division_root_exists hd
  have hneg : LocalDivision.red (-y) = -LocalDivision.red y :=
    map_neg (LocalDivision.red (p := ell)) y
  have hn := (division_labels y hred).1
  rw [hneg] at hn
  by_cases hb : residueBit (LocalDivision.red y) (-LocalDivision.red y) = b
  · exact ⟨y, hy, hb⟩
  · refine ⟨-y, by simpa only [neg_mul_neg] using hy, ?_⟩
    rw [hneg, neg_neg]
    exact eq_of_two_distinct_bits (residueBit_swap_ne hn).symm hb

private theorem division_affine_model {ell : ℕ} [Fact ell.Prime]
    [Fact (ell % 4 = 3)] (W : LocalDivision.order ell) :
    ∃ V : LocalDivision.order ell, 2 * V - 1 = W := by
  have h2 : IsUnit (2 : ℤ_[ell]) := by
    apply (PadicInt.isUnit_iff).mpr
    have hne : ell ≠ 2 := by have := (Fact.out : ell % 4 = 3); omega
    change ‖(2 : ℤ_[ell])‖ = 1
    exact (PadicInt.norm_natCast_eq_one_iff (p := ell) (n := 2)).mpr
      ((Fact.out : ell.Prime).coprime_iff_not_dvd.mpr (fun h =>
        hne (le_antisymm (Nat.le_of_dvd (by decide) h) (Fact.out : ell.Prime).two_le)))
  let v : ℤ_[ell]ˣ := h2.unit
  have hv : (v : ℤ_[ell]) = 2 := h2.unit_spec
  have hu : (2 : ℤ_[ell]) * (↑v⁻¹ : ℤ_[ell]) = 1 := by
    rw [← hv, Units.mul_inv]
  let V : LocalDivision.order ell := (↑v⁻¹ : ℤ_[ell]) • (1 + W)
  refine ⟨V, ?_⟩
  have htwo := (map_ofNat (algebraMap ℤ_[ell] (LocalDivision.order ell)) 2).symm
  calc
    2 * V - 1 = (2 : ℤ_[ell]) • V - 1 := by rw [Algebra.smul_def, ← htwo]
    _ = W := by
      change (2 : ℤ_[ell]) • ((↑v⁻¹ : ℤ_[ell]) • (1 + W)) - 1 = W
      rw [smul_smul, hu, one_smul, add_comm, add_sub_cancel_right]

private theorem division_square_val {ell : ℕ} [Fact ell.Prime] [Fact (ell % 4 = 3)]
    {W : LocalDivision.order ell} {d : ℤ} (hW : W * W = (d : LocalDivision.order ell)) :
    W.val * W.val = algebraMap ℚ_[ell] (LocalDivision.D ell) (d : ℚ_[ell]) := by
  calc
    W.val * W.val = (W * W).val := rfl
    _ = (d : LocalDivision.order ell).val := congrArg (fun w : LocalDivision.order ell => w.val) hW
    _ = (d : LocalDivision.D ell) := map_intCast (LocalDivision.order ell).val d
    _ = _ := (map_intCast (algebraMap ℚ_[ell] (LocalDivision.D ell)) d).symm

/-- At the detecting prime the two opposite reduced roots give the two
bits. Conjugacy is in the ambient division algebra. -/
theorem realize_division (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ)))
    (t : Orientations N.primeFactors.card) :
    let p : Prime := ⟨s.ell, Fact.out⟩
    ∃ u : (Bp p.val (-1) (-(s.ell : ℚ)))ˣ,
    ∃ h : unitConjRing u⁻¹ (toLocal p.val (referenceAffine s Q ι)) ∈
      (ActualOrder s).completion p.val, LabelAt s t p ⟨_, h⟩ := by
  let p : Prime := ⟨s.ell, Fact.out⟩
  let _ : Fact (s.ell % 4 = 3) := ⟨s.mod_four⟩
  have hd : legendreSym s.ell (disc s D) = -1 := by
    rw [disc, legendreSym.mul, A.detecting, hh, one_mul]
  obtain ⟨W, hW, hbit⟩ := division_root_for_bit hd (t (Fin.last N.primeFactors.card))
  obtain ⟨V, hV⟩ := division_affine_model W
  let g := DivisionJoin.ambientEquiv s.ell
  let X := g (toLocal p.val (referenceUnit s A Q ι).val)
  have hx : X * X = algebraMap ℚ_[s.ell] (LocalDivision.D s.ell) (disc s D : ℚ_[s.ell]) := by
    change g (toLocal p.val (referenceUnit s A Q ι).val) *
      g (toLocal p.val (referenceUnit s A Q ι).val) = _
    rw [← map_mul, (local_reference_root s A Q ι p).2.1]
    simp only [map_intCast]
  have hY := division_square_val hW
  have hn := detecting_nonsquare A.detecting hh
  have hdq : ¬ IsSquare (disc s D : ℚ_[s.ell]) := padic_nonsquare_of_residue hn
  have hnc : ∃ w : LocalDivision.D s.ell, X * w ≠ w * X := by
    apply noncentral_of_nonsquare hdq hx
    intro Z hZ
    let I : LocalDivision.D s.ell := ⟨0, 1, 0, 0⟩
    let J : LocalDivision.D s.ell := ⟨0, 0, 1, 0⟩
    have hi := congrArg QuaternionAlgebra.imK (hZ I)
    have hj := congrArg QuaternionAlgebra.imJ (hZ I)
    have hk := congrArg QuaternionAlgebra.imK (hZ J)
    simp [I, J, QuaternionAlgebra.imK_mul, QuaternionAlgebra.imJ_mul] at hi hj hk
    refine ⟨Z.re, QuaternionAlgebra.ext ?_ ?_ ?_ ?_⟩
    · rfl
    · change Z.imI = 0
      linear_combination hk / 2
    · change Z.imJ = 0
      linear_combination -hi / 2
    · change Z.imK = 0
      linear_combination hj / 2
  obtain ⟨w, hw⟩ := division_ambient_conj hx hY hnc
  let u := Units.map g.symm.toMonoidHom w
  let Y := (divisionOrderChart s).symm V
  have he : unitConjRing u⁻¹ (toLocal p.val (referenceAffine s Q ι)) = Y.val := by
    apply g.injective
    have hmap := conj_map_equiv g.toRingEquiv w (toLocal p.val (referenceAffine s Q ι))
    change g (unitConjRing u⁻¹ (toLocal p.val (referenceAffine s Q ι))) = _ at hmap
    rw [hmap]
    apply affine_cancel (K := ℚ_[s.ell])
    let a := toLocal p.val (referenceAffine s Q ι)
    have hα₀ : 2 * a - 1 = toLocal p.val (referenceUnit s A Q ι).val := by
      simpa only [map_sub, map_mul, map_ofNat, map_one] using
        congrArg (toLocal p.val) (referenceAffine_spec s A Q ι)
    have hα : 2 * g a - 1 = X := by
      calc
        2 * g a - 1 = g (2 * a - 1) := by rw [map_sub, map_mul, map_ofNat, map_one]
        _ = X := congrArg g hα₀
    have hβ : 2 * g Y.val - 1 = W.val := by
      rw [← division_chart_val s Y]
      change 2 * ((divisionOrderChart s) ((divisionOrderChart s).symm V)).val - 1 = _
      rw [(divisionOrderChart s).apply_symm_apply]
      exact congrArg (fun w : LocalDivision.order s.ell => w.val) hV
    have hw' : unitConjRing w⁻¹ X = W.val := by
      simpa only [unitConjRing_apply, inv_inv] using hw
    let f := unitConjRing w⁻¹
    have he' (a : LocalDivision.D s.ell) : f (2 * a - 1) = 2 * f a - 1 := by
      rw [map_sub f (2 * a) 1, map_mul f 2 a, map_one f, map_ofNat f 2]
    exact (he' a).symm.trans ((congrArg f hα).trans (hw'.trans hβ.symm))
  have hlabel : LabelAt s t p Y := by
    constructor
    · intro j h
      exact (levelPrime_ne_detecting s j (congrArg Subtype.val h).symm).elim
    · intro h
      have heq : h = rfl := Subsingleton.elim _ _
      cases heq
      change divisionBit s Y = _
      let e := divisionOrderChart s
      let f : (ActualOrder s).completion s.ell →+* LocalDivision.order s.ell := e.toRingHom
      have hredV : e (2 * Y - 1) = W := by
        change f (2 * Y - 1) = W
        calc
          f (2 * Y - 1) = f (2 * Y) - f 1 := map_sub f (2 * Y) 1
          _ = 2 * f Y - 1 := by rw [map_mul f 2 Y, map_ofNat f 2, map_one f]
          _ = W := by
            change 2 * e (e.symm V) - 1 = W
            rw [e.apply_symm_apply, hV]
      change residueBit (LocalDivision.red (e (2 * Y - 1)))
        (-LocalDivision.red (e (2 * Y - 1))) = _
      rw [hredV]
      exact hbit
  have hm : unitConjRing u⁻¹ (toLocal p.val (referenceAffine s Q ι)) ∈
      (ActualOrder s).completion s.ell := he.symm ▸ Y.prop
  have hs : (⟨_, hm⟩ : (ActualOrder s).completion s.ell) = Y := Subtype.ext he
  exact ⟨u, hm, hs.symm ▸ hlabel⟩

/-- Every actual tuple has an integral conjugate of the reference generator
carrying its specified bit at every labeled place. -/
theorem hasLocalRealizations (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) :
    ∀ t, HasLocalRealizations s (referenceAffine s Q ι) t := by
  intro t p
  by_cases hp : p.val = s.ell
  · have he : p = (⟨s.ell, Fact.out⟩ : Prime) := Subtype.ext hp
    subst p
    exact realize_division s A hh Q ι t
  · exact realize_split s A Q ι t p hp

end ZInQ.Manuscript.RC.LocalTorus
