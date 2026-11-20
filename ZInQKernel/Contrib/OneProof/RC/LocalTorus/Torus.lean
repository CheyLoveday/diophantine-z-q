import ZInQKernel.Contrib.OneProof.RC.LocalTorus.QuadraticCompletion
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Ambient
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Algebra.Group.Pi.Units

/-! The local quadratic torus and its integral intersection. Tex 9164–9165.
The affine basis avoids dividing by two in any completed order. The
comparison is on-the-spot (c). -/

noncomputable section

set_option maxHeartbeats 1100000

open scoped NumberField Quaternion

namespace ZInQ.Manuscript.RC.LocalTorus

open Eichler Adelic O7Actual O7Orbits PicardFibers IsDedekindDomain HeightOneSpectrum

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}
variable {F : Type} [Field F] [NumberField F]

private abbrev Loc (s : StageAt O N M hN m) (p : Prime) := Bp p.val (-1) (-(s.ell : ℚ))

private theorem local_order_finite {a b : ℚ} (R : Order a b) (p : Prime) :
    Module.Finite ℤ_[p.val] (R.completion p.val) := by
  let e := R.full.ratBasis (QuaternionAlgebra.basisOneIJK a 0 b)
  have h := (Submodule.fg_span (R := ℤ_[p.val]) (Set.finite_range
    (Module.Basis.ofEquivFun (localCoordinates p e))))
  have he : Submodule.span ℤ (Set.range e) = R.lattice := R.full.span_ratBasis _
  rw [← localLattice_basis p e, he, ← Order.completion_toSubmodule] at h
  exact Module.Finite.of_fg h

private def ambientEval (s : StageAt O N M hN m) {D c : ℤ}
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ)))
    (hc : disc s D = 1 - 4 * c) (p : Prime) :
    QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1 →ₐ[ℚ_[p.val]] Loc s p :=
  let x := toLocal p.val (referenceAffine s Q ι)
  QuadraticAlgebra.lift ⟨x, by
    have hh := congrArg ((toLocal p.val).comp ι.toRingHom) (affine_relation Q hc)
    simp only [RingHom.comp_apply, map_mul, map_add, map_neg, map_intCast] at hh
    change x * x = -(c : Loc s p) + x at hh
    change x * x = -(c : ℚ_[p.val]) • (1 : Loc s p) + (1 : ℚ_[p.val]) • x
    simpa only [← Algebra.algebraMap_eq_smul_one, one_smul, map_neg, map_intCast] using hh⟩

private theorem ambientEval_apply (s : StageAt O N M hN m) {D c : ℤ}
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ)))
    (hc : disc s D = 1 - 4 * c) (p : Prime)
    (x : QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1) :
    ambientEval s Q ι hc p x = x.re • (1 : Loc s p) +
      x.im • toLocal p.val (referenceAffine s Q ι) := rfl

private theorem ambientEval_injective (s : StageAt O N M hN m) {D c : ℤ}
    (A : AdmissibleD s D) (Q : QuadraticBasis F (disc s D))
    (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) (hc : disc s D = 1 - 4 * c) (p : Prime) :
    Function.Injective (ambientEval s Q ι hc p) := by
  let X := toLocal p.val (referenceAffine s Q ι)
  let Y := toLocal p.val (referenceUnit s A Q ι).val
  have hXY : 2 * X - 1 = Y := by
    simpa only [map_sub, map_mul, map_ofNat, map_one] using
      congrArg (toLocal p.val) (referenceAffine_spec s A Q ι)
  obtain ⟨hY, _, hnY⟩ := local_reference_root s A Q ι p
  have hn (a : ℚ_[p.val]) : X ≠ algebraMap ℚ_[p.val] (Loc s p) a := by
    intro h
    have he : Y = algebraMap ℚ_[p.val] (Loc s p) (2 * a - 1) := by
      rw [← hXY, h, map_sub, map_mul, map_ofNat, map_one]
    have hr : Y.re = 2 * a - 1 := congrArg QuaternionAlgebra.re he
    apply hnY
    change Y = 0
    change Y.re = 0 at hY
    rw [he, ← hr, hY, map_zero]
  intro a b h
  rw [ambientEval_apply, ambientEval_apply] at h
  have him : (a.im - b.im) • X = algebraMap ℚ_[p.val] (Loc s p) (b.re - a.re) := by
    rw [sub_smul, map_sub, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    calc
      _ = (a.re • (1 : Loc s p) + a.im • X) -
          (a.re • (1 : Loc s p) + b.im • X) := by abel
      _ = _ := by rw [h]; abel
  have hi : a.im = b.im := by
    by_contra hne
    apply hn ((a.im - b.im)⁻¹ * (b.re - a.re))
    calc
      X = (a.im - b.im)⁻¹ • ((a.im - b.im) • X) := by
        rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
      _ = _ := by rw [him, Algebra.smul_def, ← map_mul]
  exact QuadraticAlgebra.ext
    ((algebraMap ℚ_[p.val] (Loc s p)).injective (by
      rw [hi, add_left_inj, ← Algebra.algebraMap_eq_smul_one,
        ← Algebra.algebraMap_eq_smul_one] at h
      exact h)) hi

private theorem ambientEval_image (s : StageAt O N M hN m) {D c : ℤ}
    (A : AdmissibleD s D) (Q : QuadraticBasis F (disc s D))
    (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) (hc : disc s D = 1 - 4 * c)
    (p : Prime) (w : Loc s p) :
    w ∈ Set.range (ambientEval s Q ι hc p) ↔
      Commute w (toLocal p.val (referenceUnit s A Q ι).val) := by
  let α := toLocal p.val (referenceAffine s Q ι)
  let x := toLocal p.val (referenceUnit s A Q ι).val
  have hα : 2 * α - 1 = x := by
    simpa only [map_mul, map_ofNat, map_sub, map_one] using
      congrArg (toLocal p.val) (referenceAffine_spec s A Q ι)
  constructor
  · rintro ⟨y, rfl⟩
    rw [ambientEval_apply]
    change Commute (y.re • (1 : Loc s p) + y.im • α) x
    rw [← hα]
    have ht : Commute α (2 : Loc s p) := by
      rw [← map_ofNat (algebraMap ℚ_[p.val] (Loc s p))]
      exact (Algebra.commutes _ _).symm
    have he : Commute α (2 * α - 1) :=
      (ht.mul_right (Commute.refl α)).sub_right (Commute.one_right _)
    exact ((Commute.one_left _).smul_left _).add_left (he.smul_left _)
  · intro hw
    obtain ⟨hr, _, hn⟩ := local_reference_root s A Q ι p
    have ha : ((-1 : ℚ) : ℚ_[p.val]) ≠ 0 := Rat.cast_ne_zero.mpr s.weights.ha.ne
    have hb : ((-(s.ell : ℚ)) : ℚ_[p.val]) ≠ 0 := Rat.cast_ne_zero.mpr s.weights.hb.ne
    obtain ⟨t, ht⟩ := local_centralizer_span ha hb hr hn hw
    refine ⟨⟨w.re - t, 2 * t⟩, ?_⟩
    rw [ambientEval_apply]
    refine Eq.trans ?_ ht.symm
    change (w.re - t) • (1 : Loc s p) + (2 * t) • α =
      algebraMap ℚ_[p.val] (Loc s p) w.re + t • x
    rw [← hα]
    rw [Algebra.algebraMap_eq_smul_one, sub_smul, smul_sub,
      show (2 : Loc s p) * α = (2 : ℚ_[p.val]) • α by rw [Algebra.smul_def, map_ofNat],
      smul_smul, mul_comm t 2]
    abel

private def embedProduct (s : StageAt O N M hN m) {D c : ℤ}
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ)))
    (hc : disc s D = 1 - 4 * c) (p : Prime) : AdicProduct F p →+* Loc s p :=
  (ambientEval s Q ι hc p).toRingHom.comp (completedQuadratic Q p hc).symm.toRingHom

private theorem embedProduct_diagonal (s : StageAt O N M hN m) {D c : ℤ}
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ)))
    (hc : disc s D = 1 - 4 * c) (p : Prime) (x : F) :
    embedProduct s Q ι hc p (fun _v => algebraMap F _ x) = toLocal p.val (ι x) := by
  obtain ⟨a, b, hab⟩ := generator_rational_span Q x
  let y : QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1 := ⟨a, b⟩
  have hy : completedQuadratic Q p hc y = fun _v => algebraMap F _ x := by
    funext v
    rw [completedQuadratic_apply]
    change affineEval Q p (a : ℚ_[p.val]) (b : ℚ_[p.val]) v = _
    rw [affineEval_rat, ← hab]
  rw [← hy]
  change ambientEval s Q ι hc p ((completedQuadratic Q p hc).symm
    (completedQuadratic Q p hc y)) = _
  rw [(completedQuadratic Q p hc).symm_apply_apply, ambientEval_apply, hab]
  simp only [Algebra.smul_def, mul_one, map_add, map_mul]
  change algebraMap ℚ_[p.val] (Loc s p) (a : ℚ_[p.val]) +
      algebraMap ℚ_[p.val] (Loc s p) (b : ℚ_[p.val]) *
        toLocal p.val (referenceAffine s Q ι) =
    toLocal p.val (ι (algebraMap ℚ F a)) +
      toLocal p.val (ι (algebraMap ℚ F b)) * toLocal p.val (ι (generator Q))
  rw [ι.commutes, ι.commutes]
  rfl

private def conjAlg {K A : Type*} [CommRing K] [Ring A] [Algebra K A] (z : Aˣ) :
    A →ₐ[K] A where
  __ := unitConjRing z
  commutes' a := by
    change unitConjRing z (algebraMap K A a) = _
    rw [unitConjRing_apply, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

private theorem conjugated_integral_iff (s : StageAt O N M hN m) {D c : ℤ}
    (A : AdmissibleD s D) (Q : QuadraticBasis F (disc s D))
    (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) (hc : disc s D = 1 - 4 * c)
    (p : Prime) (z : (Loc s p)ˣ)
    (hz : unitConjRing z⁻¹ (toLocal p.val (referenceAffine s Q ι)) ∈
      (ActualOrder s).completion p.val) (x : AdicProduct F p) :
    unitConjRing z⁻¹ (embedProduct s Q ι hc p x) ∈ (ActualOrder s).completion p.val ↔
      ∀ v : PlacesAbove F p, x v ∈ v.val.adicCompletionIntegers F := by
  let e := completedQuadratic Q p hc
  let y := e.symm x
  have hx : x = affineEval Q p y.re y.im :=
    (e.apply_symm_apply x).symm.trans (completedQuadratic_apply Q p hc y)
  have hy : embedProduct s Q ι hc p x = ambientEval s Q ι hc p y := rfl
  let fQ := (conjAlg (K := ℚ_[p.val]) z⁻¹).comp (ambientEval s Q ι hc p)
  let f : QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1 →ₐ[ℤ_[p.val]] Loc s p :=
    { __ := fQ.toRingHom
      commutes' a := fQ.commutes (a : ℚ_[p.val]) }
  constructor
  · intro h
    let _ := local_order_finite (ActualOrder s) p
    let Y : (ActualOrder s).completion p.val := ⟨_, h⟩
    have hI : IsIntegral ℤ_[p.val] Y := IsIntegral.of_finite ℤ_[p.val] Y
    have hi : IsIntegral ℤ_[p.val] (f y) :=
      (isIntegral_algHom_iff ((ActualOrder s).completion p.val).val Subtype.val_injective).mpr hI
    have hf : Function.Injective f := by
      intro a b he
      have h' := congrArg (unitConjRing z) he
      change unitConjRing z (unitConjRing z⁻¹ (ambientEval s Q ι hc p a)) =
        unitConjRing z (unitConjRing z⁻¹ (ambientEval s Q ι hc p b)) at h'
      have hconj (x : Loc s p) : unitConjRing z (unitConjRing z⁻¹ x) = x := by
        rw [unitConjRing_mul z z⁻¹ x, mul_inv_cancel, unitConjRing_apply]
        simp
      exact ambientEval_injective s A Q ι hc p
        ((hconj _).symm.trans (h'.trans (hconj _)))
    have hiy := (isIntegral_algHom_iff f hf).mp hi
    intro v
    let g : QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1 →+* v.val.adicCompletion F :=
      (Pi.evalRingHom _ v).comp e.toRingHom
    let k : ℤ_[p.val] →+* v.val.adicCompletionIntegers F :=
      ((completedScalar p v).comp PadicInt.Coe.ringHom).codRestrict _ (completedScalar_mem p v)
    have hk : (algebraMap (v.val.adicCompletionIntegers F) _).comp k =
        g.comp (algebraMap ℤ_[p.val] _) := by
      apply RingHom.ext
      intro a
      change completedScalar p v a.val = completedQuadratic Q p hc (algebraMap ℤ_[p.val]
        (QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1) a) v
      rw [completedQuadratic_apply]
      change completedScalar p v a.val = affineEval Q p a.val 0 v
      simp only [affineEval, map_zero, zero_mul, add_zero]
    have hiv := hiy.map_of_comp_eq k g hk
    have hv := (adicCompletionIntegers.integers F v.val).isIntegral_iff_v_le_one.mp hiv
    have hgv : g y = x v := congrFun (e.apply_symm_apply x) v
    exact hgv ▸ hv
  · intro h
    have hab := (affineEval_mem_iff Q p y.re y.im).mp (hx ▸ h)
    rw [hy, ambientEval_apply]
    change (conjAlg (K := ℚ_[p.val]) z⁻¹)
      (y.re • (1 : Loc s p) + y.im • toLocal p.val (referenceAffine s Q ι)) ∈ _
    rw [map_add, map_smul, map_smul, map_one]
    exact (ActualOrder s).completion p.val |>.add_mem
      (Subalgebra.smul_mem _ (one_mem _) (⟨y.re, hab.1⟩ : ℤ_[p.val]))
      (Subalgebra.smul_mem _ hz (⟨y.im, hab.2⟩ : ℤ_[p.val]))

/-- The actual completed torus chart at every rational prime. -/
theorem localTorusChart (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (Q : QuadraticBasis F (disc s D))
    (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) :
    ∀ p, Nonempty (LocalTorusChart (ActualOrder s) ι (referenceUnit s A Q ι)
      (referenceAffine s Q ι) p) := by
  intro p
  let c := (1 - disc s D) / 4
  have h8 := A.mod_eight
  have hc : disc s D = 1 - 4 * c := by dsimp [c]; omega
  let f := embedProduct s Q ι hc p
  let i : PrimeBlock F p ≃* (AdicProduct F p)ˣ := MulEquiv.piUnits.symm
  let Z := Subgroup.centralizer
    ({Units.map (toLocal p.val).toMonoidHom (referenceUnit s A Q ι)} : Set (Loc s p)ˣ)
  have hrange (w : Loc s p) : w ∈ Set.range f ↔
      Commute w (toLocal p.val (referenceUnit s A Q ι).val) := by
    rw [← ambientEval_image s A Q ι hc]
    exact ⟨fun ⟨y, hy⟩ => ⟨(completedQuadratic Q p hc).symm y, hy⟩,
      fun ⟨y, hy⟩ => ⟨completedQuadratic Q p hc y, by
        change ambientEval s Q ι hc p ((completedQuadratic Q p hc).symm
          (completedQuadratic Q p hc y)) = w
        rw [RingEquiv.symm_apply_apply, hy]⟩⟩
  have hf : Function.Injective f :=
    (ambientEval_injective s A Q ι hc p).comp (completedQuadratic Q p hc).symm.injective
  let g : (AdicProduct F p)ˣ →* Z :=
    (Units.map f.toMonoidHom).codRestrict Z (fun w => by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply Units.ext
      exact (hrange _).mp ⟨w.val, rfl⟩)
  have hbij : Function.Bijective g := by
    constructor
    · intro a b he
      exact Units.ext (hf (congrArg (fun x : Z => x.val.val) he))
    · intro w
      have hw : w.val ∈ Z := w.prop
      have hinv : w.val⁻¹ ∈ Z := Z.inv_mem hw
      obtain ⟨a, ha⟩ := (hrange w.val.val).mpr
        (congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.mp hw))
      obtain ⟨b, hb⟩ := (hrange w.val.inv).mpr
        (congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.mp hinv))
      refine ⟨⟨a, b, hf ?_, hf ?_⟩, Subtype.ext (Units.ext ha)⟩
      · rw [map_mul, ha, hb, Units.val_inv, map_one]
      · rw [map_mul, ha, hb, Units.inv_val, map_one]
  refine ⟨⟨i.trans (MulEquiv.ofBijective g hbij), ?_, ?_⟩⟩
  · intro k
    apply Units.ext
    change f (fun v => algebraMap F (v.val.adicCompletion F) k.val) =
      toLocal p.val (ι k.val)
    exact embedProduct_diagonal s Q ι hc p k.val
  · intro z hz u
    have hu := conjugated_integral_iff s A Q ι hc p z hz (i u).val
    have hui := conjugated_integral_iff s A Q ι hc p z hz (i u).inv
    change (unitConjRing z⁻¹ (f (i u).val) ∈ (ActualOrder s).completion p.val ∧
      (↑((z⁻¹ * Units.map f.toMonoidHom (i u) * z)⁻¹) : Loc s p) ∈
        (ActualOrder s).completion p.val) ↔ _
    rw [show (z⁻¹ * Units.map f.toMonoidHom (i u) * z)⁻¹ =
      z⁻¹ * (Units.map f.toMonoidHom (i u))⁻¹ * z by group]
    change (_ ∧ unitConjRing z⁻¹ (f (i u).inv) ∈ _) ↔ _
    rw [hu, hui]
    exact ⟨fun h v => ⟨h.1 v, h.2 v⟩, fun h => ⟨fun v => (h v).1, fun v => (h v).2⟩⟩

end ZInQ.Manuscript.RC.LocalTorus
