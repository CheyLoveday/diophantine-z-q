import ZInQKernel.Contrib.OneProof.CMFibreSplit
import ZInQKernel.Contrib.OneProof.CMBranch.CoxProof

/-! # cm-fibre-split: `CMCurveOrder` -/

set_option maxHeartbeats 1000000

noncomputable section

namespace HDec
namespace CMBranch
namespace FibreSplit

section KdAlg
open Polynomial NumberField Module


theorem irreducible_X_sq_sub {d : ℚ} (hd : d < 0) : Irreducible (Polynomial.X ^ 2 - C d : ℚ[X]) := by
  have hdeg : (Polynomial.X ^ 2 - C d : ℚ[X]).natDegree = 2 := by
    rw [natDegree_sub_C, natDegree_X_pow]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [hdeg]; norm_num
  · intro x hx
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hx
    nlinarith [sq_nonneg x]

theorem monic_X_sq_sub (d : ℚ) : (Polynomial.X ^ 2 - C d : ℚ[X]).Monic :=
  monic_X_pow_sub_C d two_ne_zero

theorem fact_irr {d : ℚ} (hd : d < 0) : Fact (Irreducible (Polynomial.X ^ 2 - C d : ℚ[X])) :=
  ⟨irreducible_X_sq_sub hd⟩

theorem finrank_kd {d : ℚ} (hd : d < 0) :
    haveI := fact_irr hd
    Module.finrank ℚ (Kd d) = 2 := by
  haveI := fact_irr hd
  rw [(AdjoinRoot.powerBasis' (monic_X_sq_sub d)).finrank, AdjoinRoot.powerBasis'_dim,
    natDegree_sub_C, natDegree_X_pow]

theorem numberField_kd {d : ℚ} (hd : d < 0) :
    haveI := fact_irr hd
    NumberField (Kd d) := by
  haveI := fact_irr hd
  haveI : FiniteDimensional ℚ (Kd d) := (AdjoinRoot.powerBasis' (monic_X_sq_sub d)).finite
  exact ⟨⟩

theorem root_sq {d : ℚ} : (AdjoinRoot.root (Polynomial.X ^ 2 - C d : ℚ[X])) ^ 2 =
    algebraMap ℚ (Kd d) d := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 - C d : ℚ[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact sub_eq_zero.mp h

theorem isTotallyComplex_kd {d : ℚ} (hd : d < 0) :
    haveI := fact_irr hd
    IsTotallyComplex (Kd d) := by
  haveI := fact_irr hd
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro hreal
  have h1 := congrArg hreal.embedding (root_sq (d := d))
  simp only [map_pow, map_ratCast] at h1
  have h2 : ((d : ℚ) : ℝ) < 0 := by exact_mod_cast hd
  have h3 : hreal.embedding ((algebraMap ℚ (Kd d)) d) = (d : ℝ) :=
    eq_ratCast (hreal.embedding.comp (algebraMap ℚ (Kd d))) d
  have h4 : (hreal.embedding (AdjoinRoot.root (Polynomial.X ^ 2 - C d : ℚ[X]))) ^ 2 = (d : ℝ) := h1.trans h3
  nlinarith [sq_nonneg (hreal.embedding (AdjoinRoot.root (Polynomial.X ^ 2 - C d : ℚ[X])))]

theorem root_not_rat {d : ℚ} (hd : d < 0) :
    AdjoinRoot.root (Polynomial.X ^ 2 - C d : ℚ[X]) ∉ Set.range (algebraMap ℚ (Kd d)) := by
  haveI := fact_irr hd
  rintro ⟨q, hq⟩
  have h := root_sq (d := d)
  rw [← hq, ← map_pow] at h
  have := (algebraMap ℚ (Kd d)).injective h
  nlinarith [sq_nonneg q]

/-- **Finite conductor from one irrational element.** A subring `R ⊆ 𝓞_k` of a quadratic field containing an
element `θ ∉ ℚ` has finite index in `𝓞_k` (through `ℤ[θ] ⊆ R` and cm-branch2's `CoxCore.discr_order`). -/
theorem conductor_ne_zero_of_mem {k : Type} [Field k] [NumberField k] (hk : finrank ℚ k = 2)
    (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring) {θ : k} (hθR : θ ∈ R)
    (hnq : θ ∉ Set.range (algebraMap ℚ k)) : LeafQM.AV.conductor R ≠ 0 := by
  classical
  have hθint : IsIntegral ℤ θ := hR hθR
  -- `1, θ` independent over `ℚ`
  have hli : LinearIndependent ℚ ![(1 : k), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hnq
      refine ⟨-s / t, ?_⟩
      have e : (algebraMap ℚ k t) * θ = - algebraMap ℚ k s := by
        rw [Algebra.smul_def, Algebra.smul_def, _root_.mul_one] at hst
        linear_combination hst
      have ht' : algebraMap ℚ k t ≠ 0 := (_root_.map_ne_zero _).mpr ht
      rw [map_div₀, map_neg, div_eq_iff ht', ← e, mul_comm]
  -- the minimal polynomial of `θ` over `ℤ` is a monic quadratic
  have hdegQ : (minpoly ℚ θ).natDegree = 2 := by
    have hle : (minpoly ℚ θ).natDegree ≤ 2 := by
      rw [← hk]; exact minpoly.natDegree_le θ
    have hne1 : (minpoly ℚ θ).natDegree ≠ 1 := by
      intro h1
      exact hnq (minpoly.natDegree_eq_one_iff.mp h1)
    have hpos : 0 < (minpoly ℚ θ).natDegree :=
      minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral θ)
    omega
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hθint
  have hmon := minpoly.monic hθint
  have hdegZ : (minpoly ℤ θ).natDegree = 2 := by
    rw [← hdegQ, hmap, natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int]
  set b : ℤ := (minpoly ℤ θ).coeff 1
  set N : ℤ := (minpoly ℤ θ).coeff 0
  have hθ : θ ^ 2 + b * θ + N = 0 := by
    have h := minpoly.aeval ℤ θ
    rw [aeval_eq_sum_range, hdegZ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one] at h
    have h2 : (minpoly ℤ θ).coeff 2 = 1 := hdegZ ▸ hmon.coeff_natDegree
    rw [h2] at h
    simp only [zsmul_eq_mul, pow_zero, _root_.mul_one, pow_one, one_zsmul] at h
    linear_combination h
  -- the order `ℤ[θ] = ℤ + ℤθ`
  let S : Subring k :=
    { carrier := {r | ∃ m n : ℤ, r = m + n * θ}
      mul_mem' := by
        rintro _ _ ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
        refine ⟨m * m' - n * n' * N, m * n' + n * m' - n * n' * b, ?_⟩
        push_cast
        linear_combination (↑n * ↑n' : k) * hθ
      one_mem' := ⟨1, 0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
        exact ⟨m + m', n + n', by push_cast; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      neg_mem' := by
        rintro _ ⟨m, n, rfl⟩
        exact ⟨-m, -n, by push_cast; ring⟩ }
  have hSR : S ≤ R := by
    rintro _ ⟨m, n, rfl⟩
    exact R.add_mem (intCast_mem R m) (R.mul_mem (intCast_mem R n) hθR)
  have hSO : S ≤ (integralClosure ℤ k).toSubring := hSR.trans hR
  have hθS : θ ∈ S := ⟨0, 1, by simp⟩
  have hd := CoxCore.discr_order hk S hSO hθS (fun r hr => hr) hnq hli hθ
  have hne : b ^ 2 - 4 * N ≠ 0 := by
    intro h0
    apply hnq
    refine ⟨-(b : ℚ) / 2, ?_⟩
    have h0' : ((b : k)) ^ 2 = 4 * N := by
      exact_mod_cast (sub_eq_zero.mp h0 : b ^ 2 = 4 * N)
    have hsq : (θ + (b : k) / 2) ^ 2 = 0 := by linear_combination hθ + h0' / 4
    have h1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    rw [map_div₀, map_neg, map_intCast, map_ofNat]
    linear_combination -h1
  have hS0 : S.toAddSubgroup.relIndex (integralClosure ℤ k).toSubring.toAddSubgroup ≠ 0 := by
    intro h0
    rw [h0] at hd
    simp at hd
    exact hne hd
  intro h0
  apply hS0
  unfold LeafQM.AV.conductor at h0
  exact Nat.eq_zero_of_zero_dvd (h0 ▸ AddSubgroup.relIndex_dvd_of_le_left _ hSR)


end KdAlg

/-! ## Transport of `End` along an isomorphism of algebraically closed fields -/

section Transport

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TwistDescentXC TwistDescentHFD

variable {L : Type} [Field L] (X : PkgI3.AbVar L) {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra L Ω]
  [Algebra L Ω'] (σ : Ω ≃ₐ[L] Ω')

theorem sp_sigma : sp (algebraMap L Ω') = sp ((σ : Ω ≃+* Ω') : Ω →+* Ω') ≫ sp (algebraMap L Ω) :=
  sp_eq _ _ _ (fun x => σ.commutes x)

/-- The comparison `X_{Ω'} → X_Ω` over `Spec σ`, an isomorphism. -/
def cσ : (X.baseChange Ω').X.left ⟶ (X.baseChange Ω).X.left :=
  xc X.X (sp ((σ : Ω ≃+* Ω') : Ω →+* Ω')) (sp_sigma σ)

instance : IsIso (sp ((σ : Ω ≃+* Ω') : Ω →+* Ω')) := by
  haveI : IsIso (CommRingCat.ofHom ((σ : Ω ≃+* Ω') : Ω →+* Ω')) :=
    (RingEquiv.toCommRingCatIso (σ : Ω ≃+* Ω')).isIso_hom
  dsimp only [sp]; infer_instance

theorem isIso_cσ : IsIso (cσ X σ) :=
  (xc_isPullback X.X (sp ((σ : Ω ≃+* Ω') : Ω →+* Ω')) (sp_sigma σ)).isIso_fst_of_isIso

variable {X σ}

theorem cσ_snd : cσ X σ ≫ (X.baseChange Ω).X.hom =
    (X.baseChange Ω').X.hom ≫ sp ((σ : Ω ≃+* Ω') : Ω →+* Ω') := xc_snd _ _ _

theorem η_cσ : (η[(X.baseChange Ω').X]).left ≫ cσ X σ =
    sp ((σ : Ω ≃+* Ω') : Ω →+* Ω') ≫ (η[(X.baseChange Ω).X]).left := xc_one _ _ _

/-- `c ≫ f ≫ c⁻¹` as an endomorphism of `X_{Ω'}` (rigidity for the group law). -/
def tr (f : PkgI3.AbVar.End (X.baseChange Ω)) : PkgI3.AbVar.End (X.baseChange Ω') :=
  haveI : IsIso (cσ X σ) := isIso_cσ X σ
  let g : (X.baseChange Ω').X.left ⟶ (X.baseChange Ω').X.left := cσ X σ ≫ f.hom.left ≫ inv (cσ X σ)
  have hg : g ≫ (X.baseChange Ω').X.hom = (X.baseChange Ω').X.hom := by
    rw [← cancel_mono (sp ((σ : Ω ≃+* Ω') : Ω →+* Ω'))]
    simp only [g, Category.assoc]
    rw [← cσ_snd, IsIso.inv_hom_id_assoc, Over.w f.hom, cσ_snd]
  let G : (X.baseChange Ω').X ⟶ (X.baseChange Ω').X := Over.homMk g hg
  have hη : η[(X.baseChange Ω').X] ≫ G = η[(X.baseChange Ω').X] := by
    apply Over.OverMorphism.ext
    have hf0 : (η[(X.baseChange Ω).X]).left ≫ f.hom.left = (η[(X.baseChange Ω).X]).left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    show (η[(X.baseChange Ω').X]).left ≫ g = (η[(X.baseChange Ω').X]).left
    simp only [g]
    rw [← Category.assoc, η_cσ, Category.assoc, ← Category.assoc (η[(X.baseChange Ω).X]).left, hf0,
      ← Category.assoc, ← η_cσ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  @PkgI3.AbVar.Hom.mk' Ω' _ _ _ G (G0FibreSimple.rigidityHom Ω' _ _ G hη)

theorem tr_left (f : PkgI3.AbVar.End (X.baseChange Ω)) :
    (tr (X := X) (σ := σ) f).hom.left ≫ cσ X σ = cσ X σ ≫ f.hom.left := by
  haveI : IsIso (cσ X σ) := isIso_cσ X σ
  show (cσ X σ ≫ f.hom.left ≫ inv (cσ X σ)) ≫ cσ X σ = cσ X σ ≫ f.hom.left
  simp

theorem tr_ext {g g' : PkgI3.AbVar.End (X.baseChange Ω')}
    (h : g.hom.left ≫ cσ X σ = g'.hom.left ≫ cσ X σ) : g = g' :=
  haveI : IsIso (cσ X σ) := isIso_cσ X σ
  PkgI3.AbVar.Hom.ext' (Over.OverMorphism.ext ((cancel_mono (cσ X σ)).mp h))

theorem toUnit_left_eq {R : Type} [Field R] (U : Over (Spec (CommRingCat.of R))) :
    (toUnit U).left = U.hom := by
  have := Over.w (toUnit U); simpa using this

theorem tr_one : tr (X := X) (σ := σ) 1 = 1 := by
  apply tr_ext (X := X) (σ := σ)
  rw [tr_left]
  show cσ X σ ≫ 𝟙 _ = 𝟙 _ ≫ cσ X σ
  simp

theorem tr_mul (f g : PkgI3.AbVar.End (X.baseChange Ω)) :
    tr (X := X) (σ := σ) (f * g) = tr (X := X) (σ := σ) f * tr (X := X) (σ := σ) g := by
  apply tr_ext (X := X) (σ := σ)
  rw [tr_left]
  show cσ X σ ≫ (g.hom ≫ f.hom).left = ((tr g).hom ≫ (tr f).hom).left ≫ cσ X σ
  rw [Over.comp_left, Over.comp_left, Category.assoc, tr_left,
    ← Category.assoc (tr (X := X) (σ := σ) g).hom.left, tr_left, Category.assoc]

theorem tr_zero : tr (X := X) (σ := σ) 0 = 0 := by
  apply tr_ext (X := X) (σ := σ)
  rw [tr_left]
  show cσ X σ ≫ (toUnit _ ≫ η[(X.baseChange Ω).X]).left =
    (toUnit _ ≫ η[(X.baseChange Ω').X]).left ≫ cσ X σ
  rw [Over.comp_left, Over.comp_left, toUnit_left_eq, toUnit_left_eq, Category.assoc, η_cσ,
    ← Category.assoc, ← Category.assoc, cσ_snd]

theorem tr_add (f g : PkgI3.AbVar.End (X.baseChange Ω)) :
    tr (X := X) (σ := σ) (f + g) = tr (X := X) (σ := σ) f + tr (X := X) (σ := σ) g := by
  apply tr_ext (X := X) (σ := σ)
  rw [tr_left]
  let P' := ((X.baseChange Ω').X ⊗ (X.baseChange Ω').X).left
  let P := ((X.baseChange Ω).X ⊗ (X.baseChange Ω).X).left
  let x2 : P' ⟶ P := xc2 X.X (sp ((σ : Ω ≃+* Ω') : Ω →+* Ω')) (sp_sigma σ)
  let μ' : P' ⟶ (X.baseChange Ω').X.left := (μ[(X.baseChange Ω').X]).left
  let μ0 : P ⟶ (X.baseChange Ω).X.left := (μ[(X.baseChange Ω).X]).left
  have hmul : μ' ≫ cσ X σ = x2 ≫ μ0 := xc_mul _ _ _
  let lf' : (X.baseChange Ω').X.left ⟶ P' :=
    (lift (tr (X := X) (σ := σ) f).hom (tr (X := X) (σ := σ) g).hom).left
  let lf : (X.baseChange Ω).X.left ⟶ P := (lift f.hom g.hom).left
  let p1 : P ⟶ (X.baseChange Ω).X.left := pullback.fst _ _
  let p2 : P ⟶ (X.baseChange Ω).X.left := pullback.snd _ _
  have hp1 : x2 ≫ p1 = (pullback.fst _ _ : P' ⟶ (X.baseChange Ω').X.left) ≫ cσ X σ := xc2_fst _ _ _
  have hp2 : x2 ≫ p2 = (pullback.snd _ _ : P' ⟶ (X.baseChange Ω').X.left) ≫ cσ X σ := xc2_snd _ _ _
  have hl1 : lf ≫ p1 = f.hom.left := by simp [lf, p1]
  have hl2 : lf ≫ p2 = g.hom.left := by simp [lf, p2]
  have hl1' : lf' ≫ (pullback.fst _ _ : P' ⟶ (X.baseChange Ω').X.left) =
    (tr (X := X) (σ := σ) f).hom.left := by simp [lf']
  have hl2' : lf' ≫ (pullback.snd _ _ : P' ⟶ (X.baseChange Ω').X.left) =
    (tr (X := X) (σ := σ) g).hom.left := by simp [lf']
  have hl : lf' ≫ x2 = cσ X σ ≫ lf := by
    apply pullback.hom_ext
    · show (lf' ≫ x2) ≫ p1 = (cσ X σ ≫ lf) ≫ p1
      rw [Category.assoc, hp1, ← Category.assoc, hl1', tr_left, Category.assoc, hl1]
    · show (lf' ≫ x2) ≫ p2 = (cσ X σ ≫ lf) ≫ p2
      rw [Category.assoc, hp2, ← Category.assoc, hl2', tr_left, Category.assoc, hl2]
  show cσ X σ ≫ lf ≫ μ0 = (lf' ≫ μ') ≫ cσ X σ
  rw [Category.assoc, hmul, ← Category.assoc lf' x2, hl, Category.assoc]

/-- The transport as a ring homomorphism. -/
def trHom : PkgI3.AbVar.End (X.baseChange Ω) →+* PkgI3.AbVar.End (X.baseChange Ω') where
  toFun := tr (X := X) (σ := σ)
  map_one' := tr_one
  map_mul' := tr_mul
  map_zero' := tr_zero
  map_add' := tr_add

theorem trHom_bijective : Function.Bijective (trHom (X := X) (σ := σ)) := by
  haveI : IsIso (cσ X σ) := isIso_cσ X σ
  refine ⟨fun f f' h => ?_, fun g => ?_⟩
  · have e : (tr (X := X) (σ := σ) f).hom.left ≫ cσ X σ = (tr (X := X) (σ := σ) f').hom.left ≫ cσ X σ := by
      change (trHom f).hom.left ≫ _ = (trHom f').hom.left ≫ _
      rw [h]
    rw [tr_left, tr_left] at e
    exact PkgI3.AbVar.Hom.ext' (Over.OverMorphism.ext ((cancel_epi (cσ X σ)).mp e))
  · let fl : (X.baseChange Ω).X.left ⟶ (X.baseChange Ω).X.left := inv (cσ X σ) ≫ g.hom.left ≫ cσ X σ
    have hfl : fl ≫ (X.baseChange Ω).X.hom = (X.baseChange Ω).X.hom := by
      rw [← cancel_epi (cσ X σ)]
      simp only [fl, Category.assoc, IsIso.hom_inv_id_assoc]
      rw [cσ_snd, ← Category.assoc g.hom.left, Over.w g.hom]
    let F : (X.baseChange Ω).X ⟶ (X.baseChange Ω).X := Over.homMk fl hfl
    have hg0 : (η[(X.baseChange Ω').X]).left ≫ g.hom.left = (η[(X.baseChange Ω').X]).left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    have e0 : sp ((σ : Ω ≃+* Ω') : Ω →+* Ω') ≫ (η[(X.baseChange Ω).X]).left ≫ inv (cσ X σ) =
        (η[(X.baseChange Ω').X]).left := by
      rw [← Category.assoc, ← η_cσ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have hη : η[(X.baseChange Ω).X] ≫ F = η[(X.baseChange Ω).X] := by
      apply Over.OverMorphism.ext
      show (η[(X.baseChange Ω).X]).left ≫ fl = (η[(X.baseChange Ω).X]).left
      apply (cancel_epi (sp ((σ : Ω ≃+* Ω') : Ω →+* Ω'))).mp
      simp only [fl]
      rw [← Category.assoc (η[(X.baseChange Ω).X]).left, ← Category.assoc, e0, ← Category.assoc,
        hg0, η_cσ]
    haveI := G0FibreSimple.rigidityHom Ω _ _ F hη
    refine ⟨PkgI3.AbVar.Hom.mk' F, tr_ext (X := X) (σ := σ) ?_⟩
    change (tr (X := X) (σ := σ) (PkgI3.AbVar.Hom.mk' F)).hom.left ≫ cσ X σ = g.hom.left ≫ cσ X σ
    rw [tr_left]
    show cσ X σ ≫ fl = _
    simp only [fl, IsIso.hom_inv_id_assoc]

/-- **`End(X_Ω) ≅ End(X_{Ω'})` for an `L`-isomorphism `σ : Ω ≅ Ω'`.** -/
def trEquiv : PkgI3.AbVar.End (X.baseChange Ω) ≃+* PkgI3.AbVar.End (X.baseChange Ω') :=
  RingEquiv.ofBijective (trHom (X := X) (σ := σ)) trHom_bijective

end Transport

/-! ## Rank-one idempotents of `M₂(k)` -/

section Idem

theorem idem_two {K : Type*} [Field K] (ε : Matrix (Fin 2) (Fin 2) K) (h : ε * ε = ε) (h0 : ε ≠ 0)
    (h1 : ε ≠ 1) : Matrix.trace ε = 1 ∧ ∀ y : Matrix (Fin 2) (Fin 2) K, ε * y * ε = Matrix.trace (y * ε) • ε := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have htr : ε 0 0 + ε 1 1 = 1 := by
    by_contra hne
    have hne' : ε 0 0 + ε 1 1 - 1 ≠ 0 := sub_ne_zero.mpr hne
    have hb : ε 0 1 = 0 := by
      have : ε 0 1 * (ε 0 0 + ε 1 1 - 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hne'
    have hc : ε 1 0 = 0 := by
      have : ε 1 0 * (ε 0 0 + ε 1 1 - 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hne'
    have ha : ε 0 0 * (ε 0 0 - 1) = 0 := by rw [hb] at e00; linear_combination e00
    have hd : ε 1 1 * (ε 1 1 - 1) = 0 := by rw [hb] at e11; linear_combination e11
    rcases mul_eq_zero.mp ha with ha | ha <;> rcases mul_eq_zero.mp hd with hd | hd
    · apply h0; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
    · exact hne (by linear_combination ha + hd)
    · exact hne (by linear_combination ha + hd)
    · apply h1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, hb, hc] <;>
        [linear_combination ha; linear_combination hd]
  have hdet : ε 0 0 * ε 1 1 = ε 0 1 * ε 1 0 := by linear_combination (-1 : K) * e00 + ε 0 0 * htr
  refine ⟨by simpa [Matrix.trace, Fin.sum_univ_two] using htr, fun y => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.trace, Matrix.diag,
      smul_eq_mul, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;>
    [linear_combination (-y 1 1) * hdet; linear_combination (y 0 1) * hdet;
      linear_combination (y 1 0) * hdet; linear_combination (-y 0 0) * hdet]
end Idem

end FibreSplit
end CMBranch
end HDec
