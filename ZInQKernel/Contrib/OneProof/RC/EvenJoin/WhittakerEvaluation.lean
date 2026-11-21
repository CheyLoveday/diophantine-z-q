import ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerColumns
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion

/-! Finite Whittaker evaluations on the matrices used at coefficient one
(tex 9841–9856). On the test locus one can use the rational slash
representative and a horizontal Fourier integral. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open Function HeckeRing.GL2 Matrix ModularForm O12 O12Local UpperHalfPlane
open scoped Manifold ModularForm

set_option Elab.async false

section ComplexEvaluation

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    [hmod : ModularFormClass F Γ 2] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F)
variable (n : PosIndex) (b : Fin n.val)

private abbrev whittakerSlash : ℍ → ℂ :=
  (f : ℍ → ℂ) ∣[(2 : ℤ)] (upperTriRep n.val b : GL (Fin 2) ℚ)

include hΓ in
private theorem whittakerSlash_hasSum (τ : ℍ) :
    HasSum (fun m : ℕ => ((qExpansion 1 f).coeff m / (n.val : ℂ) *
      Periodic.qParam (n.val : ℝ) (b.val : ℂ) ^ m) •
      Periodic.qParam (n.val : ℝ) (τ : ℂ) ^ m) (whittakerSlash f n b τ) := by
  let : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  rw [whittakerSlash, slash_upperTriRep_apply]
  apply (HasSum.mul_left _ (UpperHalfPlane.hasSum_qExpansion (h := 1) one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep n.val b) • τ))).congr_fun
  intro m
  rw [qParam_one_upperTriRep_smul, mul_pow]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

include hΓ in
private theorem whittakerSlash_periodic :
    Periodic (whittakerSlash f n b ∘ ofComplex) (n.val : ℝ) := by
  intro z
  have hp := TauCeti.UpperHalfPlane.periodic_qParam_comp_ofComplex
    (h := (n.val : ℝ)) (Nat.cast_ne_zero.mpr n.property) z
  exact ((whittakerSlash_hasSum hΓ f n b (ofComplex (z + (n.val : ℝ)))).congr_fun
    (fun m => by
      let c := (qExpansion 1 f).coeff m / (n.val : ℂ) *
        Periodic.qParam (n.val : ℝ) (b.val : ℂ) ^ m
      exact congrArg (fun x : ℂ => c • x ^ m) hp.symm)).unique
    (whittakerSlash_hasSum hΓ f n b (ofComplex z))

include hmod in
private theorem whittakerSlash_holo : MDiff (whittakerSlash f n b) := by
  rw [whittakerSlash, ModularForm.rat_slash]
  exact (ModularFormClass.holo (Γ := Γ) (k := 2) f).slash 2 _

include hΓ in
private theorem whittakerSlash_bounded : IsBoundedAtImInfty (whittakerSlash f n b) :=
  isBoundedAtImInfty_of_hasSum_qExpansion (Nat.cast_pos.mpr (Nat.pos_of_ne_zero n.property))
    (whittakerSlash_hasSum hΓ f n b)

/-- The normalized horizontal Fourier integral after adelic reduction by the
rational representative with inverse proportional to `upperTriRep n b`.
The finite unipotent part of the domain has volume `1/n`. At height one
the reciprocal `q`-power divides out the archimedean Whittaker value and
supplies the character `exp(-2πix)`. -/
def whittakerIntegral : ℂ :=
  1 / (n.val : ℂ) * ∫ x in (0 : ℝ)..(n.val : ℝ),
    1 / Periodic.qParam (n.val : ℝ) (x + Complex.I) ^ n.val *
      whittakerSlash f n b ⟨x + Complex.I, by simp⟩

include hΓ in
/-- Compute the actual integral on the rational representative. The
integral translation acts trivially on the frequency `n`. -/
theorem whittakerIntegral_eq :
    whittakerIntegral f n b = (qExpansion 1 f).coeff n.val / (n.val : ℂ) := by
  have hn : (0 : ℝ) < n.val := Nat.cast_pos.mpr (Nat.pos_of_ne_zero n.property)
  have hInt := qExpansion_coeff_eq_intervalIntegral hn
    (whittakerSlash_periodic hΓ f n b) (whittakerSlash_holo f n b)
    (whittakerSlash_bounded hΓ f n b) n.val (t := 1) one_pos
  have hnth := TauCeti.UpperHalfPlane.qExpansion_coeff_unique hn
    (analyticAt_cuspFunction_zero hn (whittakerSlash_periodic hΓ f n b)
      (whittakerSlash_holo f n b) (whittakerSlash_bounded hΓ f n b))
    (whittakerSlash_hasSum hΓ f n b) n.val
  have hb : Periodic.qParam (n.val : ℝ) (b.val : ℂ) ^ n.val = 1 := by
    rw [← mul_one (n.val : ℝ), TauCeti.Periodic.qParam_nat_mul_pow n.property]
    unfold Periodic.qParam
    rw [Complex.ofReal_one, div_one, mul_comm, Complex.exp_nat_mul_two_pi_mul_I]
  calc
    whittakerIntegral f n b = (qExpansion (n.val : ℝ) (whittakerSlash f n b)).coeff n.val := by
      unfold whittakerIntegral
      simpa only [Complex.ofReal_natCast, Complex.ofReal_one, one_mul, UpperHalfPlane.coe_I] using hInt.symm
    _ = _ := by simpa only [hb, mul_one] using hnth.symm

end ComplexEvaluation

/-- Inverse rational translations are represented modulo the positive
width. The difference is an integral right unipotent. -/
def whittakerOffset (n : PosIndex) (t : ℤ) : Fin n.val :=
  ⟨((-t) % (n.val : ℤ)).toNat, by
    have h := Int.emod_nonneg (-t) (Int.natCast_ne_zero.mpr n.property)
    have h' := Int.emod_lt_of_pos (-t) (Int.natCast_pos.mpr (Nat.pos_of_ne_zero n.property))
    omega⟩

private theorem whittakerOffset_zero (n : PosIndex) : (whittakerOffset n 0).val = 0 := by
  simp [whittakerOffset]

private theorem whittakerOffset_add (n : PosIndex) (t : ℤ) :
    ∃ c : ℤ, t + ((whittakerOffset n t).val : ℤ) = (n.val : ℤ) * c := by
  refine ⟨-((-t) / (n.val : ℤ)), ?_⟩
  simp only [whittakerOffset, Int.toNat_of_nonneg
    (Int.emod_nonneg (-t) (Int.natCast_ne_zero.mpr n.property)), Int.mul_neg]
  have h := Int.emod_add_ediv_mul (-t) (n.val : ℤ)
  rw [mul_comm ((-t) / (n.val : ℤ))] at h
  omega

private theorem upper_level_of_norm {q : ℕ} [Fact q.Prime] (m : ℕ)
    {d : ℚ_[q]ˣ} {x : ℚ_[q]} (hd : ‖(d : ℚ_[q])‖ = 1) (hx : ‖x‖ ≤ 1) :
    atK1 q m (upper d 1 x) := by
  refine ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [upper, hd, hx]
  · simp [upper, det_fin_two, hd]
  · simp [upper]
  · simp [upper]

/-- The local components of a test matrix reduce by the indicated
rational matrix into the level group, including after the unipotent
translation by `n * u` on the integration domain. The away multiplier
is allowed to be any power of the tested prime. -/
theorem whittakerLocalReduction {p q : ℕ} [Fact q.Prime] (hp : p.Prime)
    (n : PosIndex) (t : ℤ) (ht : t = 0 ∨ n.val = p) (j : ℤ)
    (u : ℚ_[q]) (hu : ‖u‖ ≤ 1) (m : ℕ) :
    ∃ k : GL (Fin 2) ℚ_[q], atK1 q m k ∧
      !![(n.val : ℚ_[q]), -((whittakerOffset n t).val : ℚ_[q]); 0, 1] *
        (k : Matrix (Fin 2) (Fin 2) ℚ_[q]) =
      !![if q = p then (n.val : ℚ_[q]) else (n.val : ℚ_[q]) * (p : ℚ_[q]) ^ j,
        (if q = p then (t : ℚ_[q]) else 0) + (n.val : ℚ_[q]) * u; 0, 1] := by
  let b : ℕ := (whittakerOffset n t).val
  by_cases hq : q = p
  · obtain ⟨c, hc⟩ := whittakerOffset_add n t
    have hcast : (t : ℚ_[q]) + (b : ℚ_[q]) = (n.val : ℚ_[q]) * (c : ℚ_[q]) := by
      exact_mod_cast hc
    refine ⟨upper 1 1 ((c : ℚ_[q]) + u), upper_level_of_norm m (by simp) ?_, ?_⟩
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (IsUltrametricDist.norm_intCast_le_one _ _) hu)
    simp only [ite_eq_left hq]
    change !![(n.val : ℚ_[q]), -(b : ℚ_[q]); 0, 1] *
      !![1, (c : ℚ_[q]) + u; 0, 1] = _
    rw [Matrix.mul_fin_two]
    simp only [mul_one, zero_mul, mul_zero, zero_add, add_zero]
    have he : (n.val : ℚ_[q]) * ((c : ℚ_[q]) + u) + -(b : ℚ_[q]) =
        (t : ℚ_[q]) + (n.val : ℚ_[q]) * u := by
      rw [mul_add, ← hcast]
      ring
    rw [he]
  · have hqnorm : ‖(p : ℚ_[q])‖ = 1 :=
      Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes Fact.out hp).mpr hq)
    let d : ℚ_[q]ˣ := (Units.mk0 (p : ℚ_[q]) (Nat.cast_ne_zero.mpr hp.ne_zero)) ^ j
    have hd : ‖(d : ℚ_[q])‖ = 1 := by simp [d, norm_zpow, hqnorm]
    have hbn : ‖(b : ℚ_[q]) / (n.val : ℚ_[q])‖ ≤ 1 := by
      rcases ht with rfl | hn
      · simp [b, whittakerOffset_zero]
      · rw [norm_div, hn, hqnorm, div_one]
        exact IsUltrametricDist.norm_natCast_le_one _ _
    refine ⟨upper d 1 ((b : ℚ_[q]) / (n.val : ℚ_[q]) + u),
      upper_level_of_norm m hd ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hbn hu)), ?_⟩
    simp only [ite_eq_right hq]
    change !![(n.val : ℚ_[q]), -(b : ℚ_[q]); 0, 1] *
      !![(d : ℚ_[q]), (b : ℚ_[q]) / (n.val : ℚ_[q]) + u; 0, 1] = _
    rw [Matrix.mul_fin_two]
    simp only [d, Units.val_zpow_eq_zpow_val, Units.val_mk0, mul_one, zero_mul, mul_zero,
      zero_add, add_zero]
    have he : (n.val : ℚ_[q]) * ((b : ℚ_[q]) / (n.val : ℚ_[q]) + u) + -(b : ℚ_[q]) =
        (n.val : ℚ_[q]) * u := by
      have hn : (n.val : ℚ_[q]) ≠ 0 := Nat.cast_ne_zero.mpr n.property
      rw [mul_add, ← mul_div_assoc, mul_div_cancel_left₀ _ hn]
      ring
    rw [he]

section FiniteEvaluation

variable {K I F : Type} [Field K] [CharZero K] [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [ModularFormClass F Γ 2]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : I → F)
    (κ : K →+* ℂ) (a : I → PosIndex → K)
    (ha : ∀ i n, κ (a i n) = (qExpansion 1 (f i)).coeff n.val)
    {p : ℕ} (hp : p ≠ 0)

private def rationalDiagonal (n : PosIndex) : ℚˣ :=
  Units.mk0 (n.val : ℚ) (Nat.cast_ne_zero.mpr n.property)

private def translatedDiagonal (n : PosIndex) (t : ℤ) : Matrix (Fin 2) (Fin 2) K :=
  !![(n.val : K), (t : K); 0, 1]

private def isWhittakerTest (g : Matrix (Fin 2) (Fin 2) K) (z : ℚˣ)
    (n : PosIndex) (t : ℤ) : Prop :=
  g = translatedDiagonal n t ∧ (t = 0 ∨ n.val = p) ∧
    z * (rationalDiagonal n)⁻¹ ∈ Subgroup.zpowers (rationalDiagonal ⟨p, hp⟩)

private theorem isWhittakerTest_index {g : Matrix (Fin 2) (Fin 2) K} {z : ℚˣ}
    {n m : PosIndex} {t s : ℤ} (hn : isWhittakerTest hp g z n t)
    (hm : isWhittakerTest hp g z m s) : n = m := by
  apply Subtype.ext
  have e : (n.val : K) = (m.val : K) := by
    simpa only [translatedDiagonal, Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons]
      using congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) (hn.1.symm.trans hm.1)
  exact Nat.cast_injective e

omit [CharZero K] in
private theorem isWhittakerTest_away (g : Matrix (Fin 2) (Fin 2) K) (z : ℚˣ)
    (n : PosIndex) (t : ℤ) :
    isWhittakerTest hp g (z * rationalDiagonal ⟨p, hp⟩) n t ↔
      isWhittakerTest hp g z n t := by
  unfold isWhittakerTest
  rw [mul_right_comm z,
    Subgroup.mul_mem_cancel_right _ (Subgroup.mem_zpowers _)]

include hΓ ha in
omit [CharZero K] in
private theorem whittakerIntegral_lifts (i : I) (n : PosIndex) (t : ℤ) :
    ∃ y : K, κ y = whittakerIntegral (f i) n (whittakerOffset n t) := by
  refine ⟨a i n / (n.val : K), ?_⟩
  rw [whittakerIntegral_eq hΓ, map_div₀, map_natCast, ha]

/-- The finite test values over the placed field. On the test locus the
value is the unique lift of the classical integral. The inherited
interface uses all matrices, so extend by zero off this locus. -/
private def finiteWhittaker (i : I) (g : Matrix (Fin 2) (Fin 2) K) (z : ℚˣ) : K := by
  classical
  exact if h : ∃ n t, isWhittakerTest hp g z n t then
    (whittakerIntegral_lifts hΓ f κ a ha i h.choose h.choose_spec.choose).choose
  else 0

private theorem finiteWhittaker_eq (i : I) {g : Matrix (Fin 2) (Fin 2) K} {z : ℚˣ}
    {n : PosIndex} {t : ℤ} (h : isWhittakerTest hp g z n t) :
    finiteWhittaker hΓ f κ a ha hp i g z = a i n / (n.val : K) := by
  classical
  have hh : ∃ m s, isWhittakerTest hp g z m s := ⟨n, t, h⟩
  rw [finiteWhittaker, dite_eq_left hh]
  have he := isWhittakerTest_index hp hh.choose_spec.choose_spec h
  apply κ.injective
  rw [(whittakerIntegral_lifts hΓ f κ a ha i hh.choose hh.choose_spec.choose).choose_spec,
    whittakerIntegral_eq hΓ, he, map_div₀, map_natCast, ha]

private theorem finiteWhittaker_away (i : I) (g : Matrix (Fin 2) (Fin 2) K) (z : ℚˣ) :
    finiteWhittaker hΓ f κ a ha hp i g (z * rationalDiagonal ⟨p, hp⟩) =
      finiteWhittaker hΓ f κ a ha hp i g z := by
  classical
  by_cases h : ∃ n t, isWhittakerTest hp g z n t
  · obtain ⟨n, t, h⟩ := h
    rw [finiteWhittaker_eq hΓ f κ a ha hp i ((isWhittakerTest_away hp g z n t).mpr h),
      finiteWhittaker_eq hΓ f κ a ha hp i h]
  · have h' : ¬ ∃ n t, isWhittakerTest hp g (z * rationalDiagonal ⟨p, hp⟩) n t := by
      rintro ⟨n, t, ht⟩
      exact h ⟨n, t, (isWhittakerTest_away hp g z n t).mp ht⟩
    simp [finiteWhittaker, h, h']

/-- Realize the finite Whittaker values column by column from the actual
classical forms, with coefficients transported through their embedding. -/
def whittakerColumnsOfForms : WhittakerColumnValues hp a where
  Away := ℚˣ
  away := rationalDiagonal
  away_one := by apply Units.ext; simp [rationalDiagonal]
  W := finiteWhittaker hΓ f κ a ha hp
  fourier i n := by
    apply finiteWhittaker_eq hΓ f κ a ha hp i (n := n) (t := 0)
    simp [isWhittakerTest, translatedDiagonal]
  integral_translation i b := by
    have h (t : ℤ) : isWhittakerTest hp (translatedDiagonal ⟨p, hp⟩ t : Matrix (Fin 2) (Fin 2) K)
        1 ⟨p, hp⟩ t := by
      refine ⟨rfl, Or.inr rfl, ?_⟩
      simpa only [one_mul] using
        (Subgroup.zpowers (rationalDiagonal ⟨p, hp⟩)).inv_mem (Subgroup.mem_zpowers _)
    rw [show (!![1, (b.val : K); 0, 1] * !![(p : K), 0; 0, 1]) =
      translatedDiagonal ⟨p, hp⟩ (b.val : ℤ) by simp [translatedDiagonal]]
    rw [finiteWhittaker_eq hΓ f κ a ha hp i (h b.val)]
    simpa only [translatedDiagonal, Int.cast_zero] using
      (finiteWhittaker_eq hΓ f κ a ha hp i (h 0)).symm
  right_away := finiteWhittaker_away hΓ f κ a ha hp

end FiniteEvaluation

end ZInQ.Manuscript.RC.EvenJoin
