import ZInQKernel.Contrib.OneProof.RC.O7Actual.Arithmetic

/-! The support-to-embedding map and the stabilizer on the actual left order. -/

noncomputable section

open scoped Quaternion NumberField TensorProduct
open NumberField

namespace ZInQ.Manuscript.RC.O7Actual

open Eichler Visibility

/-- The quadratic field is presented by its square root and its integral
basis. The integral basis result for the discriminant in the filter is a
separate arithmetic obligation. -/
structure QuadraticBasis (F : Type*) [Field F] [NumberField F] (disc : ℤ) where
  model : QuadraticAlgebra ℚ (disc : ℚ) 0 ≃ₐ[ℚ] F
  half_integral : IsIntegral ℤ ((1 + model QuadraticAlgebra.omega) / 2)
  spans : ∀ y : 𝓞 F, ∃ i j : ℤ,
    (y : F) = i + j * ((1 + model QuadraticAlgebra.omega) / 2)

/-- The maximal-order version of an optimal embedding with prescribed
image of the square root. -/
def OptimalAt {a b : ℚ} (R : Order a b) {F : Type*} [Field F] [NumberField F]
    {disc : ℤ} (Q : QuadraticBasis F disc) (x : B a b) : Prop :=
  ∃ ι : F →ₐ[ℚ] B a b, ι (Q.model QuadraticAlgebra.omega) = x ∧
    ∀ y : F, ι y ∈ R.ring ↔ IsIntegral ℤ y

/-- Tex 9123–9134: on the trace-zero norm sphere, half-integrality in the
actual left order is equivalent to the prescribed optimal embedding. -/
theorem halfIntegral_iff_optimal {a b : ℚ} (R : Order a b)
    {F : Type*} [Field F] [NumberField F] {m D hstar : ℤ}
    (Q : QuadraticBasis F (D * hstar)) (hm : hstar = -m)
    {x : B a b} (hx : x.re = 0) (hn : nrd x = ((m * D : ℤ) : ℚ)) :
    HalfIntegral R x ↔ OptimalAt R Q x := by
  let α : F := (1 + Q.model QuadraticAlgebra.omega) / 2
  have halpha : 2 * α - 1 = Q.model QuadraticAlgebra.omega := by dsimp [α]; ring
  have hsq : x * x = algebraMap ℚ (B a b) ((D * hstar : ℤ) : ℚ) := by
    rw [Int.cast_mul]
    rw [Int.cast_mul] at hn
    exact (nrd_eq_mul_iff hx (m : ℚ) (D : ℚ) (hstar : ℚ) (by exact_mod_cast hm)).mp hn
  constructor
  · rintro ⟨t, ht⟩
    let f : QuadraticAlgebra ℚ ((D * hstar : ℤ) : ℚ) 0 →ₐ[ℚ] B a b :=
      QuadraticAlgebra.lift ⟨x, by simpa [Algebra.algebraMap_eq_smul_one] using hsq⟩
    let ι : F →ₐ[ℚ] B a b := f.comp Q.model.symm.toAlgHom
    have hι : ι (Q.model QuadraticAlgebra.omega) = x := by simp [ι, f]
    have he : 2 * ι α - 1 = x := by
      rw [← hι, ← halpha]
      simp only [map_sub, map_mul, map_ofNat, map_one]
    have he' : ι α = (t : B a b) := by
      rw [← ht] at he
      have he'' := sub_left_inj.mp he
      have htwo : (2 : B a b) = algebraMap ℚ (B a b) 2 := by norm_num
      rw [htwo, ← Algebra.smul_def, ← Algebra.smul_def] at he''
      exact (smul_right_injective (B a b) (show (2 : ℚ) ≠ 0 by norm_num)) he''
    refine ⟨ι, hι, optimal_of_maps_integers R ι (fun y => ?_)⟩
    obtain ⟨i, j, hij⟩ := Q.spans y
    change (y : F) = i + j * α at hij
    rw [hij, map_add, map_mul, map_intCast, map_intCast, he']
    exact R.ring.add_mem (intCast_mem R.ring i) (R.ring.mul_mem (intCast_mem R.ring j) t.prop)
  · rintro ⟨ι, hi, hopt⟩
    refine ⟨⟨ι α, (hopt α).2 Q.half_integral⟩, ?_⟩
    rw [← hi, ← halpha]
    simp only [map_sub, map_mul, map_ofNat, map_one]

/-- Tex 9123–9134: exact nonzero support in terms of optimal embeddings,
once the local weights have been related to the half-integral generator. -/
theorem supp_iff_optimal_on_sphere {O : Type*} [CommRing O] {a b : ℚ} {R : Order a b}
    (S : ThetaStage O a b) (z : S.X) {F : Type*} [Field F] [NumberField F] {m D hstar : ℤ}
    (Q : QuadraticBasis F (D * hstar)) (hm : hstar = -m)
    {x : B a b} (hx : x.re = 0) (hn : nrd x = ((m * D : ℤ) : ℚ))
    (hsupport : S.f z x ≠ 0 ↔ HalfIntegral R x) :
    x ∈ S.supp z ((m * D : ℤ) : ℚ) ↔ OptimalAt R Q x :=
  (show _ ↔ S.f z x ≠ 0 from ⟨fun h => h.2.2, fun h => ⟨hx, hn, h⟩⟩).trans
    (hsupport.trans (halfIntegral_iff_optimal R Q hm hx hn))

/-- GLUE, UNVERIFIED: Voight Proposition 14.6.7, (v) ⇒ (iii), in exactly
the implication cited at tex 9150–9155, specialized to the explicitly
ramified rational algebra. The inputs are local field conditions at the
two ramified places; the output is a rational embedding. -/
def Voight1467VToIII (ell : ℕ) [Fact ell.Prime] (F : Type*) [Field F] [NumberField F] : Prop :=
  AppF.RamifiedExactlyAtEll0Infty ell (-1) (-(ell : ℚ)) →
    IsField (ℝ ⊗[ℚ] F) → IsField (ℚ_[ell] ⊗[ℚ] F) →
      Nonempty (F →ₐ[ℚ] B (-1) (-(ell : ℚ)))

/-- Tex 9297–9300: the actual unit group of a chosen ideal class has
reduced norm one. -/
theorem classG_norm_one {a b : ℚ} {R : Order a b} (ha : a < 0) (hb : b < 0)
    (z : ClassSet R) (u : classG ha hb z) :
    nrd ((u : (B a b)ˣ) : B a b) = 1 := by
  obtain ⟨v, hv⟩ := u.prop
  rw [← hv]
  exact (classOrder ha hb z).nrd_unit ha hb v

/-- On-the-spot (c), tex 9308–9309. The centralizer of a nonzero
trace-zero quaternion in the definite algebra is its rational span with 1. -/
theorem centralizer_span {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    {x y : B a b} (hx : x.re = 0) (hx0 : x ≠ 0) (h : Commute y x) :
    ∃ t : ℚ, y = algebraMap ℚ (B a b) y.re + t • x := by
  have hI := congrArg QuaternionAlgebra.imI h.eq
  have hJ := congrArg QuaternionAlgebra.imJ h.eq
  have hK := congrArg QuaternionAlgebra.imK h.eq
  simp only [QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    zero_mul, add_zero] at hI hJ hK
  have eJK : y.imJ * x.imK = y.imK * x.imJ := by
    apply mul_left_cancel₀ hb
    linear_combination -(1 / 2 : ℚ) * hI
  have eIK : y.imI * x.imK = y.imK * x.imI := by
    apply mul_left_cancel₀ ha
    linear_combination (1 / 2 : ℚ) * hJ
  have eIJ : y.imI * x.imJ = y.imJ * x.imI := by
    linear_combination (1 / 2 : ℚ) * hK
  have finish (t : ℚ) (hI : y.imI = t * x.imI) (hJ : y.imJ = t * x.imJ)
      (hK : y.imK = t * x.imK) : y = algebraMap ℚ (B a b) y.re + t • x := by
    apply QuaternionAlgebra.ext
    · simp [QuaternionAlgebra.algebraMap_eq, hx, smul_eq_mul]
    · simpa [QuaternionAlgebra.algebraMap_eq, smul_eq_mul] using hI
    · simpa [QuaternionAlgebra.algebraMap_eq, smul_eq_mul] using hJ
    · simpa [QuaternionAlgebra.algebraMap_eq, smul_eq_mul] using hK
  have eqdiv (r s u v : ℚ) (hv : v ≠ 0) (h : r * v = u * s) :
      r = u / v * s := by
    apply mul_right_cancel₀ hv
    rw [h, mul_right_comm, div_mul_cancel₀ _ hv]
  by_cases hI0 : x.imI = 0
  · by_cases hJ0 : x.imJ = 0
    · have hK0 : x.imK ≠ 0 := fun h => hx0 (QuaternionAlgebra.ext hx hI0 hJ0 h)
      exact ⟨y.imK / x.imK, finish _ (eqdiv _ _ _ _ hK0 eIK)
        (eqdiv _ _ _ _ hK0 eJK) (div_mul_cancel₀ _ hK0).symm⟩
    · exact ⟨y.imJ / x.imJ, finish _ (eqdiv _ _ _ _ hJ0 eIJ)
        (div_mul_cancel₀ _ hJ0).symm (eqdiv _ _ _ _ hJ0 eJK.symm)⟩
  · exact ⟨y.imI / x.imI, finish _ (div_mul_cancel₀ _ hI0).symm
      (eqdiv _ _ _ _ hI0 eIJ.symm) (eqdiv _ _ _ _ hI0 eIK.symm)⟩

/-- Tex 9308–9309: the reduced norm on the image of the quadratic basis
is the binary form `i² + i j - k j²`. -/
theorem basis_norm {a b : ℚ} {x : B a b} (hx : x.re = 0) {k : ℤ}
    (hn : nrd x = -(4 * (k : ℚ) + 1)) (i j : ℤ) :
    nrd (algebraMap ℚ (B a b) ((i : ℚ) + (j : ℚ) / 2) + ((j : ℚ) / 2) • x) =
      ((QuadraticAlgebra.norm (⟨i, j⟩ : QuadraticAlgebra ℤ k 1) : ℤ) : ℚ) := by
  rw [nrd_apply, QuaternionAlgebra.algebraMap_eq]
  simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
    QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul, hx, mul_zero,
    zero_add, add_zero, QuadraticAlgebra.norm_def]
  push_cast
  rw [nrd_apply, hx] at hn
  linear_combination (((j : ℚ) / 2) ^ 2) * hn

/-- Tex 9308–9309: an order unit commuting with a supported optimal
embedding acts by one of the two signs. -/
theorem optimal_commuting_unit_sign {a b : ℚ} (R : Order a b) (ha : a < 0) (hb : b < 0)
    {F : Type*} [Field F] [NumberField F] {disc k : ℤ} (Q : QuadraticBasis F disc)
    (hk : disc = 4 * k + 1) (hd : disc < 0) (h8 : disc % 8 = 1)
    {x : B a b} (hx : x.re = 0) (hn : nrd x = -(disc : ℚ))
    (hopt : OptimalAt R Q x) (u : (B a b)ˣ) (hu : u ∈ R.G)
    (hcomm : Commute (u : B a b) x) :
    (u : B a b) = 1 ∨ (u : B a b) = -1 := by
  obtain ⟨ι, hroot, hι⟩ := hopt
  have hx0 : x ≠ 0 := by
    intro he
    have : (disc : ℚ) < 0 := by exact_mod_cast hd
    simp [he, nrd] at hn
    linarith
  obtain ⟨t, ht⟩ := centralizer_span ha.ne hb.ne hx hx0 hcomm
  let y : F := algebraMap ℚ F (u : B a b).re + t • Q.model QuadraticAlgebra.omega
  have hy : ι y = (u : B a b) := by
    rw [ht]
    simp only [y, map_add, AlgHom.commutes, map_smul, hroot]
  obtain ⟨v, hv⟩ := hu
  have hyInt : IsIntegral ℤ y := (hι y).mp (hy ▸ hv ▸ v.val.prop)
  obtain ⟨i, j, hij⟩ := Q.spans ⟨y, hyInt⟩
  change y = _ at hij
  let α : F := (1 + Q.model QuadraticAlgebra.omega) / 2
  have hα : ι α = algebraMap ℚ (B a b) (1 / 2) + (1 / 2 : ℚ) • x := by
    have hh : α = algebraMap ℚ F (1 / 2) + (1 / 2 : ℚ) • Q.model QuadraticAlgebra.omega := by
      simp [α, Algebra.smul_def]
      ring
    rw [hh, map_add, AlgHom.commutes, map_smul, hroot]
  have hform : (u : B a b) =
      algebraMap ℚ (B a b) ((i : ℚ) + (j : ℚ) / 2) + ((j : ℚ) / 2) • x := by
    rw [← hy, hij, map_add, map_mul, map_intCast, map_intCast]
    change _ + _ * ι α = _
    rw [hα, ← map_intCast (algebraMap ℚ (B a b)), ← map_intCast (algebraMap ℚ (B a b)),
      ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one]
    module
  have hvnorm := R.nrd_unit ha hb v
  rw [hv, hform, basis_norm hx (by push_cast [hk] at hn; exact hn)] at hvnorm
  have hqn : QuadraticAlgebra.norm (⟨i, j⟩ : QuadraticAlgebra ℤ k 1) = 1 := by
    exact_mod_cast hvnorm
  rcases quadratic_norm_one (quadratic_parameter_le hd h8 hk) _ hqn with h | h
  · have hi : i = 1 := congrArg QuadraticAlgebra.re h
    have hj : j = 0 := congrArg QuadraticAlgebra.im h
    left
    simp [hform, hi, hj]
  · have hi : i = -1 := congrArg QuadraticAlgebra.re h
    have hj : j = 0 := congrArg QuadraticAlgebra.im h
    right
    simp [hform, hi, hj]

end ZInQ.Manuscript.RC.O7Actual
