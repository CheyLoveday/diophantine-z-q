import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
import ZInQKernel.Contrib.CloudB3RC53.Companion.Disc

/-! # Discharging the unit factor in the Cai–Chen–Liu norm relations -/

noncomputable section

open NumberField Polynomial
open ZInQ.Contrib.CloudB3RC53.Splitting (pbOf discr_pbOf natDegree_quad)
open ZInQ.Contrib.CloudB3RC53.Companion (discr_mul_sq_int)
open ZInQ.Contrib.CloudB3RC53.CST (IsHeegnerForm)

namespace ZInQ.Manuscript.RC.PrintsArith

variable {K : Type} [Field K] [NumberField K]

@[simp] theorem cclUnitFactor_of_ne_one {m : ℕ} (hm : m ≠ 1) :
    cclUnitFactor K m = 1 := by simp [cclUnitFactor, hm]

/-- At a level divisible by four, the Heegner form rules out discriminants −3 and −4
by reduction modulo sixteen. -/
theorem disc_ne_exceptional_of_heegner_form {N : ℕ} {D A B C : ℤ}
    (hN : 4 ∣ N) (hform : IsHeegnerForm N D A B C) : D ≠ -3 ∧ D ≠ -4 := by
  have hA : (4 : ℤ) ∣ A :=
    (Int.natCast_dvd.mpr hN : ((4 : ℕ) : ℤ) ∣ (N : ℤ)).trans hform.2.1
  obtain ⟨k, rfl⟩ := hA
  have hsquares (b : ZMod 16) : b ^ 2 ≠ -3 ∧ b ^ 2 ≠ -4 := by decide +revert
  have hmod := congrArg (fun x : ℤ => (x : ZMod 16)) hform.2.2.1
  have h16 : (4 : ZMod 16) * 4 = 0 := by decide
  push_cast at hmod
  have hD : (B : ZMod 16) ^ 2 = (D : ZMod 16) := by
    simpa only [← mul_assoc, h16, zero_mul, sub_zero] using hmod
  constructor
  · rintro rfl
    exact (hsquares _).1 (by simpa using hD)
  · rintro rfl
    exact (hsquares _).2 (by simpa using hD)

/-- The maximal order of an imaginary quadratic field of discriminant below −4
has only the units coming from `ℤ`. -/
theorem cclUnitFactor_eq_one_of_discr_lt (hK : Module.finrank ℚ K = 2)
    (hdisc : discr K < -4) : cclUnitFactor K 1 = 1 := by
  classical
  let _ : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  simp only [cclUnitFactor, ite_true, Subgroup.index_eq_one, eq_top_iff]
  intro U _
  let z : 𝓞 K := U
  have hnUnit : IsUnit (Algebra.norm ℤ z) := U.isUnit.map (Algebra.norm ℤ)
  have hzrat : (z : K) ∈ (algebraMap ℚ K).range := by
    by_contra hz
    let t : ℤ := -Algebra.trace ℤ (𝓞 K) z
    let n : ℤ := Algebra.norm ℤ z
    have hmonic : (X ^ 2 + C (t : ℚ) * X + C (n : ℚ) : ℚ[X]).Monic := by
      rw [Monic, leadingCoeff, natDegree_quad]
      norm_num only [coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C, ite_true, ite_false,
        Nat.reduceEqDiff, add_zero]
    have hroot : aeval (z : K) (X ^ 2 + C (t : ℚ) * X + C (n : ℚ) : ℚ[X]) = 0 := by
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C,
        t, n, Int.cast_neg, Algebra.coe_trace_int, Algebra.coe_norm_int, map_neg, neg_mul]
      simpa only [sub_eq_add_neg, Algebra.smul_def] using
        Algebra.IsQuadraticExtension.sq_sub_trace_smul_add_norm_eq_zero ℚ (z : K)
    have hzint : IsIntegral ℚ (z : K) := Algebra.IsIntegral.isIntegral _
    have hmin : minpoly ℚ (z : K) = X ^ 2 + C (t : ℚ) * X + C (n : ℚ) :=
      (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzint) hmonic
        (minpoly.dvd ℚ (z : K) hroot)
        ((natDegree_quad t n).trans_le ((minpoly.two_le_natDegree_iff hzint).2 hz))).symm
    obtain ⟨i, hi⟩ := discr_mul_sq_int hK hmin
    have hi0 : i ≠ 0 := by
      rintro rfl
      have hne := Algebra.discr_not_zero_of_basis ℚ ((pbOf hK hmin).basis)
      rw [discr_pbOf, hi] at hne
      simp at hne
    have hi1 : 1 ≤ i ^ 2 := by
      have := sq_pos_of_ne_zero hi0
      omega
    have hle : discr K * i ^ 2 ≤ discr K := by
      simpa using mul_le_mul_of_nonpos_left hi1 (show discr K ≤ 0 by omega)
    rcases Int.isUnit_iff.mp hnUnit with hn | hn <;>
      change n = _ at hn <;> rw [hn] at hi <;> nlinarith [sq_nonneg t]
  obtain ⟨q, hq⟩ := hzrat
  have hqint : IsIntegral ℤ q := (isIntegral_algebraMap_iff (B := K)).mp (by
    rw [hq]
    exact z.isIntegral_coe)
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
  have haz : algebraMap ℚ K (a : ℚ) = (z : K) := by
    simpa using (congrArg (algebraMap ℚ K) ha).trans hq
  have hnorm : Algebra.norm ℤ z = a ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, ← haz, Algebra.norm_algebraMap, hK, Int.cast_pow]
  have haUnit : IsUnit a := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (hnorm ▸ hnUnit)
  obtain ⟨v, hv⟩ := haUnit
  refine ⟨v, Units.ext (RingOfIntegers.ext ?_)⟩
  change ((v : ℤ) : K) = (z : K)
  rw [hv, ← haz]
  simp

/-- The level argument supplies the unit check independently of the choice of companion. -/
theorem cclUnitFactor_eq_one_of_heegner_level (hK : Module.finrank ℚ K = 2)
    (hdisc : discr K < 0) {N : ℕ} {A B C : ℤ}
    (hN : 4 ∣ N) (hform : IsHeegnerForm N (discr K) A B C) :
    cclUnitFactor K 1 = 1 := by
  obtain ⟨h3, h4⟩ := disc_ne_exceptional_of_heegner_form hN hform
  have habs := abs_discr_gt_two (K := K) (by omega)
  rw [abs_of_neg hdisc] at habs
  exact cclUnitFactor_eq_one_of_discr_lt hK (by omega)

theorem HeegnerPointData.NormRelationsWithUnits.toNormRelations {E : WeierstrassCurve ℚ}
    {D : HeegnerPointData E} (h : D.NormRelationsWithUnits K) (hu : cclUnitFactor K 1 = 1) :
    D.NormRelations := by
  constructor
  · intro d ℓ hadm hinert
    simpa only [hu, one_nsmul] using h.1 d ℓ hadm hinert
  · intro d q hadm hsplit
    simpa only [hu, one_nsmul] using h.2 d q hadm hsplit

/-- The existing additive transport can use the normalized equations on the same
anchored datum. -/
theorem CCLThm2_15AppliedWithUnits.exists_normRelations {E : WeierstrassCurve ℚ}
    {Anchor : HeegnerPointData E → Prop} (h : CCLThm2_15AppliedWithUnits E K Anchor)
    (hu : cclUnitFactor K 1 = 1) :
    ∃ D : HeegnerPointData E, D.NormRelations ∧ Anchor D := by
  obtain ⟨D, hD, hA⟩ := h
  exact ⟨D, hD.toNormRelations hu, hA⟩

end ZInQ.Manuscript.RC.PrintsArith
