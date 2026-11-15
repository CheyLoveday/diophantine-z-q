import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.TYZGenus.ShimuraFricke
import ZInQKernel.Contrib.TYZGenus.ShimuraTheta
import ZInQKernel.Contrib.TYZGenus.ShimuraThetaDup

/-! hx-used, scratch: the eta route (hCM + one explicit identity ⇒ the level-32 instances of
`ShimuraReciprocityModFn`). Part 1: the lattices `⟨1/M, τ_Q⟩` in `K`. -/

noncomputable section

set_option maxRecDepth 20000

namespace X0EtaRoute

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise
open T5Glue

variable {m : ℕ} [NeZero m]

/-- `⟨1/M, τ_Q⟩ ⊂ ℂ`. -/
def latM {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) (M : ℕ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {1 / (M : ℂ), Q.tau}

/-- `1/M ∈ K`. -/
def invK (m M : ℕ) [NeZero m] : QNeg m := algebraMap ℚ (QNeg m) (1 / (M : ℚ))

theorem kappa_invK (M : ℕ) : kappa m (invK m M) = 1 / (M : ℂ) := by
  rw [invK, kappa_rat]; push_cast; rfl

theorem preimage_latM_eq_span {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D)
    (M : ℕ) {t : QNeg m} (ht : kappa m t = Q.tau) :
    kappa m ⁻¹' (latM Q M : Set ℂ) = (Submodule.span ℤ {invK m M, t} : Set (QNeg m)) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe, latM, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, kappa_injective ?_⟩
    simp only [zsmul_eq_mul] at hab ⊢
    rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht, kappa_invK, ← hab]
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, b, ?_⟩
    simp only [zsmul_eq_mul]
    rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht, kappa_invK]

theorem latM_subset_range {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D)
    (M : ℕ) : (latM Q M : Set ℂ) ⊆ Set.range (kappa m) := by
  obtain ⟨t, ht⟩ := exists_kappa_tau (m := m) hD Q
  intro z hz
  rw [SetLike.mem_coe, latM, Submodule.mem_span_pair] at hz
  obtain ⟨a, b, rfl⟩ := hz
  refine ⟨(a : QNeg m) * invK m M + (b : QNeg m) * t, ?_⟩
  rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht, kappa_invK]
  simp [zsmul_eq_mul]

/-- **`K ∩ 𝔟̂ = 𝔟` for `𝔟 = κ⁻¹⟨1/M, τ_Q⟩`** (`n = 2c₀`, `d = 2AM`), as `latHat_inter_heegner`. -/
theorem latHat_inter_latM (hsq : Squarefree m) {f : ℕ} [NeZero f] {D : ℤ} (hD : D = discOf m f)
    {N : ℕ} (Q : HeegnerForm N D) {M : ℕ} (hM : 0 < M) :
    {x : QNeg m | algebraMap (QNeg m) (AfK m) x ∈ latHat m (kappa m ⁻¹' (latM Q M : Set ℂ))} =
      kappa m ⁻¹' (latM Q M : Set ℂ) := by
  have ht := kappa_tK (m := m) hD Q
  rw [preimage_latM_eq_span hD Q M ht]
  have hA : (0 : ℤ) < Q.A := Q.A_pos
  have hAq : (Q.A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  have hAt : ((Q.A.toNat : ℕ) : ℚ) = Q.A := by
    have : ((Q.A.toNat : ℕ) : ℤ) = Q.A := Int.toNat_of_nonneg hA.le
    exact_mod_cast this
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  refine latHat_inter_of_sandwich (invK m M) (tK m Q (cz m f)) (2 * cz m f) (2 * Q.A.toNat * M)
    (by have := cz_pos (m := m) (f := f); omega) (Nat.mul_pos (Nat.mul_pos two_pos (by omega)) hM) ?_ ?_ ?_
  · intro y
    have h1 := two_cz_mul_mem hsq hD Q y
    refine (Submodule.span_le.mpr ?_) h1
    rintro z (rfl | rfl)
    · rw [SetLike.mem_coe, Submodule.mem_span_pair]
      refine ⟨M, 0, ?_⟩
      have hMK : (M : QNeg m) ≠ 0 := by exact_mod_cast hM.ne'
      simp only [invK, zero_smul, add_zero, zsmul_eq_mul, Int.cast_natCast, map_div₀, map_one,
        map_natCast]
      field_simp
    · exact Submodule.subset_span (by simp)
  · refine ⟨((2 * Q.A.toNat : ℕ) : 𝓞 (QNeg m)), ?_⟩
    have hMK : (M : QNeg m) ≠ 0 := by exact_mod_cast hM.ne'
    rw [map_natCast]
    simp only [invK, map_div₀, map_one, map_natCast]
    push_cast
    field_simp
  · refine ⟨((M : ℕ) : 𝓞 (QNeg m)) * ((-Q.B : 𝓞 (QNeg m)) + (cz m f : 𝓞 (QNeg m)) * sqrtNeg m), ?_⟩
    have hsq' : algebraMap (𝓞 (QNeg m)) (QNeg m) (sqrtNeg m) = QuadraticAlgebra.omega := coe_sqrtNeg
    rw [map_mul, map_add, map_mul, map_neg, map_intCast, map_natCast, map_natCast, hsq',
      natCast_mul_mk (2 * Q.A.toNat * M)]
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, tK, QuadraticAlgebra.im_add,
        QuadraticAlgebra.im_neg, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast]
      push_cast [hAt]
      field_simp
      ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, tK, QuadraticAlgebra.re_add,
        QuadraticAlgebra.re_neg, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast]
      push_cast [hAt]
      field_simp
      ring

end X0EtaRoute
