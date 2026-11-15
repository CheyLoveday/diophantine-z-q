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

/-! ## Part 2. Integer and lattice helpers -/

theorem dvd_pow_eight_sub_one {p : ℤ} (hp : Odd p) : (32 : ℤ) ∣ p ^ 8 - 1 := by
  obtain ⟨k, rfl⟩ := hp
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self k
  refine ⟨r * (2 * k ^ 2 + 2 * k + 1) * (8 * k ^ 4 + 16 * k ^ 3 + 12 * k ^ 2 + 4 * k + 1), ?_⟩
  linear_combination 16 * (2 * k ^ 2 + 2 * k + 1) * (8 * k ^ 4 + 16 * k ^ 3 + 12 * k ^ 2 + 4 * k + 1) * hr

/-- The period pair `(1/M, τ)`. -/
def ppM (M : ℕ) (hM : M ≠ 0) (τ : UpperHalfPlane) : PeriodPair :=
  ⟨1 / (M : ℂ), τ, by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him : t * τ.im = 0 := by
      have := congrArg Complex.im h
      simpa [Complex.real_smul] using this
    have ht : t = 0 := by
      rcases mul_eq_zero.1 him with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt τ.im_pos)
    subst ht
    simp only [zero_smul, add_zero, Complex.real_smul] at h
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
    refine ⟨?_, rfl⟩
    have h2 : (s : ℂ) = 0 := by
      have := congrArg (fun z => z * (M : ℂ)) h
      simpa [hM'] using this
    exact_mod_cast h2⟩

theorem ppM_lattice {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) (M : ℕ) (hM : M ≠ 0) :
    (ppM M hM Q.tauH).lattice = latM Q M := rfl

theorem latM_one {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : latM Q 1 = Q.lat := by
  simp [latM, HeegnerForm.lat]

theorem latM_N {D : ℤ} (Q : HeegnerForm 32 D) : latM Q 32 = Q.latN := rfl

theorem notMem_of_coeffs (P : PeriodPair) (α β : ℚ) (h : α.den ≠ 1 ∨ β.den ≠ 1) {z : ℂ}
    (hz : z = α * P.ω₁ + β * P.ω₂) : z ∉ P.lattice := by
  rw [hz, PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice]
  tauto

theorem mem_smul_span_pair {c α β z : ℂ} :
    z ∈ c • ((Submodule.span ℤ {α, β} : Submodule ℤ ℂ) : Set ℂ) ↔
      ∃ a b : ℤ, z = c * (a * α + b * β) := by
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_pair] at hy
    obtain ⟨a, b, rfl⟩ := hy
    exact ⟨a, b, by simp [zsmul_eq_mul, smul_eq_mul]⟩
  · rintro ⟨a, b, rfl⟩
    refine ⟨a * α + b * β, ?_, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_pair]
    exact ⟨a, b, by simp [zsmul_eq_mul]⟩

theorem latHat_zsmul_mem (M : Submodule ℤ (QNeg m)) (n : ℤ) {x : AfK m}
    (hx : x ∈ latHat m (M : Set (QNeg m))) : n • x ∈ latHat m (M : Set (QNeg m)) := by
  rw [latHat_eq_closure] at hx ⊢
  exact AddSubgroup.zsmul_mem _ hx n

/-- `κ⁻¹(L)` as a submodule; its coercion is the preimage. -/
abbrev KL (m : ℕ) [NeZero m] (L : Submodule ℤ ℂ) : Submodule ℤ (QNeg m) := kappaComap (m := m) L

theorem coe_KL (L : Submodule ℤ ℂ) : ((KL m L : Submodule ℤ (QNeg m)) : Set (QNeg m)) =
    kappa m ⁻¹' (L : Set ℂ) := coe_kappaComap L

theorem mem_sInv_iff {s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)} {X : Set (QNeg m)} {c : ℂ}
    {L : Set ℂ} (h : kappa m '' sInvLat m s X = c • L) {x : QNeg m} :
    x ∈ sInvLat m s X ↔ kappa m x ∈ c • L := by
  constructor
  · intro hx; rw [← h]; exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← kappa_injective hyx]

theorem mem_sInvLat_iff {s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)} {X : Set (QNeg m)} {x : QNeg m} :
    x ∈ sInvLat m s X ↔ finPart s * algebraMap (QNeg m) (AfK m) x ∈ latHat m X := Iff.rfl

/-! ## Part 3. The idelic transport at level 32 -/

section Transport

variable {f : ℕ} [NeZero f] {D : ℤ}

/-- The data of one transport: `s⁻¹⟨1, τ_Q⟩ = c'⟨1, τ_{Q'}⟩`, `s⁻¹⟨1/32, τ_Q⟩ = c'⟨1/32, τ_{Q'}⟩`
(the conclusion of `T5Glue.IdeleLatticeScale` at `N = 32`). -/
structure TData (m : ℕ) [NeZero m] (f : ℕ) (D : ℤ) where
  hsq : Squarefree m
  hD : D = discOf m f
  Q : HeegnerForm 32 D
  Q' : HeegnerForm 32 D
  s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)
  c : ℂ
  hc : c ≠ 0
  hlat : kappa m '' sInvLat m s (kappa m ⁻¹' (Q.lat : Set ℂ)) = c • (Q'.lat : Set ℂ)
  hlatN : kappa m '' sInvLat m s (kappa m ⁻¹' (Q.latN : Set ℂ)) = c • (Q'.latN : Set ℂ)

variable (T : TData m f D)

/-- `u₁ = 1/32 ∈ K`. -/
abbrev u1 (m : ℕ) [NeZero m] : QNeg m := invK m 32

theorem kappa_u1 : kappa m (u1 m) = 1 / 32 := by
  rw [u1, kappa_invK]; norm_num

theorem lat_le_latM (Q : HeegnerForm 32 D) {M : ℕ} (hM : 0 < M) : Q.lat ≤ latM Q M := by
  rw [HeegnerForm.lat, latM, Submodule.span_le]
  rintro z (rfl | rfl)
  · rw [SetLike.mem_coe, Submodule.mem_span_pair]
    refine ⟨M, 0, ?_⟩
    have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    simp [zsmul_eq_mul]; field_simp
  · exact Submodule.subset_span (by simp)

theorem latM_le_latN (Q : HeegnerForm 32 D) {M d : ℕ} (hdM : d * M = 32) : latM Q M ≤ Q.latN := by
  rw [latM, HeegnerForm.latN, Submodule.span_le]
  rintro z (rfl | rfl)
  · rw [SetLike.mem_coe, Submodule.mem_span_pair]
    refine ⟨d, 0, ?_⟩
    have hM : (M : ℂ) ≠ 0 := by
      have : M ≠ 0 := by rintro rfl; simp at hdM
      exact_mod_cast this
    have h32 : ((32 : ℕ) : ℂ) = (d : ℂ) * M := by rw [← hdM]; push_cast; ring
    simp only [zsmul_eq_mul, Int.cast_natCast, zero_smul, add_zero, h32]
    have hd : (d : ℂ) ≠ 0 := by
      have : d ≠ 0 := by rintro rfl; simp at hdM
      exact_mod_cast this
    field_simp
  · exact Submodule.subset_span (by simp)

/-- `𝔞̂ ⊆ 𝔟̂` for `κ⁻¹⟨1,τ⟩ ⊆ κ⁻¹L`. -/
theorem latHat_lat_sub {L : Submodule ℤ ℂ} (Q : HeegnerForm 32 D) (h : Q.lat ≤ L) :
    latHat m (kappa m ⁻¹' (Q.lat : Set ℂ)) ⊆ latHat m (kappa m ⁻¹' (L : Set ℂ)) :=
  latHat_mono (Set.preimage_mono h)

/-- **`s⁻¹(1/32)`**: some `v₁ ∈ K` with `s_f v₁ − 1/32 ∈ 𝔞̂` and `κ(v₁) = c'(p₁/32 + q₁τ')`, `p₁` odd. -/
theorem exists_v1 : ∃ (v : QNeg m) (p q : ℤ),
    finPart T.s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) (u1 m) ∈
      latHat m (kappa m ⁻¹' (T.Q.lat : Set ℂ)) ∧
    kappa m v = T.c * (p * (1 / 32) + q * T.Q'.tau) ∧ Odd p := by
  obtain ⟨v, hv⟩ := strongApprox m T.hsq f D T.hD 32 T.Q T.s (u1 m)
  have hlatN := T.hlatN
  -- `v ∈ s⁻¹𝔞_N`
  have hvN : v ∈ sInvLat m T.s (kappa m ⁻¹' (T.Q.latN : Set ℂ)) := by
    rw [mem_sInvLat_iff, ← coe_KL]
    have h1 : finPart T.s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) (u1 m) ∈
        latHat m ((KL m T.Q.latN : Submodule ℤ (QNeg m)) : Set (QNeg m)) := by
      rw [coe_KL]; exact latHat_lat_sub T.Q (lat_le_latN T.Q (by norm_num)) hv
    have h2 : algebraMap (QNeg m) (AfK m) (u1 m) ∈
        latHat m ((KL m T.Q.latN : Submodule ℤ (QNeg m)) : Set (QNeg m)) := by
      apply mem_latHat_of_mem
      rw [coe_KL, Set.mem_preimage, kappa_u1]
      exact Submodule.subset_span (by simp)
    have := latHat_add_mem _ h1 h2
    simpa using this
  rw [mem_sInv_iff hlatN, HeegnerForm.latN, mem_smul_span_pair] at hvN
  obtain ⟨p, q, hpq⟩ := hvN
  refine ⟨v, p, q, hv, by rw [hpq]; push_cast; ring, ?_⟩
  -- `p` odd
  by_contra hp
  rw [Int.not_odd_iff_even] at hp
  obtain ⟨r, rfl⟩ := hp
  have h16 : (16 : ℤ) • v ∈ sInvLat m T.s (kappa m ⁻¹' (T.Q.lat : Set ℂ)) := by
    rw [mem_sInv_iff T.hlat, HeegnerForm.lat, mem_smul_span_pair]
    refine ⟨r, 16 * q, ?_⟩
    rw [zsmul_eq_mul, kappa_intCast_mul, hpq]; push_cast; ring
  rw [mem_sInvLat_iff, ← coe_KL] at h16
  have h3 := latHat_sub_mem _ h16 (latHat_zsmul_mem _ 16 (by rw [coe_KL]; exact hv))
  rw [map_zsmul, smul_sub, mul_smul_comm, sub_sub_cancel, ← map_zsmul, coe_KL] at h3
  have h4 := (Set.ext_iff.1 (latHatInter m T.hsq f D T.hD 32 T.Q) _).1 h3
  rw [Set.mem_preimage, zsmul_eq_mul, kappa_intCast_mul, kappa_u1] at h4
  apply notMem_of_coeffs (pp T.Q.tauH) (1 / 2) 0 (Or.inl (by norm_num)) (z := ((16 : ℤ) : ℂ) * (1 / 32))
    (by simp [pp]; norm_num)
  exact h4

end Transport

end X0EtaRoute
