import ZInQKernel.Contrib.OneProof.ShimuraMainCM

noncomputable section

open Complex Topology Filter

namespace ZInQ.Contrib.HCMLattice

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise T5Glue

/-! ## §L. Local components at a rational prime `p` -/

/-- The places `v` of `K = ℚ(√−m)` above a rational prime `p` (the height-one primes containing `p`). -/
abbrev PlacesAbove (m : ℕ) [NeZero m] (p : ℕ) : Type :=
  {v : HeightOneSpectrum (𝓞 (QNeg m)) // (p : 𝓞 (QNeg m)) ∈ v.asIdeal}

/-- `K_p = K ⊗_ℚ ℚ_p`, in its standard model `∏_{v ∣ p} K_v`. -/
abbrev Kp (m : ℕ) [NeZero m] (p : ℕ) : Type :=
  (v : PlacesAbove m p) → v.1.adicCompletion (QNeg m)

variable {m : ℕ} [NeZero m]

/-- The `p`-component `x ↦ x_p` of a finite adele, `𝔸_{K,f} → K_p`. -/
def projP (p : ℕ) (x : AfK m) : Kp m p := fun v => x v.1

/-- The diagonal embedding `K → K_p`. -/
def diagP (p : ℕ) (k : QNeg m) : Kp m p := projP p (algebraMap (QNeg m) (AfK m) k)

/-- `𝔞_p = 𝔞 ⊗ ℤ_p ⊂ K_p`: the closure of a lattice `𝔞 ⊂ K` in `K_p` (for a finitely generated `ℤ`-module
`𝔞` this is the `ℤ_p`-module it generates, since `ℤ` is dense in `ℤ_p`). -/
def locLat (p : ℕ) (𝔞 : Set (QNeg m)) : Set (Kp m p) := closure (diagP p '' 𝔞)

/-- The `p`-component `s_p ∈ K_p^×` of an idele `s` of `K`. -/
def ideleComp (p : ℕ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : Kp m p := projP p (finPart s)

theorem continuous_projP (p : ℕ) : Continuous (projP (m := m) p) :=
  continuous_pi fun v => RestrictedProduct.continuous_eval v.1

theorem projP_mul (p : ℕ) (x y : AfK m) : projP p (x * y) = projP p x * projP p y := rfl

theorem projP_sub (p : ℕ) (x y : AfK m) : projP p (x - y) = projP p x - projP p y := rfl

theorem projP_one (p : ℕ) : projP p (1 : AfK m) = 1 := rfl

theorem finPart_mul_inv (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : finPart s * finPart s⁻¹ = 1 := by
  rw [mul_comm]; exact finPart_inv_mul s

theorem ideleComp_mul_inv (p : ℕ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    ideleComp p s * ideleComp p s⁻¹ = 1 := by
  simp only [ideleComp, ← projP_mul, finPart_mul_inv, projP_one]

theorem ideleComp_inv_mul (p : ℕ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    ideleComp p s⁻¹ * ideleComp p s = 1 := by
  rw [mul_comm]; exact ideleComp_mul_inv p s

/-! ## §M. A lattice contains `N·𝓞_K` -/

theorem mem_of_kappa (L : PeriodPair) {𝔞 : Set (QNeg m)} (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞)
    (x : QNeg m) : x ∈ 𝔞 ↔ kappa m x ∈ L.lattice := by
  rw [← SetLike.mem_coe, h𝔞]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, e⟩ => kappa_injective e ▸ hy⟩

theorem kappa_zsmul (n : ℤ) (x : QNeg m) : kappa m (n • x) = n • kappa m x := by
  rw [← kappaLin_apply, ← kappaLin_apply, map_zsmul]

/-- Every element of `K` has a nonzero integer multiple in a lattice `𝔞`. -/
theorem exists_nat_mul_mem (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) (x : QNeg m) :
    ∃ n : ℕ, 0 < n ∧ ((n : ℤ) • x) ∈ 𝔞 := by
  have hm := mem_of_kappa L h𝔞
  obtain ⟨a₁, -, ha₁⟩ : L.ω₁ ∈ kappa m '' 𝔞 := h𝔞 ▸ L.ω₁_mem_lattice
  obtain ⟨a₂, -, ha₂⟩ : L.ω₂ ∈ kappa m '' 𝔞 := h𝔞 ▸ L.ω₂_mem_lattice
  have hind := LinearIndependent.pair_iff.1 L.indep
  have hk : ∀ c₁ c₂ : ℚ, kappa m ((c₁ : QNeg m) * a₁ + (c₂ : QNeg m) * a₂) =
      (c₁ : ℝ) • L.ω₁ + (c₂ : ℝ) • L.ω₂ := by
    intro c₁ c₂
    rw [← ha₁, ← ha₂, ← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply]
    simp only [map_add, map_mul, map_ratCast, Complex.real_smul]
    push_cast; ring
  set p₁ := a₁.re; set q₁ := a₁.im; set p₂ := a₂.re; set q₂ := a₂.im
  have hdet : p₁ * q₂ - p₂ * q₁ ≠ 0 := by
    intro hd
    have e1 : (q₂ : QNeg m) * a₁ + ((-q₁ : ℚ) : QNeg m) * a₂ = ((p₁ * q₂ - p₂ * q₁ : ℚ) : QNeg m) := by
      ext <;> simp [p₁, q₁, p₂, q₂] <;> ring
    have h1 := hk q₂ (-q₁)
    rw [e1, hd] at h1
    simp only [Rat.cast_zero, show kappa m 0 = 0 by simp [kappa]] at h1
    obtain ⟨hq₂, hq₁⟩ := hind _ _ h1.symm
    have hq₂' : q₂ = 0 := by exact_mod_cast hq₂
    have hq₁' : q₁ = 0 := by have := hq₁; push_cast at this; exact_mod_cast neg_eq_zero.1 this
    have e2 : (p₂ : QNeg m) * a₁ + ((-p₁ : ℚ) : QNeg m) * a₂ = ((0 : ℚ) : QNeg m) := by
      ext <;> simp [p₁, q₁, p₂, q₂, hq₁', hq₂'] <;> ring
    have h2 := hk p₂ (-p₁)
    rw [e2] at h2
    simp only [Rat.cast_zero, show kappa m 0 = 0 by simp [kappa]] at h2
    obtain ⟨hp₂, hp₁⟩ := hind _ _ h2.symm
    have hp₁' : p₁ = 0 := by have := hp₁; push_cast at this; exact_mod_cast neg_eq_zero.1 this
    have ha₁0 : a₁ = 0 := by
      ext
      · exact hp₁'
      · exact hq₁'
    have := hind 1 0 (by rw [← ha₁, ha₁0]; simp [kappa])
    exact one_ne_zero this.1
  set r : ℚ := (x.re * q₂ - x.im * p₂) / (p₁ * q₂ - p₂ * q₁)
  set t : ℚ := (p₁ * x.im - q₁ * x.re) / (p₁ * q₂ - p₂ * q₁)
  have hdet' : a₂.im * a₁.re - a₂.re * a₁.im ≠ 0 := by
    intro h; apply hdet; simp only [p₁, q₁, p₂, q₂]; linear_combination h
  have hx : (r : QNeg m) * a₁ + (t : QNeg m) * a₂ = x := by
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_ratCast,
        QuadraticAlgebra.im_ratCast, r, t, p₁, q₁, p₂, q₂, Rat.cast_id] at hdet ⊢
      field_simp; ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ratCast,
        QuadraticAlgebra.im_ratCast, r, t, p₁, q₁, p₂, q₂, Rat.cast_id] at hdet ⊢
      field_simp; ring
  refine ⟨r.den * t.den, Nat.mul_pos r.den_pos t.den_pos, ?_⟩
  rw [hm, ← hx, kappa_zsmul, hk]
  have er : ((r.den * t.den : ℕ) : ℤ) • ((r : ℝ) • L.ω₁) = ((r.num * t.den : ℤ) : ℂ) * L.ω₁ := by
    rw [zsmul_eq_mul, Complex.real_smul, ← mul_assoc]
    congr 1
    have : (r : ℝ) = r.num / r.den := by exact_mod_cast (Rat.num_div_den r).symm
    rw [this]; push_cast; field_simp
  have et : ((r.den * t.den : ℕ) : ℤ) • ((t : ℝ) • L.ω₂) = ((t.num * r.den : ℤ) : ℂ) * L.ω₂ := by
    rw [zsmul_eq_mul, Complex.real_smul, ← mul_assoc]
    congr 1
    have : (t : ℝ) = t.num / t.den := by exact_mod_cast (Rat.num_div_den t).symm
    rw [this]; push_cast; field_simp
  rw [smul_add, er, et]
  exact PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩

/-- A lattice `𝔞 ⊂ K` (with `κ𝔞` a period lattice) contains `N·𝓞_K` for some `N > 0`. -/
theorem exists_nat_mul_integers_mem (hsq : Squarefree m) (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) :
    ∃ N : ℕ, 0 < N ∧ ∀ y : 𝓞 (QNeg m), (N : QNeg m) * y ∈ 𝔞 := by
  have hm := mem_of_kappa L h𝔞
  obtain ⟨n₁, hn₁, h₁⟩ := exists_nat_mul_mem L h𝔞 1
  obtain ⟨n₂, hn₂, h₂⟩ := exists_nat_mul_mem L h𝔞 QuadraticAlgebra.omega
  refine ⟨2 * n₁ * n₂, by positivity, fun y => ?_⟩
  obtain ⟨a, t, -, ha, ht, -⟩ := two_coords hsq y
  have hy : (2 : QNeg m) * (y : QNeg m) = (a : QNeg m) + (t : QNeg m) * QuadraticAlgebra.omega := by
    ext
    · simp [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, ha]
    · simp [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, ht]
  have e : ((2 * n₁ * n₂ : ℕ) : QNeg m) * (y : QNeg m) =
      (a * n₂ : ℤ) • ((n₁ : ℤ) • (1 : QNeg m)) + (t * n₁ : ℤ) • ((n₂ : ℤ) • QuadraticAlgebra.omega) := by
    have : ((2 * n₁ * n₂ : ℕ) : QNeg m) * (y : QNeg m) = (n₁ * n₂ : QNeg m) * (2 * (y : QNeg m)) := by
      push_cast; ring
    rw [this, hy]
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [e, hm, kappa_add, kappa_zsmul (a * n₂), kappa_zsmul (t * n₁)]
  exact add_mem (zsmul_mem ((hm _).1 h₁) _) (zsmul_mem ((hm _).1 h₂) _)

/-- `𝔞 = κ⁻¹(L)` as a `ℤ`-submodule. -/
theorem eq_kappaComap (L : PeriodPair) {𝔞 : Set (QNeg m)} (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) :
    𝔞 = ((kappaComap (m := m) L.lattice : Submodule ℤ (QNeg m)) : Set (QNeg m)) := by
  rw [coe_kappaComap]; ext x; exact mem_of_kappa L h𝔞 x

/-- **`𝔞̂` is open** in `𝔸_{K,f}` for a lattice `𝔞` (it contains `N·𝒪̂_K`). -/
theorem isOpen_latHat (hsq : Squarefree m) (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) : IsOpen (latHat m 𝔞) := by
  obtain ⟨N, hN, hN𝔞⟩ := exists_nat_mul_integers_mem hsq L h𝔞
  have e := eq_kappaComap L h𝔞
  set M := kappaComap (m := m) L.lattice
  rw [e] at hN𝔞 ⊢
  rw [latHat_eq_closure]
  set H := (M.toAddSubgroup.map (algebraMap (QNeg m) (AfK m)).toAddMonoidHom).topologicalClosure
  refine AddSubgroup.isOpen_of_mem_nhds H (g := 0) ?_
  have hN0 : (N : QNeg m) ≠ 0 := by exact_mod_cast hN.ne'
  set W : Set (AfK m) := (fun z => algebraMap (QNeg m) (AfK m) ((N : QNeg m)⁻¹) * z) ⁻¹'
    (FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m) : Set (AfK m))
  have hWo : IsOpen W := (FiniteAdeleRing.isOpen_integralAdeles (𝓞 (QNeg m)) (QNeg m)).preimage
    (continuous_const.mul continuous_id)
  have h0W : (0 : AfK m) ∈ W := by
    show algebraMap (QNeg m) (AfK m) ((N : QNeg m)⁻¹) * 0 ∈
      (FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m) : Set (AfK m))
    rw [mul_zero]; exact Subalgebra.zero_mem _
  refine Filter.mem_of_superset (hWo.mem_nhds h0W) fun z hz => ?_
  have hcl := FiniteAdeleRing.closure_range_algebraMap (𝓞 (QNeg m)) (QNeg m)
  have hz' := (Set.ext_iff.1 hcl (algebraMap (QNeg m) (AfK m) ((N : QNeg m)⁻¹) * z)).2 hz
  have hcont : Continuous fun w : AfK m => algebraMap (QNeg m) (AfK m) (N : QNeg m) * w :=
    continuous_const.mul continuous_id
  have h1 := image_closure_subset_closure_image hcont ⟨_, hz', rfl⟩
  have hzeq : algebraMap (QNeg m) (AfK m) (N : QNeg m) *
      (algebraMap (QNeg m) (AfK m) ((N : QNeg m)⁻¹) * z) = z := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hN0, map_one, one_mul]
  beta_reduce at h1
  rw [hzeq] at h1
  rw [AddSubgroup.topologicalClosure_coe]
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
  refine ⟨(N : QNeg m) * (r : QNeg m), hN𝔞 r, ?_⟩
  show algebraMap (QNeg m) (AfK m) ((N : QNeg m) * (r : QNeg m)) = _
  rw [map_mul]; rfl

/-! ## §N. `(s⁻¹𝔞)_p = s_p⁻¹ 𝔞_p` -/

/-- **The localization form of `s⁻¹𝔞`**, preimage version: for every lattice `𝔞 ⊂ K`, idele `s` and `p`,
`(K ∩ s_f⁻¹𝔞̂)_p = {y ∈ K_p : s_p y ∈ 𝔞_p}`. -/
theorem locLat_sInvLat_eq_preimage (hsq : Squarefree m) (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (p : ℕ) :
    locLat p (sInvLat m s 𝔞) = {y | ideleComp p s * y ∈ locLat p 𝔞} := by
  set U : Set (AfK m) := {x | finPart s * x ∈ latHat m 𝔞} with hUdef
  have hUo : IsOpen U := (isOpen_latHat hsq L h𝔞).preimage (continuous_const.mul continuous_id)
  have hproj : ∀ x ∈ latHat m 𝔞, projP p x ∈ locLat p 𝔞 := by
    intro x hx
    have h := image_closure_subset_closure_image (continuous_projP (m := m) p) ⟨x, hx, rfl⟩
    rw [Set.image_image] at h
    exact h
  apply Set.Subset.antisymm
  · have hcl : IsClosed {y : Kp m p | ideleComp p s * y ∈ locLat p 𝔞} :=
      isClosed_closure.preimage (continuous_const.mul continuous_id)
    refine closure_minimal ?_ hcl
    rintro _ ⟨k, hk, rfl⟩
    show ideleComp p s * diagP p k ∈ locLat p 𝔞
    have := hproj _ hk
    rw [projP_mul] at this
    exact this
  · intro y hy
    rw [locLat, mem_closure_iff]
    intro W hWo hyW
    set c := ideleComp p s⁻¹
    have hW' : IsOpen {z : Kp m p | c * z ∈ W} := hWo.preimage (continuous_const.mul continuous_id)
    have hsy : c * (ideleComp p s * y) ∈ W := by rw [← mul_assoc, ideleComp_inv_mul, one_mul]; exact hyW
    obtain ⟨_, hz, ⟨a₀, ha₀, rfl⟩⟩ := mem_closure_iff.1 hy _ hW' hsy
    have hx₀U : finPart s⁻¹ * algebraMap (QNeg m) (AfK m) a₀ ∈ U := by
      show finPart s * (finPart s⁻¹ * algebraMap (QNeg m) (AfK m) a₀) ∈ latHat m 𝔞
      rw [← mul_assoc, finPart_mul_inv, one_mul]
      exact mem_latHat_of_mem ha₀
    have hx₀W : finPart s⁻¹ * algebraMap (QNeg m) (AfK m) a₀ ∈ projP p ⁻¹' W := by
      show projP p (finPart s⁻¹ * algebraMap (QNeg m) (AfK m) a₀) ∈ W
      rw [projP_mul]; exact hz
    obtain ⟨k, hk⟩ := (FiniteAdeleRing.denseRange_algebraMap (𝓞 (QNeg m)) (QNeg m)).exists_mem_open
      (((continuous_projP p).isOpen_preimage W hWo).inter hUo) ⟨_, hx₀W, hx₀U⟩
    exact ⟨diagP p k, hk.1, k, hk.2, rfl⟩

/-- **`(s⁻¹𝔞)_p = s_p⁻¹ 𝔞_p`** (Shimura's localization form of `s⁻¹𝔞`), for every lattice `𝔞 ⊂ K` (of any order),
every idele `s` and every `p`, where `s⁻¹𝔞 = sInvLat m s 𝔞 = K ∩ s_f⁻¹𝔞̂`. -/
theorem locLat_sInvLat (hsq : Squarefree m) (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (p : ℕ) :
    locLat p (sInvLat m s 𝔞) = (fun x => ideleComp p s⁻¹ * x) '' locLat p 𝔞 := by
  rw [locLat_sInvLat_eq_preimage hsq L h𝔞 s p]
  ext y
  constructor
  · intro hy
    refine ⟨_, hy, ?_⟩
    show ideleComp p s⁻¹ * (ideleComp p s * y) = y
    rw [← mul_assoc, ideleComp_inv_mul, one_mul]
  · rintro ⟨x, hx, rfl⟩
    show ideleComp p s * (ideleComp p s⁻¹ * x) ∈ locLat p 𝔞
    rwa [← mul_assoc, ideleComp_mul_inv, one_mul]

/-- The two readings of "`v` represents `s⁻¹u`": `s_f v − u ∈ 𝔞̂` gives `v − s_p⁻¹u ∈ (s⁻¹𝔞)_p` for every `p`. -/
theorem rep_local_of_global (hsq : Squarefree m) (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) {u v : QNeg m}
    (h : finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞) (p : ℕ) :
    diagP p v - ideleComp p s⁻¹ * diagP p u ∈ locLat p (sInvLat m s 𝔞) := by
  rw [locLat_sInvLat_eq_preimage hsq L h𝔞 s p]
  show ideleComp p s * (diagP p v - ideleComp p s⁻¹ * diagP p u) ∈ locLat p 𝔞
  have e : ideleComp p s * (diagP p v - ideleComp p s⁻¹ * diagP p u) =
      projP p (finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u) := by
    rw [projP_sub, projP_mul, mul_sub, ← mul_assoc, ideleComp_mul_inv, one_mul]; rfl
  rw [e]
  have h' := image_closure_subset_closure_image (continuous_projP (m := m) p) ⟨_, h, rfl⟩
  rw [Set.image_image] at h'
  exact h'

end ZInQ.Contrib.HCMLattice
