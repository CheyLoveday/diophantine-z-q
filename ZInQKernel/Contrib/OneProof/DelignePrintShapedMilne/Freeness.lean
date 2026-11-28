import ZInQKernel.Contrib.OneProof.DelignePrintShapedMilne.Datum
set_option autoImplicit false

/-!
# Freeness of the action at level `K₃`

Let `B = (2, -3)_ℚ`, `𝒪̂ = 𝒪 ⊗ ℤ̂` and `K₃ = {k ∈ 𝒪̂^× : k ≡ 1 mod 3𝒪̂}`. The group `B^×` acts on
`ℍ^± × (B ⊗ 𝔸_f)^× / K₃` by `γ · [z, g] = [ι(γ) z, γ g]`. The main theorem `stabilizer_trivial`
states that this action is free: if `ι(γ) z = z` and `g = γ g k` with `k ∈ K₃`, then `γ = 1`.
Equivalently, every group `Γ_g = B^× ∩ g K₃ g⁻¹` acts freely on `ℍ^±`.

This is the property for which Milne asks `K` to be "sufficiently small" (J. S. Milne,
*Introduction to Shimura varieties*, Clay Math. Proc. 4 (2005), p. 307: "when K is sufficiently
small, Γg will be neat … and hence torsion free"), here for the whole group `B^×`, `−1` included;
it is the smoothness step (step 2) of the derivation listed in the docstring of
`DelignePSMilne.MilneShimuraFamilyPrint`.

Proof.
* **Integrality.** From `γ = g k⁻¹ g⁻¹` in `(B ⊗ 𝔸_f)^×`, the reduced norm `nrd γ` is a unit of
  `ℤ̂ ∩ ℚ = ℤ`, so `nrd γ = ±1`, and `nrd(γ - 1) = nrd(k⁻¹(1 - k)) ∈ 9ℤ̂ ∩ ℚ = 9ℤ`.
* **Fixed points.** If a real matrix `M = (a b; c d)` fixes a non-real `z = x + iy`, then
  `a - d = 2cx` and `b = -c(x² + y²)`, so `(tr M)² - 4 det M = -4c²y² ≤ 0`, with equality only
  when `M` is scalar.
* **Conclusion.** With `t = 2 re γ = tr ι(γ)` and `det ι(γ) = nrd γ`: `nrd γ ≥ t²/4 ≥ 0`, so
  `nrd γ = 1`; then `t² ≤ 4` and `2 - t = nrd(γ - 1) ∈ 9ℤ`, so `t = 2`; then `ι(γ)` is scalar and
  `γ = 1`.
-/

noncomputable section

namespace DelignePSMilne.Freeness

open ShimuraCFT RayClassCFT

/-! ## 1. Integrality -/

/-- The finite integral adeles `ℤ̂ ⊂ 𝔸_f` as a subring. -/
def zhatSubring : Subring AQ where
  carrier := ZhatQ
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' _ := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' _ := zero_mem _
  neg_mem' ha v := neg_mem (ha v)

theorem mem_zhatSubring {a : AQ} : a ∈ zhatSubring ↔ a ∈ ZhatQ := Iff.rfl

/-- The reduced norm commutes with `B → B ⊗ 𝔸_f`. -/
theorem nrd_bEmb (x : LeafQM.B) :
    ShimuraGlue.nrdQ AQ (bEmb x) = algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ x) := by
  rw [ShimuraGlue.nrdQ_apply, ShimuraGlue.nrdQ_apply]
  change (algebraMap ℚ AQ x.re) ^ 2 - 2 * (algebraMap ℚ AQ x.imI) ^ 2 +
      3 * (algebraMap ℚ AQ x.imJ) ^ 2 - 6 * (algebraMap ℚ AQ x.imK) ^ 2 = _
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]

/-- `nrd(-z) = nrd z`. -/
theorem nrd_neg (z : BAQ) : ShimuraGlue.nrdQ AQ (-z) = ShimuraGlue.nrdQ AQ z := by
  rw [ShimuraGlue.nrdQ_apply, ShimuraGlue.nrdQ_apply]
  simp

/-- `nrd 3 = 9`. -/
theorem nrd_three : ShimuraGlue.nrdQ AQ (3 : BAQ) = 9 := by
  rw [ShimuraGlue.nrdQ_apply, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  norm_num

/-- The reduced norm of an element of `𝒪̂` lies in `ℤ̂`:
`nrd(ofQ n) = n₀² + n₀n₂ + n₂² - 2(n₁² + n₁n₃ + n₃²)`. -/
theorem nrd_mem_ZhatQ {y : BAQ} (hy : y ∈ OhatQ) : ShimuraGlue.nrdQ AQ y ∈ ZhatQ := by
  obtain ⟨n, hn, rfl⟩ := hy
  have h2 := ShimuraGlue.two_mul_half AQ
  have e : ShimuraGlue.nrdQ AQ (ShimuraGlue.ofQ n) =
      n 0 * n 0 + n 0 * n 2 + n 2 * n 2 -
        ((n 1 * n 1 + n 1 * n 3 + n 3 * n 3) + (n 1 * n 1 + n 1 * n 3 + n 3 * n 3)) := by
    rw [ShimuraGlue.nrdQ_apply]
    change (n 0 + ShimuraGlue.half AQ * n 2) ^ 2 - 2 * (n 1 + ShimuraGlue.half AQ * n 3) ^ 2 +
      3 * (ShimuraGlue.half AQ * n 2) ^ 2 - 6 * (ShimuraGlue.half AQ * n 3) ^ 2 = _
    linear_combination (n 0 * n 2 + (2 * ShimuraGlue.half AQ + 1) * n 2 ^ 2 - 2 * n 1 * n 3 -
      2 * (2 * ShimuraGlue.half AQ + 1) * n 3 ^ 2) * h2
  rw [e, ← mem_zhatSubring]
  have m : ∀ i, n i ∈ zhatSubring := hn
  have q : n 1 * n 1 + n 1 * n 3 + n 3 * n 3 ∈ zhatSubring :=
    add_mem (add_mem (mul_mem (m 1) (m 1)) (mul_mem (m 1) (m 3))) (mul_mem (m 3) (m 3))
  exact sub_mem (add_mem (add_mem (mul_mem (m 0) (m 0)) (mul_mem (m 0) (m 2)))
    (mul_mem (m 2) (m 2))) (add_mem q q)

/-- `ℚ ∩ ℤ̂ = ℤ`. -/
theorem exists_int_of_mem {r : ℚ} (h : algebraMap ℚ AQ r ∈ ZhatQ) : ∃ n : ℤ, r = n := by
  have h0 : (0 : AQ) ∈ ZhatQ := zhatSubring.zero_mem
  have hx : bEmb (⟨r, 0, 0, 0⟩ : LeafQM.B) ∈ OhatQ := by
    refine ⟨![algebraMap ℚ AQ r, 0, 0, 0], fun i => ?_, ?_⟩
    · fin_cases i
      · exact h
      · exact h0
      · exact h0
      · exact h0
    · ext <;> simp [bEmb, ShimuraGlue.ofQ]
  obtain ⟨n, hn⟩ := inO_of_bEmb_mem hx
  have h1 : r = (n 0 : ℚ) + (n 2 : ℚ) / 2 := congrArg QuaternionAlgebra.re hn
  have h3 : (0 : ℚ) = (n 2 : ℚ) / 2 := congrArg QuaternionAlgebra.imJ hn
  exact ⟨n 0, by linarith⟩

/-- **Integrality.** If `g = γ g k` with `k ∈ K₃`, then `nrd γ = ±1` and `nrd(γ - 1) ∈ 9ℤ`. -/
theorem integrality (gm : LeafQM.B) (hγ : ShimuraGlue.nrdQ ℚ gm ≠ 0) (g k : BAQˣ)
    (hk : k ∈ K3Q) (hg : (g : BAQ) = bEmb gm * g * k) :
    (ShimuraGlue.nrdQ ℚ gm = 1 ∨ ShimuraGlue.nrdQ ℚ gm = -1) ∧
      ∃ m : ℤ, ShimuraGlue.nrdQ ℚ (gm - 1) = 9 * m := by
  obtain ⟨hk1, hk2, y, hy, hky⟩ := hk
  have hgg : ShimuraGlue.nrdQ AQ (g : BAQ) * ShimuraGlue.nrdQ AQ ((g⁻¹ : BAQˣ) : BAQ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hkk : ShimuraGlue.nrdQ AQ (k : BAQ) * ShimuraGlue.nrdQ AQ ((k⁻¹ : BAQˣ) : BAQ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have e : ShimuraGlue.nrdQ AQ (g : BAQ) = algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ gm) *
      ShimuraGlue.nrdQ AQ (g : BAQ) * ShimuraGlue.nrdQ AQ (k : BAQ) := by
    conv_lhs => rw [hg]
    rw [map_mul, map_mul, nrd_bEmb]
  have h1 : algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ gm) * ShimuraGlue.nrdQ AQ (k : BAQ) = 1 := by
    linear_combination (-ShimuraGlue.nrdQ AQ ((g⁻¹ : BAQˣ) : BAQ)) * e +
      (1 - algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ gm) * ShimuraGlue.nrdQ AQ (k : BAQ)) * hgg
  have h2 : algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ gm) = ShimuraGlue.nrdQ AQ ((k⁻¹ : BAQˣ) : BAQ) := by
    linear_combination ShimuraGlue.nrdQ AQ ((k⁻¹ : BAQˣ) : BAQ) * h1 -
      algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ gm) * hkk
  have hinv : algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ gm) * algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ gm)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hγ, map_one]
  have h3 : algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ gm)⁻¹ = ShimuraGlue.nrdQ AQ (k : BAQ) := by
    linear_combination ShimuraGlue.nrdQ AQ (k : BAQ) * hinv -
      algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ gm)⁻¹ * h1
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := exists_int_of_mem (h2 ▸ nrd_mem_ZhatQ hk2)
    obtain ⟨b, hb⟩ := exists_int_of_mem (h3 ▸ nrd_mem_ZhatQ hk1)
    have hab' : ((a * b : ℤ) : ℚ) = 1 := by
      push_cast
      rw [← ha, ← hb]
      exact mul_inv_cancel₀ hγ
    have hab : a * b = 1 := by exact_mod_cast hab'
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hab with h | h
    · left; rw [ha, h]; simp
    · right; rw [ha, h]; simp
  · have e1 : (g : BAQ) * ((k⁻¹ : BAQˣ) : BAQ) = bEmb gm * g := by
      calc (g : BAQ) * ((k⁻¹ : BAQˣ) : BAQ) = bEmb gm * g * k * ((k⁻¹ : BAQˣ) : BAQ) := by
            rw [← hg]
        _ = bEmb gm * g := by rw [mul_assoc, Units.mul_inv, mul_one]
    have h1k : (1 : BAQ) - k = -(3 * y) := by rw [hky]; abel
    have e2 : bEmb (gm - 1) * g = g * (((k⁻¹ : BAQˣ) : BAQ) * -(3 * y)) := by
      rw [map_sub, map_one, sub_mul, ← e1, one_mul, ← h1k, mul_sub (((k⁻¹ : BAQˣ) : BAQ)),
        mul_one, Units.inv_mul, mul_sub, mul_one]
    have e3 := congrArg (ShimuraGlue.nrdQ AQ) e2
    simp only [map_mul, nrd_bEmb, nrd_neg, nrd_three] at e3
    have hM : algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ (gm - 1)) =
        9 * (ShimuraGlue.nrdQ AQ ((k⁻¹ : BAQˣ) : BAQ) * ShimuraGlue.nrdQ AQ y) := by
      linear_combination ShimuraGlue.nrdQ AQ ((g⁻¹ : BAQˣ) : BAQ) * e3 -
        (algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ (gm - 1)) -
          9 * (ShimuraGlue.nrdQ AQ ((k⁻¹ : BAQˣ) : BAQ) * ShimuraGlue.nrdQ AQ y)) * hgg
    have hM9 : algebraMap ℚ AQ (ShimuraGlue.nrdQ ℚ (gm - 1) / 9) =
        ShimuraGlue.nrdQ AQ ((k⁻¹ : BAQˣ) : BAQ) * ShimuraGlue.nrdQ AQ y := by
      rw [show ShimuraGlue.nrdQ ℚ (gm - 1) / 9 = (1 / 9) * ShimuraGlue.nrdQ ℚ (gm - 1) by ring,
        map_mul, hM, ← mul_assoc, ← map_ofNat (algebraMap ℚ AQ) 9, ← map_mul]
      norm_num
    have hmem : ShimuraGlue.nrdQ AQ ((k⁻¹ : BAQˣ) : BAQ) * ShimuraGlue.nrdQ AQ y ∈ ZhatQ :=
      zhatSubring.mul_mem (nrd_mem_ZhatQ hk2) (nrd_mem_ZhatQ hy)
    obtain ⟨m, hm⟩ := exists_int_of_mem (hM9 ▸ hmem)
    exact ⟨m, by rw [← hm]; ring⟩

/-! ## 2. Fixed points of real Möbius transformations -/

/-- If `M = (a b; c d)` fixes a non-real `z = x + iy`, then `a - d = 2cx` and `b = -c(x² + y²)`. -/
theorem fixed_point_eqs (M : GL (Fin 2) ℝ) (z : Y3Hodge.HPM) (h : Y3Hodge.mobPM M z = z) :
    (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1 =
        2 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (z : ℂ).re ∧
      (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
        -((M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * ((z : ℂ).re ^ 2 + (z : ℂ).im ^ 2)) := by
  have hz : (z : ℂ).im ≠ 0 := z.2
  have h1 : UpperHalfPlane.num M (z : ℂ) / UpperHalfPlane.denom M (z : ℂ) = (z : ℂ) :=
    congrArg Subtype.val h
  have hd : UpperHalfPlane.denom M (z : ℂ) ≠ 0 := by
    intro hd
    rw [hd, div_zero] at h1
    exact hz (by rw [← h1]; simp)
  have h2 := (div_eq_iff hd).mp h1
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom] at h2
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im] at hre him
  have hA : (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1 =
      2 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (z : ℂ).re := by
    have : ((M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1) * (z : ℂ).im =
        (2 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (z : ℂ).re) * (z : ℂ).im := by
      linear_combination him
    exact mul_right_cancel₀ hz this
  refine ⟨hA, ?_⟩
  linear_combination hre - (z : ℂ).re * hA

/-! ## 3. Freeness -/

theorem iota_entry00 (x : LeafQM.B) :
    BPAnalytic.QM.iota x 0 0 = (x.re : ℝ) + x.imI * √2 := by
  rw [Datum.iota_eq]; rfl

theorem iota_entry01 (x : LeafQM.B) :
    BPAnalytic.QM.iota x 0 1 = -3 * (x.imJ : ℝ) - 3 * x.imK * √2 := by
  rw [Datum.iota_eq]; rfl

theorem iota_entry10 (x : LeafQM.B) :
    BPAnalytic.QM.iota x 1 0 = (x.imJ : ℝ) - x.imK * √2 := by
  rw [Datum.iota_eq]; rfl

theorem iota_entry11 (x : LeafQM.B) :
    BPAnalytic.QM.iota x 1 1 = (x.re : ℝ) - x.imI * √2 := by
  rw [Datum.iota_eq]; rfl

/-- `nrd(γ - 1) = nrd γ - 2 re γ + 1`. -/
theorem nrd_sub_one (x : LeafQM.B) :
    ShimuraGlue.nrdQ ℚ (x - 1) = ShimuraGlue.nrdQ ℚ x - 2 * x.re + 1 := by
  rw [ShimuraGlue.nrdQ_apply, ShimuraGlue.nrdQ_apply]
  simp
  ring

/-- **`B^×` acts freely on `ℍ^± × (B ⊗ 𝔸_f)^× / K₃`.** If `γ ∈ B^×` fixes `z ∈ ℍ^±` and
`g = γ g k` with `k ∈ K₃`, then `γ = 1`; i.e. every `Γ_g = B^× ∩ g K₃ g⁻¹` acts freely on `ℍ^±`.
This is the property for which Milne asks `K` to be sufficiently small (*Introduction to Shimura
varieties*, Clay Math. Proc. 4 (2005), p. 307). -/
theorem stabilizer_trivial (z : Y3Hodge.HPM) (g : BAQˣ) (gm : LeafQM.B)
    (hγ : ShimuraGlue.nrdQ ℚ gm ≠ 0) (hfix : Y3Hodge.mobPM (RayClassCFT.iotaGL gm hγ) z = z)
    (k : BAQˣ) (hk : k ∈ K3Q) (hg : (g : BAQ) = bEmb gm * g * k) :
    gm = 1 := by
  obtain ⟨hN, m, hm⟩ := integrality gm hγ g k hk hg
  obtain ⟨hA, hB⟩ := fixed_point_eqs _ z hfix
  rw [RayClassCFT.iotaGL_coe, iota_entry00, iota_entry11, iota_entry10] at hA
  rw [RayClassCFT.iotaGL_coe, iota_entry01, iota_entry10] at hB
  have hs : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (√2 : ℝ) ≠ 0 := by positivity
  have hy : (z : ℂ).im ≠ 0 := z.2
  have hNR : ((ShimuraGlue.nrdQ ℚ gm : ℚ) : ℝ) = (gm.re : ℝ) ^ 2 - 2 * (gm.imI : ℝ) ^ 2 +
      3 * (gm.imJ : ℝ) ^ 2 - 6 * (gm.imK : ℝ) ^ 2 := by
    rw [ShimuraGlue.nrdQ_apply]; push_cast; ring
  have key : (gm.re : ℝ) ^ 2 - ((ShimuraGlue.nrdQ ℚ gm : ℚ) : ℝ) =
      -(((gm.imJ : ℝ) - gm.imK * √2) ^ 2 * (z : ℂ).im ^ 2) := by
    rw [hNR]
    linear_combination ((gm.imI : ℝ) * √2 + ((gm.imJ : ℝ) - gm.imK * √2) * (z : ℂ).re) / 2 * hA +
      ((gm.imJ : ℝ) - gm.imK * √2) * hB - ((gm.imI : ℝ) ^ 2 + 3 * (gm.imK : ℝ) ^ 2) * hs
  have hpos : 0 ≤ ((gm.imJ : ℝ) - gm.imK * √2) ^ 2 * (z : ℂ).im ^ 2 := by positivity
  have hle : (gm.re : ℝ) ^ 2 ≤ ((ShimuraGlue.nrdQ ℚ gm : ℚ) : ℝ) := by linarith
  have hleQ : gm.re ^ 2 ≤ ShimuraGlue.nrdQ ℚ gm := by exact_mod_cast hle
  rcases hN with hN1 | hN1
  swap
  · rw [hN1] at hleQ
    nlinarith [sq_nonneg gm.re]
  have h2re : 2 * gm.re = 2 - 9 * (m : ℚ) := by
    have := nrd_sub_one gm
    rw [hm, hN1] at this
    linarith
  have ht : (2 - 9 * (m : ℚ)) ^ 2 ≤ 4 := by
    rw [hN1] at hleQ
    rw [← h2re]; nlinarith
  have hlo : (-2 : ℚ) ≤ 2 - 9 * (m : ℚ) := by nlinarith
  have hhi : 2 - 9 * (m : ℚ) ≤ 2 := by nlinarith
  have hlo' : (-2 : ℤ) ≤ 2 - 9 * m := by exact_mod_cast hlo
  have hhi' : 2 - 9 * m ≤ (2 : ℤ) := by exact_mod_cast hhi
  have hm0 : m = 0 := by omega
  have hre : gm.re = 1 := by rw [hm0] at h2re; push_cast at h2re; linarith
  have hreR : (gm.re : ℝ) = 1 := by exact_mod_cast hre
  have hNR1 : ((ShimuraGlue.nrdQ ℚ gm : ℚ) : ℝ) = 1 := by rw [hN1]; norm_num
  rw [hreR, hNR1] at key
  have hc2 : ((gm.imJ : ℝ) - gm.imK * √2) ^ 2 * (z : ℂ).im ^ 2 = 0 := by linarith
  have hc : (gm.imJ : ℝ) - gm.imK * √2 = 0 := by
    rcases mul_eq_zero.mp hc2 with h | h
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hy
  rw [hc] at hA hB
  have hI : (gm.imI : ℝ) * √2 = 0 := by linarith
  have hK : (gm.imK : ℝ) * √2 = 0 := by linarith
  have hIR : (gm.imI : ℝ) = 0 := by
    rcases mul_eq_zero.mp hI with h | h
    · exact h
    · exact absurd h hs0
  have hKR : (gm.imK : ℝ) = 0 := by
    rcases mul_eq_zero.mp hK with h | h
    · exact h
    · exact absurd h hs0
  have hJR : (gm.imJ : ℝ) = 0 := by rw [hKR] at hc; linarith
  have hI' : gm.imI = 0 := by exact_mod_cast hIR
  have hJ' : gm.imJ = 0 := by exact_mod_cast hJR
  have hK' : gm.imK = 0 := by exact_mod_cast hKR
  ext <;> simp [hre, hI', hJ', hK']

end DelignePSMilne.Freeness
