import ZInQKernel.Contrib.OneProof.HfxProof.Assembly
import ZInQKernel.Contrib.OneProof.HfxProof.ClassOne
import ZInQKernel.Contrib.OneProof.HfxProof.Finite25

/-!
# hfx-proof: every unit of `B̂` lies in one of TYZ's 8 double cosets

Task hfx-proof. TYZ Lemma 2.5 (L645–661), surjectivity half: for every `n`, admissible or not `τ`, and
the place `v` above `2`, every `x ∈ B̂^×` lies in `B^× twoRep(v, t) H` for some `t`
(`exists_twoRep`). Proof: `x = qι γ · u` with `u ∈ Ô_B^×` (`exists_global_mul_unit`); `u_2 ≡ ± μ β_t
(mod 4)` (`lemma25_check`); and `(± μ twoRep t)⁻¹ u ∈ 1 + 4Ô_B ⊂ R̂_n^× ⊂ H`.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! ## `Ô_B` from local data, and `1 + 4Ô_B ⊂ R̂_n` -/

theorem two_mul_half : (2 : AQ) * algebraMap ℚ AQ (1 / 2) = 1 := by
  rw [← map_ofNat (algebraMap ℚ AQ) 2, ← map_mul]; norm_num

/-- **`Ô_B` is read place by place.** -/
theorem mem_hurwitzHat_of_LH {y : ℍ[AQ]} (h : LH y) : y ∈ hurwitzHat := by
  have hI : ∀ a : AQ, (∀ w, ev w a ∈ Zp (Pw w : ℕ)) → a ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ :=
    fun a ha => integral_of_ev fun w => mem_Zp.mp (ha w)
  refine ⟨y.re + y.imK, y.imI - y.imK, y.imJ - y.imK, 0, 2 * y.imK, ?_, ?_, ?_,
    Subalgebra.zero_mem _, ?_, ?_⟩
  · exact hI _ fun w => by rw [map_add]; exact (h w).1
  · exact hI _ fun w => by rw [map_sub]; exact (h w).2.1
  · exact hI _ fun w => by rw [map_sub]; exact (h w).2.2.1
  · exact hI _ fun w => by rw [map_mul, map_ofNat]; exact (h w).2.2.2
  · have e : ∀ a : AQ, 2 * a * algebraMap ℚ AQ (1 / 2) = a := fun a => by
      rw [mul_comm 2 a, mul_assoc, two_mul_half, mul_one]
    apply QuaternionAlgebra.ext <;> dsimp only <;> rw [e] <;> ring

theorem piQ_qsmul (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) (x : ℍ[AQ]) :
    piQ w (q • x) = (q : ℚ_[Pw w]) • piQ w x := by
  have : q • x = algebraMap AQ ℍ[AQ] (algebraMap ℚ AQ q) * x := by
    rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  rw [this, map_mul, piQ_algebraMap, ev_algebraMap, Quaternion.coe_mul_eq_smul]

/-- `1 + 4Ô_B ⊂ R̂_n`. -/
theorem mem_RnHat_of {n : ℕ} [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) {x : ℍ[AQ]}
    (h : LH ((1 / 4 : ℚ) • (x - 1))) : x ∈ RnHat n τ := by
  have hx : x = tauHat n τ 1 + 4 * ((1 / 4 : ℚ) • (x - 1)) := by
    rw [map_one, mul_smul_comm, ← smul_mul_assoc]
    have : (1 / 4 : ℚ) • (4 : ℍ[AQ]) = 1 := by
      rw [show (4 : ℍ[AQ]) = (4 : ℚ) • (1 : ℍ[AQ]) by rw [ofNat_smul_eq_nsmul]; simp, smul_smul]
      norm_num
    rw [this, one_mul]; abel
  rw [hx]
  refine AddSubgroup.add_mem _ (AddSubgroup.subset_closure (Or.inl ⟨1, Subalgebra.one_mem _, rfl⟩))
    (AddSubgroup.subset_closure (Or.inr ⟨_, mem_hurwitzHat_of_LH h, rfl⟩))

theorem mem_HgrpN_of {n : ℕ} [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) {w : ℍ[AQ]ˣ}
    (h1 : LH ((1 / 4 : ℚ) • ((w : ℍ[AQ]) - 1))) (h2 : LH ((1 / 4 : ℚ) • (((w⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) - 1))) :
    w ∈ HgrpN n τ :=
  Subgroup.subset_closure (Or.inl (Subgroup.subset_closure (Or.inl ⟨mem_RnHat_of τ h1, mem_RnHat_of τ h2⟩)))

/-! ## The local step at `2` -/

theorem quarter_mem {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : ((1 / 4 : ℚ) : ℚ_[p]) ∈ Zp p := by
  rw [mem_Zp]
  have h4 : ‖((4 : ℕ) : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    have := Nat.Coprime.pow_right 2 ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp)
    simpa using this
  push_cast
  rw [norm_div, norm_one]
  have : ‖(4 : ℚ_[p])‖ = 1 := by exact_mod_cast h4
  rw [this]; norm_num

theorem red4_eq_zero_iff_norm {x : ℤ_[2]} (h : red4 x = 0) : ‖(x : ℚ_[2])‖ ≤ 1 / 4 := by
  rw [red4, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow] at h
  rw [← PadicInt.norm_def]; norm_num at h ⊢; exact h

theorem quarter_mul_mem {x : ℚ_[2]} (hx : ‖x‖ ≤ 1 / 4) : ((1 / 4 : ℚ) : ℚ_[2]) * x ∈ Zp 2 := by
  rw [mem_Zp, norm_mul]
  have : ‖((1 / 4 : ℚ) : ℚ_[2])‖ = 4 := by
    push_cast; rw [norm_div, norm_one]
    have : ‖(4 : ℚ_[2])‖ = 1 / 4 := by
      rw [show (4 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) ^ 2 by norm_num, Padic.norm_p_pow]; norm_num
    rw [this]; norm_num
  rw [this]; linarith

theorem red4_ne_zero_two_of_unit {x : ℤ_[2]} (hx : ‖(x : ℚ_[2])‖ = 1) : red4 x ≠ 0 ∧ red4 x ≠ 2 := by
  have key : ∀ c : ℤ_[2], ‖(c : ℚ_[2])‖ ≤ 1 / 2 → red4 (x - c) = 0 → False := by
    intro c hc h
    have h1 := red4_eq_zero_iff_norm h
    have : ‖(x : ℚ_[2])‖ ≤ 1 / 2 := by
      have e : (x : ℚ_[2]) = ((x - c : ℤ_[2]) : ℚ_[2]) + c := by push_cast; ring
      rw [e]
      exact (Padic.nonarchimedean _ _).trans (max_le (by linarith) hc)
    linarith
  constructor
  · intro h0
    exact key 0 (by simp) (by rw [sub_zero]; exact h0)
  · intro h2
    refine key 2 ?_ ?_
    · have : ‖((2 : ℤ_[2]) : ℚ_[2])‖ = 1 / 2 := by
        rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, PadicInt.coe_natCast, Padic.norm_p]
        norm_num
      rw [this]
    · have : red4 (2 : ℤ_[2]) = 2 := map_ofNat red4 2
      rw [map_sub, h2, this, sub_self]

/-- **The local step**: a Hurwitz `z ∈ ℍ[ℚ_2]` of unit norm is `± μ β_t` modulo `4O_{B,2}`. -/
theorem local25 {p : ℕ} [Fact p.Prime] (hp : p = 2) {z : ℍ[ℚ_[p]]} (hz : IsHur (Zp p) z)
    (hn : ‖Quaternion.normSq z‖ = 1) :
    ∃ μ ∈ unitList, ∃ s : Fin 2, ∃ t : Fin 2 × Fin 2 × Fin 2,
      IsHur (Zp p) (((1 / 4 : ℚ) : ℚ_[p]) • (z - qp p (hurZ (smulH (sg s) (mulH μ (βZ t)))))) := by
  subst hp
  obtain ⟨h0, h1, h2, h3⟩ := hz
  obtain ⟨Z, hZ⟩ : ∃ Z : H4 ℤ_[2], mapH PadicInt.Coe.ringHom Z = hc z :=
    ⟨⟨⟨_, mem_Zp.mp h0⟩, ⟨_, mem_Zp.mp h1⟩, ⟨_, mem_Zp.mp h2⟩, ⟨_, mem_Zp.mp h3⟩⟩, rfl⟩
  have hnZ : ‖((nrdH Z : ℤ_[2]) : ℚ_[2])‖ = 1 := by
    have : ((nrdH Z : ℤ_[2]) : ℚ_[2]) = Quaternion.normSq z := by
      rw [normSq_eq_nrdH, ← hZ, ← map_nrdH]; rfl
    rw [this, hn]
  obtain ⟨hr0, hr2⟩ := red4_ne_zero_two_of_unit hnZ
  rw [map_nrdH] at hr0 hr2
  obtain ⟨μ, hμ, s, he⟩ := lemma25_check _ _ _ _ hr0 hr2
  refine ⟨μ, hμ, s, tOf (scal4 (sg s : ZMod 4) (mulH (starH (mapH (Int.castRingHom (ZMod 4)) μ))
    ⟨red4 Z.a0, red4 Z.a1, red4 Z.a2, red4 Z.a3⟩)), ?_⟩
  generalize smulH (sg s) (mulH μ (βZ _)) = σ at he ⊢
  have hσ : hc (qp 2 (hurZ σ)) = mapH (Int.castRingHom ℚ_[2]) σ := by
    rw [qp_hurZ, hc_hurZ]
  simp only [IsHur, hc_smul, hc_sub, hσ, ← hZ]
  simp only [mapH, H4.mk.injEq] at he
  have key : ∀ (Zi : ℤ_[2]) (si : ℤ), red4 Zi = (Int.castRingHom (ZMod 4)) si →
      ((1 / 4 : ℚ) : ℚ_[2]) * (PadicInt.Coe.ringHom Zi - (Int.castRingHom ℚ_[2]) si) ∈ Zp 2 := by
    intro Zi si h
    refine quarter_mul_mem ?_
    have h' : red4 (Zi - si) = 0 := by rw [map_sub, h, map_intCast, eq_intCast, sub_self]
    have := red4_eq_zero_iff_norm h'
    simpa using this
  exact ⟨key _ _ he.1, key _ _ he.2.1, key _ _ he.2.2.1, key _ _ he.2.2.2⟩

end ZInQ.Contrib.HfxProof
