import ZInQKernel.Contrib.OneProof.T21Proof.K2

/-!
# t21-proof: the double coset of `1` in `B^× \ B̂^× / ℚ̂^× U_3`

Task t21-proof. For an admissible `τ` (signs `s`) and the place `v` above `2`:
* `Sg v s`: the subgroup of `B̂^×` of elements lying in `ℚ_p^× O_{B,p}^×` at odd places and in
  `ℚ_2^× R_2^×` at `v`;
* `H τ = ⟨U_3, ℚ̂^×⟩ ≤ Sg v s` (`H_le_Sg`): the generators `R̂_3^×` (via `tauHat_integral`),
  `K_{3,2}^×` (via `loc2OK_of_commute`) and the centre;
* `twoRep_not_mem`: for the 6 classes `t ∉ {0, t*}`, `twoRep v t ∉ B^× H`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open ZInQ.Contrib.TYZDecomp.H29Split IsDedekindDomain NumberField
open scoped Quaternion FiniteAdeleExtension
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! ## Local lemmas -/

theorem eq_of_mul_eq_one' {p : ℕ} [Fact p.Prime] {c : ℚ_[p]} {u z : ℍ[ℚ_[p]]} (hc : c ≠ 0)
    (hn : Quaternion.normSq u ≠ 0) (h : z * (c • u) = 1) :
    z = c⁻¹ • ((Quaternion.normSq u)⁻¹ • star u) := by
  have h1 : (z * (c • u)) * star u = star u := by rw [h, one_mul]
  have h2 : (z * (c • u)) * star u = (c * Quaternion.normSq u) • z := by
    rw [mul_assoc, smul_mul_assoc, Quaternion.self_mul_star, ← Quaternion.coe_mul_eq_smul,
      ← Quaternion.coe_mul, Quaternion.mul_coe_eq_smul]
  rw [h2] at h1
  rw [← h1, smul_smul, smul_smul, ← mul_assoc, mul_comm c⁻¹, mul_assoc]
  have : c⁻¹ * (c * Quaternion.normSq u) = Quaternion.normSq u := by field_simp
  rw [mul_assoc, this, inv_mul_cancel₀ hn, one_smul]

theorem LocOK.of_mul_eq_one' {p : ℕ} [Fact p.Prime] {y z : ℍ[ℚ_[p]]} (hy : LocOK y)
    (h : z * y = 1) : LocOK z := by
  obtain ⟨c, hc, u, rfl, hu, hn⟩ := hy
  exact ⟨c⁻¹, inv_ne_zero hc, _, eq_of_mul_eq_one' hc (normSq_ne_zero_of hn) h,
    isHur_inv_star hu hn, normSq_inv_star hn⟩

theorem InR.zero {p : ℕ} [Fact p.Prime] {ω : ℍ[ℚ_[p]]} : InR ω 0 :=
  ⟨0, 0, by simp, by simp, 0, isHur_zero, by simp⟩

theorem InR.add {p : ℕ} [Fact p.Prime] {ω u u' : ℍ[ℚ_[p]]} (hu : InR ω u) (hu' : InR ω u') :
    InR ω (u + u') := by
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hu
  obtain ⟨x', z', hx', hz', a', ha', rfl⟩ := hu'
  refine ⟨x + x', z + z', (Zp p).add_mem hx hx', (Zp p).add_mem hz hz', a + a', ha.add ha', ?_⟩
  simp only [add_smul, smul_add]; abel

theorem InR.neg {p : ℕ} [Fact p.Prime] {ω u : ℍ[ℚ_[p]]} (hu : InR ω u) : InR ω (-u) := by
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hu
  refine ⟨-x, -z, by rwa [norm_neg], by rwa [norm_neg], -a, ?_, ?_⟩
  · simpa using ha.smul ((Zp p).neg_mem (Zp p).one_mem)
  · simp only [neg_smul, smul_neg, neg_add]

theorem ωp_mul {p : ℕ} [Fact p.Prime] (s : Signs) :
    qp p (ωq s) * qp p (ωq s) = qp p (ωq s) - 1 := by
  rw [qp_ωq]
  have h1 := sgp_sq (p := p) s.1
  have h2 := sgp_sq (p := p) s.2.1
  have h3 := sgp_sq (p := p) s.2.2
  ext <;> simp
  · linear_combination (-1/4 : ℚ_[p]) * h1 - (1/4 : ℚ_[p]) * h2 - (1/4 : ℚ_[p]) * h3
  all_goals ring

theorem ωp_star {p : ℕ} [Fact p.Prime] (s : Signs) :
    star (qp p (ωq s)) = 1 - qp p (ωq s) := by
  rw [qp_ωq]; ext <;> simp <;> ring

/-! ## The subgroup `Sg` -/

/-- The local condition at a place `w`. -/
def Cond (v : HeightOneSpectrum (𝓞 ℚ)) (s : Signs) (w : HeightOneSpectrum (𝓞 ℚ))
    (y : ℍ[ℚ_[Pw w]]) : Prop :=
  (w = v → Loc2OK (qp (Pw w : ℕ) (ωq s)) y) ∧ (w ≠ v → LocOK y)

theorem Cond.mul {v : HeightOneSpectrum (𝓞 ℚ)} {s : Signs} {w} {y z : ℍ[ℚ_[Pw w]]}
    (hy : Cond v s w y) (hz : Cond v s w z) : Cond v s w (y * z) :=
  ⟨fun h => (hy.1 h).mul (isHur_qp_hurZ _) (ωp_mul s) (hz.1 h),
    fun h => (hy.2 h).mul (hz.2 h)⟩

theorem Cond.one {v : HeightOneSpectrum (𝓞 ℚ)} {s : Signs} {w} : Cond v s w 1 :=
  ⟨fun _ => Loc2OK.one, fun _ => LocOK.one⟩

theorem Cond.of_mul_eq_one {v : HeightOneSpectrum (𝓞 ℚ)} {s : Signs} {w} {y z : ℍ[ℚ_[Pw w]]}
    (hy : Cond v s w y) (h : y * z = 1) : Cond v s w z :=
  ⟨fun hw => (hy.1 hw).of_mul_eq_one (ωp_star s) h, fun hw => (hy.2 hw).of_mul_eq_one h⟩

/-- **The subgroup `Sg v s ⊂ B̂^×`**: `ℚ_p^× O_{B,p}^×` at odd places, `ℚ_2^× R_2^×` at `v`. -/
def Sg (v : HeightOneSpectrum (𝓞 ℚ)) (s : Signs) : Subgroup ℍ[AQ]ˣ where
  carrier := {h | ∀ w, Cond v s w (piQ w (h : ℍ[AQ]))}
  mul_mem' {a b} ha hb w := by
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    exact (ha w).mul (hb w)
  one_mem' w := by simp only [Units.val_one, map_one]; exact Cond.one
  inv_mem' {a} ha w := by
    refine (ha w).of_mul_eq_one ?_
    rw [← map_mul, Units.mul_inv, map_one]

/-! ## The generators -/

/-- `H τ = ⟨U_3, ℚ̂^×⟩`. -/
def Hgrp (τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]) : Subgroup ℍ[AQ]ˣ :=
  Subgroup.closure ((Un 3 τ : Set ℍ[AQ]ˣ) ∪ Set.range (Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom))

theorem centre_mem_Sg (v : HeightOneSpectrum (𝓞 ℚ)) (s : Signs) (z : AQˣ) :
    Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom z ∈ Sg v s := by
  intro w
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, piQ_algebraMap]
  have hz : ev w (z : AQ) ≠ 0 := by
    intro h0
    have := congrArg (ev w) z.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have he : ((ev w z : ℚ_[Pw w]) : ℍ[ℚ_[Pw w]]) = (ev w z) • (1 : ℍ[ℚ_[Pw w]]) := by
    rw [← Quaternion.coe_mul_eq_smul, mul_one]
  rw [he]
  exact ⟨fun _ => ⟨_, hz, 1, rfl, isHur_one, by simp, InR.one⟩,
    fun _ => ⟨_, hz, 1, rfl, isHur_one, by simp⟩⟩

theorem piQ_eq_one_of_comps {w : HeightOneSpectrum (𝓞 ℚ)} {y : ℍ[AQ]}
    (h : y.re w = 1 ∧ y.imI w = 0 ∧ y.imJ w = 0 ∧ y.imK w = 0) : piQ w y = 1 := by
  ext <;> simp [piQ, ev_apply, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem commute_ω_of {p : ℕ} [Fact p.Prime] {s : Signs} {τ' : ℍ[ℚ]} (hτ' : τ' = 2)
    {y : ℍ[ℚ_[p]]}
    (h : y * qp p (τ' * ωq s - 1) = qp p (τ' * ωq s - 1) * y) :
    y * qp p (ωq s) = qp p (ωq s) * y := by
  subst hτ'
  have e : qp p ((2 : ℍ[ℚ]) * ωq s - 1) = (2 : ℚ_[p]) • qp p (ωq s) - 1 := by
    rw [map_sub, map_mul, map_one, ← Quaternion.coe_mul_eq_smul]
    congr 1
  rw [e, mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc] at h
  have h' : (2 : ℚ_[p]) • (y * qp p (ωq s)) = (2 : ℚ_[p]) • (qp p (ωq s) * y) := by
    have := congrArg (· + y) h
    simpa using this
  exact smul_right_injective _ two_ne_zero h'

theorem K2Units_sub_Sg {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceTwo v) {s : Signs}
    {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} (hs : τ ((ωK : 𝓞 (QNeg 3)) : QNeg 3) = ωq s) :
    K2Units 3 τ ⊆ Sg v s := by
  intro k hk w
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · subst hw
    have hc := congrArg (piQ w) hk.1.eq
    rw [map_mul, map_mul, piQ_qι, sqrtNeg_eq, map_sub, map_mul, map_one, hs] at hc
    have hc' := commute_ω_of (s := s) (map_ofNat τ 2) hc
    have hne : piQ w ↑k ≠ 0 := by
      intro h0
      have := congrArg (piQ w) k.mul_inv
      rw [map_mul, h0, zero_mul, map_one] at this
      exact zero_ne_one this
    exact loc2OK_of_commute (Pw_eq_two hv) s hne hc'
  · rw [piQ_eq_one_of_comps (hk.2 w (not_isPlaceTwo_of_ne hv hw))]
    exact LocOK.one

end ZInQ.Contrib.T21Proof
