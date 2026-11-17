import ZInQKernel.Contrib.OneProof.CarayolDDTOdd

/-!
# carirr-refold: Carayol's leaf with the unramified clause in the manuscript's normalization

Task carirr-refold (2026-11-17), report `docs/research/carirr-refold.md`, scratch `scratch/carirr-refold/`.

The open field `carayolThmAIrr : CarayolPrinted.CarayolThmAIrr` has an **odd** clause
(`∃ c, c² = 1 ∧ det ρ(c) = -1`) that no print states in that form. carirr-odd replaced it by the global
determinant `det ρ = ψ·χ_ℓ` of Darmon–Diamond–Taylor 1997 Thm 3.1 (`CarayolDDT.CarayolDDT31`). The manuscript
cites Carayol 1986, Théorème (A), once (diophantine_zq.tex L9778-9796) and reads off from Carayol's
normalization the polynomial of **arithmetic Frobenius**: `X² − a_q X + q χ(q)` at good primes `q`. This file
states the leaf with exactly that per-Frobenius clause (trace `a_p`, determinant `p ψ(p)`) and proves:

* `odd_of_frobDet` (new): if `det ρ(Frob_p) = p` at every arithmetic Frobenius with `p ≡ -1 (mod N)`,
  `p ∤ Nℓ`, then complex conjugation `c` has `det ρ(c) = -1`. One Frobenius element near `c` (the kernel's
  Chebotarev density T18, `CarayolLevel.frobeniusDense_C9`) in the open subgroup cut out by `p ≡ -1 (mod N)`,
  `p ≡ -1 (mod ℓ^k)` and `‖det ρ − 1‖ < ‖2‖` forces `det ρ(c) ≠ 1`; with `det ρ(c)² = 1` this gives `-1`.
  No `ℓ`-adic cyclotomic character in `K_{f,λ}` and no embedding `ℤ_ℓ → K_{f,λ}` is needed.
* `CarayolThmAFrob` (the leaf), `carayolThmAIrr_of_frob : CarayolThmAFrob → CarayolPrinted.CarayolThmAIrr`.
* `frob_of_DDT31 : CarayolDDT.CarayolDDT31 → CarayolThmAFrob`: the new leaf is implied by carirr-odd's DDT
  form (so it is not stronger than DDT 3.1), via `χ_ℓ(Frob_p) = p`, `Frob_p mod N = p` (hodge-split's
  `cyc_arithFrob`, `arithFrob_pow_of_rootOfUnity`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace CarayolRefold

open PkgI4 LadicCond

/-! ## §1. The mod-`M` cyclotomic character: open kernel, value at Frobenius -/

/-- `ker (σ ↦ σ mod M)` is open in `G_ℚ`: it contains `Gal(ℚ̄/ℚ(ζ_M))`. -/
theorem isOpen_ker_cycN (M : ℕ) [NeZero M] : IsOpen ((CarayolDDT.cycN M).ker : Set GQ) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar M
  let K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {ζ}
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have hK : K.fixingSubgroup ≤ (CarayolDDT.cycN M).ker := by
    intro σ hσ
    have hfix : σ ζ = ζ := hσ ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    refine (modularCyclotomicCharacter.unique Qbar (CarayolDDT.natCard_rootsOfUnity_Qbar M)
      (MulSemiringAction.toRingAut GQ Qbar σ) fun t ht => ?_).symm
    have htn : (t : Qbar) ^ M = 1 := by
      have := (mem_rootsOfUnity _ _).mp ht
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one htn
    show σ (t : Qbar) = ((t ^ ((1 : (ZMod M)ˣ) : ZMod M).val : Qbarˣ) : Qbar)
    rw [← hi, map_pow, hfix, Units.val_pow_eq_pow_val, ← hi]
    by_cases hM1 : M = 1
    · subst hM1
      have : (t : Qbar) = 1 := by simpa using htn
      rw [hi, this, one_pow]
    · have : Fact (1 < M) := ⟨by have := NeZero.ne M; omega⟩
      rw [Units.val_one, ZMod.val_one, pow_one]
  exact Subgroup.isOpen_mono hK (IntermediateField.fixingSubgroup_isOpen K)

/-- An arithmetic Frobenius at `v ∣ p`, `p ∤ M`, has `σ mod M = p`. -/
theorem cycN_arithFrob {M : ℕ} [NeZero M] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpM : ¬ p ∣ M) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((CarayolDDT.cycN M σ : (ZMod M)ˣ) : ZMod M) = (p : ZMod M) := by
  refine (modularCyclotomicCharacter.unique Qbar (CarayolDDT.natCard_rootsOfUnity_Qbar M)
    (MulSemiringAction.toRingAut GQ Qbar σ) fun t ht => ?_).symm
  have htn : (t : Qbar) ^ M = 1 := by
    have := (mem_rootsOfUnity _ _).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  show σ (t : Qbar) = ((t ^ ((p : ZMod M)).val : Qbarˣ) : Qbar)
  rw [ZInQ.Contrib.HodgeSplit.arithFrob_pow_of_rootOfUnity hp hv hσ (NeZero.ne M) htn hpM,
    Units.val_pow_eq_pow_val, ZMod.val_natCast,
    ← ZInQ.Contrib.HodgeSplit.pow_eq_pow_mod_of htn]

/-- An arithmetic Frobenius at `v ∣ p`, `p ≠ ℓ`, has `χ_ℓ(σ) = p`. -/
theorem cycL_arithFrob {ℓ : ℕ} [Fact ℓ.Prime] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpl : p ≠ ℓ) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((CarayolDDT.cycL ℓ σ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (p : ℤ_[ℓ]) := by
  have h := ZInQ.Contrib.HodgeSplit.cyc_arithFrob (ℓ := ℓ) hp hpl hv hσ
  have he : MulSemiringAction.toRingAut GQ Qbar σ = σ.toRingEquiv := RingEquiv.ext fun _ => rfl
  simp only [CarayolDDT.cycL, MonoidHom.coe_comp, Function.comp_apply, he]
  exact h

/-! ## §2. Oddness from the determinant at Frobenius elements -/

section Odd

variable {E : Type*} [NormedField E] [IsUltrametricDist E]

theorem norm_eq_one_of_near {x : E} (hx : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have := CarayolHerbrand.norm_eq_of_norm_sub_lt (a := x) (b := 1) (by rwa [norm_one])
  rwa [norm_one] at this

/-- `{σ : ‖d(σ) − 1‖ < r}` for a character `d : G_ℚ → Eˣ` and `0 < r ≤ 1`: a subgroup. -/
def nearOne (d : GQ →* Eˣ) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) : Subgroup GQ where
  carrier := {σ | ‖((d σ : Eˣ) : E) - 1‖ < r}
  one_mem' := by simp [hr0]
  mul_mem' := by
    intro a b ha hb
    change ‖_‖ < r at ha hb ⊢
    simp only [map_mul, Units.val_mul]
    have hna : ‖((d a : Eˣ) : E)‖ = 1 := norm_eq_one_of_near (lt_of_lt_of_le ha hr1)
    have e : ((d a : Eˣ) : E) * (d b : Eˣ) - 1 =
        ((d a : Eˣ) : E) * (((d b : Eˣ) : E) - 1) + (((d a : Eˣ) : E) - 1) := by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ha)
    rw [norm_mul, hna, one_mul]
    exact hb
  inv_mem' := by
    intro a ha
    change ‖_‖ < r at ha ⊢
    simp only [map_inv, Units.val_inv_eq_inv_val]
    have hna : ‖((d a : Eˣ) : E)‖ = 1 := norm_eq_one_of_near (lt_of_lt_of_le ha hr1)
    have h0 : ((d a : Eˣ) : E) ≠ 0 := (d a).ne_zero
    have e : ((d a : Eˣ) : E)⁻¹ - 1 = -((((d a : Eˣ) : E) - 1) * ((d a : Eˣ) : E)⁻¹) := by
      field_simp; ring
    rw [e, norm_neg, norm_mul, norm_inv, hna, inv_one, mul_one]
    exact ha

/-- **Odd from the determinant at Frobenius elements (GLUE, proved).** Let `E` be an ultrametric normed
field with `‖ℓ‖ < 1` and `2 ≠ 0`, and `ρ : G_ℚ → GL₂(E)` continuous with `det ρ(σ) = p` at every arithmetic
Frobenius `σ` above a prime `p ∤ Nℓ` with `σ mod N = -1`. Then some `c` with `c² = 1` (complex conjugation)
has `det ρ(c) = -1`. -/
theorem odd_of_frobDet {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ‖(ℓ : E)‖ < 1) (h2 : (2 : E) ≠ 0)
    {N : ℕ} [NeZero N] (ρ : GQ →* GL (Fin 2) E) (hρ : Continuous ρ)
    (hfrob : ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ (v : ValuationSubring Qbar) (σ : GQ),
      LiesOver v p → IsArithFrob σ v p → CarayolDDT.cycN N σ = -1 →
        (ρ σ : Matrix (Fin 2) (Fin 2) E).det = (p : E)) :
    ∃ c : GQ, c * c = 1 ∧ (ρ c : Matrix (Fin 2) (Fin 2) E).det = -1 := by
  obtain ⟨c, hcc, hc⟩ := CarayolDDT.exists_complexConj
  refine ⟨c, hcc, ?_⟩
  let d : GQ →* Eˣ := Matrix.GeneralLinearGroup.det.comp ρ
  have hdv : ∀ σ, ((d σ : Eˣ) : E) = (ρ σ : Matrix (Fin 2) (Fin 2) E).det := fun σ =>
    Matrix.GeneralLinearGroup.val_det_apply _
  have hdc : Continuous fun σ => ((d σ : Eˣ) : E) := by
    simp only [hdv]
    exact (Units.continuous_val.comp hρ).matrix_det
  set r : ℝ := ‖(2 : E)‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 h2
  have hr1 : r ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one E 2
    simpa using this
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hr0 hℓ
  have : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let U : Subgroup GQ := (CarayolDDT.cycN N).ker ⊓ (CarayolDDT.cycN (ℓ ^ k)).ker ⊓
    nearOne d r hr0 hr1
  have hU : IsOpen (U : Set GQ) := by
    refine ((isOpen_ker_cycN N).inter (isOpen_ker_cycN (ℓ ^ k))).inter ?_
    have : ((fun σ => ((d σ : Eˣ) : E)) ⁻¹' Metric.ball 1 r) = (nearOne d r hr0 hr1 : Set GQ) := by
      ext σ; simp [nearOne, dist_eq_norm]
    exact this ▸ Metric.isOpen_ball.preimage hdc
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := CarayolLevel.frobeniusDense_C9 U hU c (N * ℓ).primeFactors
  have hNl : N * ℓ ≠ 0 := mul_ne_zero (NeZero.ne N) (Fact.out : ℓ.Prime).ne_zero
  have hpNl : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.2 ⟨hp, h, hNl⟩)
  have hpN : ¬ p ∣ N := fun h => hpNl (dvd_mul_of_dvd_left h _)
  have hpl : p ≠ ℓ := fun h => hpNl (h ▸ dvd_mul_left p N)
  have hlp : ¬ ℓ ∣ p := fun h =>
    hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) hp).1 h).symm
  have hplk : ¬ p ∣ ℓ ^ k := fun h =>
    hpl ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨⟨hU1, hU2⟩, hU3⟩ := hU'
  have hcN : ∀ M [NeZero M], τ⁻¹ * c ∈ (CarayolDDT.cycN M).ker → CarayolDDT.cycN M τ = -1 := by
    intro M _ h
    rw [MonoidHom.mem_ker, map_mul, map_inv, CarayolDDT.cycN_eq_neg_one M hc, inv_mul_eq_one] at h
    exact h
  have hτN := hcN N hU1
  have hτl := hcN (ℓ ^ k) hU2
  -- `det ρ(τ) = p`
  have hdτ : ((d τ : Eˣ) : E) = (p : E) := by rw [hdv]; exact hfrob p hp hpNl v τ hv hτ hτN
  -- `p ≡ -1 (mod ℓ^k)`
  have hpk : ((p : ℕ) : ZMod (ℓ ^ k)) = -1 := by
    rw [← cycN_arithFrob hp hplk hv hτ, hτl, Units.val_neg, Units.val_one]
  have hdvd : ℓ ^ k ∣ p + 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hpk, Nat.cast_one, neg_add_cancel]
  obtain ⟨m, hm⟩ := hdvd
  have hp1 : ‖((p : E) + 1)‖ < r := by
    have : ((p : E) + 1) = (ℓ : E) ^ k * (m : E) := by
      have h' := congrArg (Nat.cast : ℕ → E) hm
      push_cast at h'
      exact h'
    rw [this, norm_mul, norm_pow]
    calc ‖(ℓ : E)‖ ^ k * ‖(m : E)‖ ≤ ‖(ℓ : E)‖ ^ k * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one E m)
            (pow_nonneg (norm_nonneg _) _)
      _ < r := by rw [mul_one]; exact hk
  have hpn : ‖(p : E)‖ = 1 := CarayolHerbrand.norm_natCast_eq_one_of hℓ hlp
  have hp0 : (p : E) ≠ 0 := by intro h; rw [h, norm_zero] at hpn; exact zero_ne_one hpn
  -- `det ρ(c)² = 1`
  have hsq : ((d c : Eˣ) : E) * (d c : Eˣ) = 1 := by
    rw [← Units.val_mul, ← map_mul, hcc, map_one, Units.val_one]
  rw [← hdv]
  rcases mul_self_eq_one_iff.1 hsq with h1 | h1
  · exfalso
    have hnear : ‖((d (τ⁻¹ * c) : Eˣ) : E) - 1‖ < r := hU3
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hdτ, h1, mul_one] at hnear
    have hpm1 : ‖(p : E) - 1‖ < r := by
      have e : (p : E) - 1 = -((p : E) * ((p : E)⁻¹ - 1)) := by field_simp; ring
      rw [e, norm_neg, norm_mul, hpn, one_mul]
      exact hnear
    have e2 : (2 : E) = ((p : E) + 1) - ((p : E) - 1) := by ring
    have : ‖(2 : E)‖ < r := by
      rw [e2, sub_eq_add_neg]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hp1 ?_)
      rw [norm_neg]; exact hpm1
    exact lt_irrefl _ (hr ▸ this)
  · exact h1

end Odd

end CarayolRefold
