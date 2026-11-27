import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Place
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-! Algebraic and integral images of character values and phase-removed
rational scalars at the chosen place. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenPlace

open NumberField IsDedekindDomain HeightOneSpectrum

theorem character_value_pow {N e : ℕ} (χ : DirichletCharacter ℂ N)
    (hχ : χ ^ (2 ^ e) = 1) {x : ZMod N} (hx : IsUnit x) :
    χ x ^ (2 ^ e) = 1 := by
  rw [← MulChar.pow_apply' χ (pow_ne_zero _ two_ne_zero), hχ, MulChar.one_apply hx]

namespace Place

variable {F : IntermediateField ℚ ℂ} [NumberField F] (V : Place F)

theorem character_mem {e f N : ℕ} (V : Place (PhaseField e))
    (χ : DirichletCharacter ℂ N) (hχ : χ ^ (2 ^ f) = 1) (hf : f ≤ e) (x : ZMod N) :
    χ x ∈ V.complexIntegers := by
  by_cases hx : IsUnit x
  · have h := character_value_pow χ hχ hx
    exact V.root_mem_complexIntegers (phaseField_mem hf h) (by positivity) h
  · rw [χ.map_nonunit hx]
    exact V.complexIntegers.zero_mem

/-- The fixed complex embedding recovers the input value. -/
def fieldLift (z : ℂ) (hz : z ∈ V.complexIntegers) : F :=
  (show ∃ x : F, x ∈ (V.v.valuation F).valuationSubring.toSubring ∧ F.subtype x = z from hz).choose

theorem fieldLift_complex (z : ℂ) (hz : z ∈ V.complexIntegers) :
    F.subtype (V.fieldLift z hz) = z :=
  (show ∃ x : F, x ∈ (V.v.valuation F).valuationSubring.toSubring ∧ F.subtype x = z from hz).choose_spec.2

/-- The integral image in the completion of the same algebraic scalar. -/
def localLift (z : ℂ) (hz : z ∈ V.complexIntegers) : V.LocalIntegers :=
  ⟨FinitePlace.embedding V.v (V.fieldLift z hz),
    (V.mem_complexIntegers_iff _).mp (by
      change F.subtype (V.fieldLift z hz) ∈ V.complexIntegers
      rwa [V.fieldLift_complex])⟩

theorem localLift_eq (z : ℂ) (hz : z ∈ V.complexIntegers) :
    algebraMap V.LocalIntegers V.LocalField (V.localLift z hz) =
      FinitePlace.embedding V.v (V.fieldLift z hz) := rfl

theorem localLift_pow {z : ℂ} (hz : z ∈ V.complexIntegers) {m : ℕ} (h : z ^ m = 1) :
    V.localLift z hz ^ m = 1 := by
  have hF : (V.fieldLift z hz) ^ m = 1 := by
    apply F.subtype.injective
    rw [map_pow, V.fieldLift_complex, map_one, h]
  apply Subtype.ext
  change (FinitePlace.embedding V.v (V.fieldLift z hz)) ^ m = 1
  rw [← map_pow, hF, map_one]

theorem rat_mem (r : ℚ) (h : 0 ≤ padicValRat 2 r) : (r : ℂ) ∈ V.complexIntegers := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : ¬ 2 ∣ r.den := by
    intro hdiv
    have hn : ¬ 2 ∣ r.num.natAbs := fun e =>
      (by decide : ¬ 2 ∣ 1) (r.reduced ▸ Nat.dvd_gcd e hdiv)
    have hv₀ : padicValNat 2 r.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hn
    have hv₁ := one_le_padicValNat_of_dvd r.den_ne_zero hdiv
    rw [padicValRat, padicValInt, hv₀] at h
    omega
  rw [Rat.cast_def, div_eq_mul_inv]
  exact V.complexIntegers.mul_mem (intCast_mem _ _) (V.odd_inv_mem _ hd)

/-- The phase stays integral, and the specified factor is an integer
power of two. A shift can pay a negative depth. -/
theorem scaled_phase_factor {z : ℂ} (hz : z ∈ V.complexIntegers) (r : ℚ)
    (k : ℤ) (s : ℕ) (h : r ≠ 0 → (s : ℤ) - k ≤ padicValRat 2 r) :
    ∃ y ∈ V.complexIntegers, (2 : ℂ) ^ k * (z * (r : ℂ)) = (2 : ℂ) ^ s * y := by
  by_cases hr : r = 0
  · exact ⟨0, V.complexIntegers.zero_mem, by simp [hr]⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let y : ℚ := (2 : ℚ) ^ (k - (s : ℤ)) * r
  have htwo : padicValRat 2 (2 : ℚ) = 1 := by
    simpa only [Nat.cast_ofNat] using (padicValRat.self (p := 2) Nat.prime_two.one_lt)
  have hy : 0 ≤ padicValRat 2 y := by
    unfold y
    rw [padicValRat.mul (zpow_ne_zero _ (by norm_num)) hr, padicValRat.zpow, htwo, mul_one]
    have := h hr
    omega
  refine ⟨z * (y : ℂ), V.complexIntegers.mul_mem hz (V.rat_mem y hy), ?_⟩
  simp only [y, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat]
  rw [mul_left_comm ((2 : ℂ) ^ s), ← mul_assoc ((2 : ℂ) ^ s), ← zpow_natCast,
    ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
    show (s : ℤ) + (k - s) = k by omega]
  ring

end Place

/-- One prime for all the characters with a common two-power bound.
A phase defined by evaluating any of these characters is covered by the
same membership statement. -/
theorem common_place_for_characters {ι : Type*} (N e : ι → ℕ)
    (χ : ∀ i, DirichletCharacter ℂ (N i)) (bound : ℕ)
    (hχ : ∀ i, χ i ^ (2 ^ e i) = 1) (hle : ∀ i, e i ≤ bound) :
    ∃ V : Place (PhaseField bound), ∀ i x, χ i x ∈ V.complexIntegers := by
  obtain ⟨V⟩ := place_exists (PhaseField bound)
  exact ⟨V, fun i x => V.character_mem (χ i) (hχ i) (hle i) x⟩

end ZInQ.Manuscript.RC.EvenPlace
