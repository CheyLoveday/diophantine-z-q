import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.Inputs

/-!
# EvenUpper, part 3: the inputs without distinct parameters

Manuscript `diophantine_zq.tex`, tex 2311–2341.  The cubes of the address construction need not
have distinct parameters at distinct addresses (the activations of the new vertices need not span
the dual of `𝔽₂^b`).  `evenUpperInputsAt_of'` (`PROVED`) removes the hypothesis
`Function.Injective fam.h` of `evenUpperInputsAt_of`: the representative address of a parameter is
chosen *after* the Boolean comparison, as the zero address for `d` and as the address `x` found
there for `h_x`.  `evenUpper33b_of_RC11'` is the corresponding assembly.
-/

namespace ZInQ.Contrib.CloudB3RC53.EvenUpper

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The single-precision inputs from (3.3a), RC11's (3.2), the realized cubes (any parameters)
and the Boolean comparison** (tex 2302–2341), `PROVED`. -/
theorem evenUpperInputsAt_of' (unitSym : ℤ → Prop) (C₀ : ℤ)
    (h33a : ∀ p, unitSym p → p ≠ 0 ∧ W.Lstar p ≠ 0 ∧ padicValRat 2 (W.Lstar p) ≤ 2 * omega p + C₀)
    {N₀ : ℕ} (L : Even.CentralNormalization (Ecurve ℓ)) (hLW : L.Lstar = W.Lstar)
    (h32 : Even.EvenScalar32 (Ecurve ℓ) N₀ L)
    (hcubes : ∀ d : ℤ, d ≠ 0 → W.Partitionable d → Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      ∀ b : ℕ, ∃ fam : Even.BinaryFamily N₀, b ≤ fam.b ∧ fam.h 0 = d ∧
        ∀ x, x ≠ 0 → unitSym (fam.h x)) :
    EvenUpperInputsAt W := by
  classical
  obtain ⟨Cev, C, h32⟩ := h32
  refine ⟨C₀, C, fun d hd0 hpart hcz => ?_⟩
  set M : ℕ := (C₀ + C + 1).toNat + Cev with hM
  obtain ⟨fam, hb, hh0, hunit⟩ := hcubes d hd0 hpart hcz (2 ^ (M - 1))
  obtain ⟨uf, hint, hzero, hbd⟩ := h32 fam
  obtain ⟨x, hx0, hcong⟩ := boolean_comparison uf Cev hint M (by
    have : 2 ^ (M - 1) - 1 < 2 ^ (M - 1) := Nat.sub_lt (Nat.two_pow_pos _) one_pos
    omega)
  -- representative addresses, chosen after the comparison
  let rep : ℤ → (Fin fam.b → ZMod 2) := fun p =>
    if p = fam.h 0 then 0 else if p = fam.h x then x else
      if hp : ∃ y, fam.h y = p then hp.choose else 0
  have hrep : ∀ y, fam.h (rep (fam.h y)) = fam.h y := by
    intro y
    simp only [rep]
    split_ifs with h1 h2 h3
    · exact h1.symm
    · exact h2.symm
    · exact h3.choose_spec
    · exact absurd ⟨y, rfl⟩ h3
  let art : ℤ → ℚ_[2] := fun p => if W.Lstar p = 0 then 0 else
    (2 : ℚ_[2]) ^ (padicValRat 2 (W.Lstar p) - 2 * (omega p : ℤ) - (shaLength (Etw ℓ p) : ℤ))
  let u : ℤ → ℚ_[2] := fun p =>
    if ∃ y, fam.h y = p then Even.central (Even.charEval uf (rep p)) else art p
  have hu_fam : ∀ y, u (fam.h y) = Even.central (Even.charEval uf (rep (fam.h y))) := by
    intro y; simp only [u, if_pos (⟨y, rfl⟩ : ∃ z, fam.h z = fam.h y)]
  refine ⟨unitSym, u, h33a, fun p hp0 hcp => ?_, ?_⟩
  · by_cases hp : ∃ y, fam.h y = p
    · obtain ⟨y, rfl⟩ := hp
      rw [hu_fam]
      set z := rep (fam.h y)
      have hz : fam.h z = fam.h y := hrep y
      have hcz' : Even.CorankZero (Ecurve ℓ) (fam.h z) := by rw [hz]; exact hcp
      refine ⟨by rw [hzero z hcz', hLW, hz], fun hL => ?_⟩
      have := hbd z hcz' (by rw [hLW, hz]; exact hL)
      rw [hLW, even_omega_eq, hz] at this
      exact_mod_cast this
    · have hart : u p = art p := by simp only [u, if_neg hp]
      rw [hart]
      by_cases hL : W.Lstar p = 0
      · simp [art, hL]
      · simp only [art, if_neg hL]
        refine ⟨⟨fun h0 => absurd h0 (zpow_ne_zero _ two_ne_zero), fun h0 => absurd h0 hL⟩,
          fun _ => ?_⟩
        rw [Padic.valuation_zpow]
        have h2 : (2 : ℚ_[2]).valuation = 1 := by simp
        rw [h2, mul_one, sub_self, abs_zero]
        exact_mod_cast Nat.zero_le C
  · refine ⟨fam.h x, hunit x hx0, ?_⟩
    have hd : u d = Even.central (Even.charEval uf 0) := by
      rw [← hh0, hu_fam]; simp [rep]
    by_cases hx : fam.h x = fam.h 0
    · left; rw [hx, hh0]
    · have hux : u (fam.h x) = Even.central (Even.charEval uf x) := by
        rw [hu_fam]; simp [rep, hx]
      rw [hux, hd]
      rcases hcong with heq | hge
      · exact Or.inl heq
      · right
        have : (C₀ + C + 1 : ℤ) ≤ (M : ℤ) - Cev := by
          rw [hM]; push_cast; have := Int.self_le_toNat (C₀ + C + 1); omega
        exact le_trans (by exact_mod_cast this) hge

/-- **(3.3b) assembled, cubes with any parameters** (tex 2273–2341), `PROVED`. -/
theorem evenUpper33b_of_RC11' (P : Prints) (hKum : KummerCorankZero) (hℓ : 0 < ℓ)
    (hL : LstarTarget W.toRCData) (hN : LstarNormalized W.toRCData) {N₀ : ℕ}
    (h32 : ∀ L : Even.CentralNormalization (Ecurve ℓ), L.Lstar = W.Lstar →
      Even.EvenScalar32 (Ecurve ℓ) N₀ L)
    (aNZ : ℤ → Prop) (va : ℤ → ℤ) (κ c : ℤ)
    (hE11 : ∀ D, (W.Lstar D ≠ 0 ↔ aNZ D) ∧ (aNZ D → padicValRat 2 (W.Lstar D) = 2 * va D + κ))
    (hE9 : ∀ D, aNZ D → c ≤ va D - omega D) (href : ∃ D, aNZ D) (hNZ : ∀ D, aNZ D → D ≠ 0)
    (hcubes : ∀ d : ℤ, d ≠ 0 → W.Partitionable d →
      Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
      ∀ b : ℕ, ∃ fam : Even.BinaryFamily N₀, b ≤ fam.b ∧ fam.h 0 = d ∧
        ∀ x, x ≠ 0 → UnitMin aNZ va (fam.h x)) :
    ∃ C₁ : ℤ, EvenUpper33b W C₁ := by
  obtain ⟨L, hLW⟩ := hN
  obtain ⟨C₀, h33a⟩ := h33a_of_F1 W aNZ va κ c hE11 hE9 href hNZ
  exact evenUpper33b_of_inputsAt W P hKum hℓ hL
    (evenUpperInputsAt_of' W _ _ h33a L hLW (h32 L hLW) hcubes)

end ZInQ.Contrib.CloudB3RC53.EvenUpper
