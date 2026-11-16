import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Repo.A1Quaternion

/-! eichler-bound, part A: arithmetic of the maximal order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` of
`B = (2, −3 | ℚ)` used by the optimal-embedding count. -/

set_option linter.style.longLine false

noncomputable section

namespace EichlerBound

open LeafQM
open scoped QuaternionAlgebra

abbrev B := LeafQM.B

/-! ## A.1 Norm and trace -/

def nrd (x : B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

def trd (x : B) : ℚ := 2 * x.re

theorem star_mul_self' (a : B) : star a * a = ((nrd a : ℚ) : B) := by
  rw [QuaternionAlgebra.star_mul_eq_coe]; congr 1; simp [nrd]; ring

theorem mul_star_self' (a : B) : a * star a = ((nrd a : ℚ) : B) := by
  rw [QuaternionAlgebra.mul_star_eq_coe]; congr 1; simp [nrd]; ring

theorem nrd_mul (x y : B) : nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

theorem nrd_star (x : B) : nrd (star x) = nrd x := by
  simp [nrd]

theorem nrd_ne_zero {x : B} (hx : x ≠ 0) : nrd x ≠ 0 := by
  have h := GlueRepo.A1.nrd_ne_zero hx
  rw [GlueRepo.A1.nrd_eq] at h
  exact h

theorem nrd_eq_zero_iff {x : B} : nrd x = 0 ↔ x = 0 := by
  constructor
  · intro h; by_contra hx; exact nrd_ne_zero hx h
  · rintro rfl; simp [nrd]

theorem star_eq_trd_sub (x : B) : star x = ((trd x : ℚ) : B) - x := by
  ext <;> simp <;> (try simp only [trd]) <;> ring

theorem sq_eq_trd (x : B) : x * x = ((trd x : ℚ) : B) * x - ((nrd x : ℚ) : B) := by
  ext <;> simp <;> (try simp only [trd, nrd]) <;> ring

theorem nrd_coe (q : ℚ) : nrd (q : B) = q ^ 2 := by simp [nrd]

theorem trd_coe (q : ℚ) : trd (q : B) = 2 * q := by simp [trd]

theorem nrd_smul (q : ℚ) (x : B) : nrd (q • x) = q ^ 2 * nrd x := by
  simp [nrd]; ring

theorem coe_mul_eq_smul (q : ℚ) (x : B) : (q : B) * x = q • x := by
  ext <;> simp

theorem mul_coe_eq_smul (q : ℚ) (x : B) : x * (q : B) = q • x := by
  ext <;> simp [mul_comm]

theorem coe_comm (q : ℚ) (x : B) : (q : B) * x = x * (q : B) := by
  rw [coe_mul_eq_smul, mul_coe_eq_smul]

/-- A nonzero quaternion is invertible, with inverse `(nrd x)⁻¹ • star x`. -/
theorem mul_inv_eq (x : B) (hx : x ≠ 0) : x * ((nrd x)⁻¹ • star x) = 1 := by
  rw [mul_smul_comm, mul_star_self', ← coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul,
    inv_mul_cancel₀ (nrd_ne_zero hx), QuaternionAlgebra.coe_one]

theorem inv_mul_eq (x : B) (hx : x ≠ 0) : ((nrd x)⁻¹ • star x) * x = 1 := by
  rw [smul_mul_assoc, star_mul_self', ← coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul,
    inv_mul_cancel₀ (nrd_ne_zero hx), QuaternionAlgebra.coe_one]

/-! ## A.2 Integer coordinates on `𝒪` -/

/-- The integer norm form on the coordinates of `𝒪`. -/
def nrdZ (n : Fin 4 → ℤ) : ℤ := n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2)

def trdZ (n : Fin 4 → ℤ) : ℤ := 2 * n 0 + n 2

def conjZ (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem nrd_ofInt (n : Fin 4 → ℤ) : nrd (ofInt n) = (nrdZ n : ℚ) := by
  simp [nrd, nrdZ, ofInt]; ring

theorem trd_ofInt (n : Fin 4 → ℤ) : trd (ofInt n) = (trdZ n : ℚ) := by
  simp [trd, trdZ, ofInt]; ring

theorem star_ofInt (n : Fin 4 → ℤ) : star (ofInt n) = ofInt (conjZ n) := by
  ext <;> simp [ofInt, conjZ] <;> ring

theorem ofInt_injective : Function.Injective ofInt := by
  intro n m h
  have h0 := congrArg QuaternionAlgebra.re h
  have h1 := congrArg QuaternionAlgebra.imI h
  have h2 := congrArg QuaternionAlgebra.imJ h
  have h3 := congrArg QuaternionAlgebra.imK h
  simp only [ofInt] at h0 h1 h2 h3
  have e2 : n 2 = m 2 := by exact_mod_cast (by linarith : (n 2 : ℚ) = m 2)
  have e3 : n 3 = m 3 := by exact_mod_cast (by linarith : (n 3 : ℚ) = m 3)
  have e0 : n 0 = m 0 := by
    have : (n 0 : ℚ) = m 0 := by rw [e2] at h0; linarith
    exact_mod_cast this
  have e1 : n 1 = m 1 := by
    have : (n 1 : ℚ) = m 1 := by rw [e3] at h1; linarith
    exact_mod_cast this
  funext i; fin_cases i <;> assumption

theorem ofInt_smul (z : ℤ) (n : Fin 4 → ℤ) : ofInt (fun i => z * n i) = (z : ℚ) • ofInt n := by
  ext <;> simp [ofInt] <;> ring

theorem ofInt_sub (n m : Fin 4 → ℤ) : ofInt n - ofInt m = ofInt (n - m) := by
  ext <;> simp [ofInt] <;> ring

theorem mem_O {x : B} : x ∈ LeafQM.O ↔ ∃ n, x = ofInt n := Iff.rfl

theorem ofInt_mem (n : Fin 4 → ℤ) : ofInt n ∈ LeafQM.O := ⟨n, rfl⟩

theorem star_mem {x : B} (hx : x ∈ LeafQM.O) : star x ∈ LeafQM.O := by
  obtain ⟨n, rfl⟩ := hx; rw [star_ofInt]; exact ofInt_mem _

theorem nrd_int {x : B} (hx : x ∈ LeafQM.O) : ∃ z : ℤ, nrd x = z := by
  obtain ⟨n, rfl⟩ := hx; exact ⟨_, nrd_ofInt n⟩

theorem trd_int {x : B} (hx : x ∈ LeafQM.O) : ∃ z : ℤ, trd x = z := by
  obtain ⟨n, rfl⟩ := hx; exact ⟨_, trd_ofInt n⟩

theorem intCast_mem (z : ℤ) : ((z : ℚ) : B) ∈ LeafQM.O := by
  refine ⟨![z, 0, 0, 0], ?_⟩
  ext <;> simp [ofInt]

/-- `𝒪 ∩ ℚ = ℤ`. -/
theorem rat_mem_O {q : ℚ} (h : (q : B) ∈ LeafQM.O) : ∃ z : ℤ, q = z := by
  obtain ⟨n, hn⟩ := h
  have h0 := congrArg QuaternionAlgebra.re hn
  have h2 := congrArg QuaternionAlgebra.imJ hn
  simp [ofInt] at h0 h2
  have : (n 2 : ℚ) = 0 := by linarith
  refine ⟨n 0, ?_⟩
  rw [h0, this]; ring

/-! ## A.3 The ideal `ℓ𝒪` -/

/-- `x ∈ ℓ𝒪`. -/
def LO (ℓ : ℤ) (x : B) : Prop := ∃ n : Fin 4 → ℤ, x = ofInt (fun i => ℓ * n i)

theorem LO_ofInt_iff (ℓ : ℤ) (n : Fin 4 → ℤ) : LO ℓ (ofInt n) ↔ ∀ i, ℓ ∣ n i := by
  constructor
  · rintro ⟨m, hm⟩ i
    have := congrFun (ofInt_injective hm) i
    exact ⟨m i, this⟩
  · intro h
    choose m hm using h
    exact ⟨m, congrArg ofInt (funext hm)⟩

theorem LO_iff_smul (ℓ : ℤ) (hℓ : ℓ ≠ 0) (x : B) : LO ℓ x ↔ ∃ y ∈ LeafQM.O, x = (ℓ : ℚ) • y := by
  constructor
  · rintro ⟨n, rfl⟩; exact ⟨ofInt n, ofInt_mem n, ofInt_smul ℓ n⟩
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩; exact ⟨n, (ofInt_smul ℓ n).symm⟩

theorem LO_mem {ℓ : ℤ} {x : B} (h : LO ℓ x) : x ∈ LeafQM.O := by
  obtain ⟨n, rfl⟩ := h; exact ofInt_mem _

theorem LO_add {ℓ : ℤ} {x y : B} (hx : LO ℓ x) (hy : LO ℓ y) : LO ℓ (x + y) := by
  obtain ⟨n, rfl⟩ := hx; obtain ⟨m, rfl⟩ := hy
  refine ⟨n + m, ?_⟩
  rw [ofInt_add]; congr 1; funext i; simp [mul_add]

theorem LO_neg {ℓ : ℤ} {x : B} (hx : LO ℓ x) : LO ℓ (-x) := by
  obtain ⟨n, rfl⟩ := hx
  refine ⟨-n, ?_⟩
  rw [ofInt_neg]; congr 1; funext i; simp

theorem LO_sub {ℓ : ℤ} {x y : B} (hx : LO ℓ x) (hy : LO ℓ y) : LO ℓ (x - y) := by
  rw [sub_eq_add_neg]; exact LO_add hx (LO_neg hy)

theorem LO_zero (ℓ : ℤ) : LO ℓ 0 := ⟨0, by rw [← ofInt_zero]; congr 1; funext i; simp⟩

theorem LO_self (ℓ : ℤ) : LO ℓ ((ℓ : ℚ) : B) := by
  refine ⟨![1, 0, 0, 0], ?_⟩
  ext <;> simp [ofInt]

theorem LO_mul_left {ℓ : ℤ} (hℓ : ℓ ≠ 0) {x y : B} (hx : x ∈ LeafQM.O) (hy : LO ℓ y) : LO ℓ (x * y) := by
  rw [LO_iff_smul ℓ hℓ] at hy ⊢
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨x * z, LeafQM.O.mul_mem hx hz, by rw [mul_smul_comm]⟩

theorem LO_mul_right {ℓ : ℤ} (hℓ : ℓ ≠ 0) {x y : B} (hx : LO ℓ x) (hy : y ∈ LeafQM.O) : LO ℓ (x * y) := by
  rw [LO_iff_smul ℓ hℓ] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨z * y, LeafQM.O.mul_mem hz hy, by rw [smul_mul_assoc]⟩

theorem LO_star {ℓ : ℤ} (hℓ : ℓ ≠ 0) {x : B} (hx : LO ℓ x) : LO ℓ (star x) := by
  rw [LO_iff_smul ℓ hℓ] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨star y, star_mem hy, by rw [star_smul, star_trivial]⟩

theorem LO_intCast_mul {ℓ : ℤ} (z : ℤ) {x : B} (hx : x ∈ LeafQM.O) : LO (ℓ * z) (((ℓ * z : ℤ) : ℚ) • x) := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨n, (ofInt_smul _ n).symm⟩

theorem LO_of_smul {ℓ : ℤ} {x : B} (hx : x ∈ LeafQM.O) : LO ℓ ((ℓ : ℚ) • x) := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨n, (ofInt_smul _ n).symm⟩

/-- `x ∈ ℓ𝒪 ⟹ ℓ⁻¹ x ∈ 𝒪`. -/
theorem LO_div {ℓ : ℤ} (hℓ : ℓ ≠ 0) {x : B} (hx : LO ℓ x) : ((ℓ : ℚ)⁻¹ • x) ∈ LeafQM.O := by
  rw [LO_iff_smul ℓ hℓ] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hℓ), one_smul]

/-- A rational in `ℓ𝒪` is in `ℓℤ`. -/
theorem LO_rat {ℓ : ℤ} (hℓ : ℓ ≠ 0) {q : ℚ} (h : LO ℓ (q : B)) : ∃ z : ℤ, q = ℓ * z := by
  have := LO_div hℓ h
  rw [← coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul] at this
  obtain ⟨z, hz⟩ := rat_mem_O this
  refine ⟨z, ?_⟩
  have hℓ' : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ
  field_simp at hz
  linarith

/-! ## A.4 The two-sided primes `P₂ = i𝒪`, `P₃ = j𝒪` -/

/-- `x ∈ P_ℓ`: `x ∈ 𝒪` with `ℓ ∣ nrd x`. -/
def PP (ℓ : ℤ) (x : B) : Prop := ∃ n : Fin 4 → ℤ, x = ofInt n ∧ ℓ ∣ nrdZ n

theorem z2_aux : ∀ a b c d : ZMod 2,
    (a ^ 2 + a * c + c ^ 2 - 2 * (b ^ 2 + b * d + d ^ 2) = 0 ↔ a = 0 ∧ c = 0) := by decide

theorem z3_aux : ∀ a b c d : ZMod 3,
    (a ^ 2 + a * c + c ^ 2 - 2 * (b ^ 2 + b * d + d ^ 2) = 0 ↔ a - c = 0 ∧ b - d = 0) := by decide

theorem dvd2_nrdZ (n : Fin 4 → ℤ) : (2 : ℤ) ∣ nrdZ n ↔ (2 : ℤ) ∣ n 0 ∧ (2 : ℤ) ∣ n 2 := by
  have key : ∀ x : ℤ, (2 : ℤ) ∣ x ↔ ((x : ZMod 2) = 0) := fun x =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).symm
  simp only [key, nrdZ]
  push_cast
  exact z2_aux _ _ _ _

theorem dvd3_nrdZ (n : Fin 4 → ℤ) : (3 : ℤ) ∣ nrdZ n ↔ (3 : ℤ) ∣ n 0 - n 2 ∧ (3 : ℤ) ∣ n 1 - n 3 := by
  have key : ∀ x : ℤ, (3 : ℤ) ∣ x ↔ ((x : ZMod 3) = 0) := fun x =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).symm
  simp only [key, nrdZ]
  push_cast
  exact z3_aux _ _ _ _

theorem PP_mem {ℓ : ℤ} {x : B} (h : PP ℓ x) : x ∈ LeafQM.O := by
  obtain ⟨n, rfl, -⟩ := h; exact ofInt_mem n

theorem PP_iff {ℓ : ℤ} {x : B} (hx : x ∈ LeafQM.O) : PP ℓ x ↔ ∃ z : ℤ, nrd x = z ∧ ℓ ∣ z := by
  obtain ⟨n, rfl⟩ := hx
  constructor
  · rintro ⟨m, hm, hd⟩
    rw [← ofInt_injective hm] at hd
    exact ⟨_, nrd_ofInt n, hd⟩
  · rintro ⟨z, hz, hd⟩
    refine ⟨n, rfl, ?_⟩
    rw [nrd_ofInt] at hz
    have : nrdZ n = z := by exact_mod_cast hz
    rwa [this]

/-- `P_ℓ` is prime: `xy ∈ P_ℓ ⟹ x ∈ P_ℓ ∨ y ∈ P_ℓ`. -/
theorem PP_prime {ℓ : ℤ} (hℓ : Prime ℓ) {x y : B} (hx : x ∈ LeafQM.O) (hy : y ∈ LeafQM.O)
    (h : PP ℓ (x * y)) : PP ℓ x ∨ PP ℓ y := by
  obtain ⟨a, ha⟩ := nrd_int hx
  obtain ⟨b, hb⟩ := nrd_int hy
  rw [PP_iff (LeafQM.O.mul_mem hx hy)] at h
  obtain ⟨z, hz, hd⟩ := h
  rw [nrd_mul, ha, hb] at hz
  have : z = a * b := by exact_mod_cast hz.symm
  rw [this] at hd
  rcases hℓ.dvd_or_dvd hd with h1 | h1
  · left; rw [PP_iff hx]; exact ⟨a, ha, h1⟩
  · right; rw [PP_iff hy]; exact ⟨b, hb, h1⟩

theorem PP_star {ℓ : ℤ} {x : B} (h : PP ℓ x) : PP ℓ (star x) := by
  have hx := PP_mem h
  rw [PP_iff hx] at h; rw [PP_iff (star_mem hx), nrd_star]; exact h

theorem PP_of_LO {ℓ : ℤ} {x : B} (h : LO ℓ x) : PP ℓ x := by
  obtain ⟨n, rfl⟩ := h
  refine ⟨_, rfl, ?_⟩
  simp only [nrdZ]
  exact ⟨n 0 ^ 2 * ℓ + n 0 * n 2 * ℓ + n 2 ^ 2 * ℓ - 2 * (n 1 ^ 2 * ℓ + n 1 * n 3 * ℓ + n 3 ^ 2 * ℓ), by ring⟩

theorem PP_mul_left {ℓ : ℤ} {x y : B} (hx : x ∈ LeafQM.O) (hy : PP ℓ y) : PP ℓ (x * y) := by
  have hy' := PP_mem hy
  rw [PP_iff hy'] at hy
  obtain ⟨z, hz, hd⟩ := hy
  obtain ⟨a, ha⟩ := nrd_int hx
  rw [PP_iff (LeafQM.O.mul_mem hx hy')]
  exact ⟨a * z, by rw [nrd_mul, ha, hz]; push_cast; ring, dvd_mul_of_dvd_right hd a⟩

theorem PP_mul_right {ℓ : ℤ} {x y : B} (hx : PP ℓ x) (hy : y ∈ LeafQM.O) : PP ℓ (x * y) := by
  have hx' := PP_mem hx
  rw [PP_iff hx'] at hx
  obtain ⟨z, hz, hd⟩ := hx
  obtain ⟨a, ha⟩ := nrd_int hy
  rw [PP_iff (LeafQM.O.mul_mem hx' hy)]
  exact ⟨z * a, by rw [nrd_mul, ha, hz]; push_cast; ring, dvd_mul_of_dvd_left hd a⟩

/-- `ℓ ∈ {2, 3}`. -/
def L6 (ℓ : ℤ) : Prop := ℓ = 2 ∨ ℓ = 3

theorem PP_coord {ℓ : ℤ} (hℓ : L6 ℓ) (n : Fin 4 → ℤ) :
    PP ℓ (ofInt n) ↔ (ℓ = 2 ∧ (2 : ℤ) ∣ n 0 ∧ (2 : ℤ) ∣ n 2) ∨
      (ℓ = 3 ∧ (3 : ℤ) ∣ n 0 - n 2 ∧ (3 : ℤ) ∣ n 1 - n 3) := by
  constructor
  · rintro ⟨m, hm, hd⟩
    rw [← ofInt_injective hm] at hd
    rcases hℓ with rfl | rfl
    · left; exact ⟨rfl, (dvd2_nrdZ n).1 hd⟩
    · right; exact ⟨rfl, (dvd3_nrdZ n).1 hd⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨n, rfl, (dvd2_nrdZ n).2 h⟩
    · exact ⟨n, rfl, (dvd3_nrdZ n).2 h⟩

theorem PP_add {ℓ : ℤ} (hℓ : L6 ℓ) {x y : B} (hx : PP ℓ x) (hy : PP ℓ y) : PP ℓ (x + y) := by
  obtain ⟨n, rfl, hn⟩ := hx; obtain ⟨m, rfl, hm⟩ := hy
  have hn' := (PP_coord hℓ n).1 ⟨n, rfl, hn⟩
  have hm' := (PP_coord hℓ m).1 ⟨m, rfl, hm⟩
  rw [ofInt_add, PP_coord hℓ]
  simp only [Pi.add_apply]
  omega

theorem PP_neg {ℓ : ℤ} (hℓ : L6 ℓ) {x : B} (hx : PP ℓ x) : PP ℓ (-x) := by
  obtain ⟨n, rfl, hn⟩ := hx
  have hn' := (PP_coord hℓ n).1 ⟨n, rfl, hn⟩
  rw [ofInt_neg, PP_coord hℓ]
  simp only [Pi.neg_apply]
  omega

theorem PP_sub {ℓ : ℤ} (hℓ : L6 ℓ) {x y : B} (hx : PP ℓ x) (hy : PP ℓ y) : PP ℓ (x - y) := by
  rw [sub_eq_add_neg]; exact PP_add hℓ hx (PP_neg hℓ hy)

/-- Commutators lie in `P_ℓ` (`𝒪/P_ℓ` is commutative). -/
theorem PP_comm {ℓ : ℤ} (hℓ : L6 ℓ) {x y : B} (hx : x ∈ LeafQM.O) (hy : y ∈ LeafQM.O) :
    PP ℓ (x * y - y * x) := by
  obtain ⟨n, rfl⟩ := hx; obtain ⟨m, rfl⟩ := hy
  rw [ofInt_mul, ofInt_mul, ofInt_sub, PP_coord hℓ]
  simp only [mulCoord, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rcases hℓ with rfl | rfl
  · left; refine ⟨rfl, ⟨n 3 * m 1 - n 1 * m 3, by ring⟩, ⟨2 * (n 1 * m 3 - n 3 * m 1), by ring⟩⟩
  · right; refine ⟨rfl, ⟨2 * (n 3 * m 1 - n 1 * m 3), by ring⟩, ⟨n 2 * m 1 - n 1 * m 2 + n 2 * m 3 - n 3 * m 2, by ring⟩⟩

/-- The uniformizers `π₂ = i`, `π₃ = j`. -/
def piL (ℓ : ℤ) : B := if ℓ = 2 then ofInt ![0, 1, 0, 0] else ofInt ![-1, 0, 2, 0]

theorem piL_two : piL 2 = ofInt ![0, 1, 0, 0] := if_pos rfl

theorem piL_three : piL 3 = ofInt ![-1, 0, 2, 0] := if_neg (by norm_num)

theorem piL_mem (ℓ : ℤ) : piL ℓ ∈ LeafQM.O := by
  unfold piL; split_ifs <;> exact ofInt_mem _

/-- `nrd π_ℓ = ε ℓ` with `ε = ±1`: `nrd i = −2`, `nrd j = 3`. -/
def epsL (ℓ : ℤ) : ℤ := if ℓ = 2 then -1 else 1

theorem nrd_piL {ℓ : ℤ} (hℓ : L6 ℓ) : nrd (piL ℓ) = ((epsL ℓ * ℓ : ℤ) : ℚ) := by
  rcases hℓ with rfl | rfl <;> simp [piL, epsL, nrd_ofInt, nrdZ]

theorem epsL_sq {ℓ : ℤ} : epsL ℓ * epsL ℓ = 1 := by unfold epsL; split_ifs <;> norm_num

/-- `π_ℓ² = ±ℓ`: `i² = 2`, `j² = −3`. -/
theorem piL_sq {ℓ : ℤ} (hℓ : L6 ℓ) : piL ℓ * piL ℓ = (((-epsL ℓ) * ℓ : ℤ) : ℚ) := by
  rcases hℓ with rfl | rfl <;> ext <;> simp [piL, epsL, ofInt] <;> norm_num

theorem piL_ne_zero {ℓ : ℤ} (hℓ : L6 ℓ) : piL ℓ ≠ 0 := by
  intro h
  have := nrd_piL hℓ
  rw [h] at this
  rcases hℓ with rfl | rfl <;> simp [nrd, epsL] at this

/-- `P_ℓ = π_ℓ 𝒪`: every `x ∈ P_ℓ` is `π_ℓ y` with `y ∈ 𝒪`. -/
theorem PP_eq_pi_mul {ℓ : ℤ} (hℓ : L6 ℓ) {x : B} (hx : PP ℓ x) :
    ∃ y ∈ LeafQM.O, x = piL ℓ * y := by
  obtain ⟨n, rfl, hn⟩ := hx
  have hn' := (PP_coord hℓ n).1 ⟨n, rfl, hn⟩
  rcases hℓ with rfl | rfl
  · obtain ⟨-, ⟨a, ha⟩, ⟨c, hc⟩⟩ := hn'.resolve_right (by omega)
    refine ⟨ofInt ![n 1, a, n 3, c], ofInt_mem _, ?_⟩
    rw [piL_two, ofInt_mul]; congr 1; funext i; fin_cases i <;> simp [mulCoord] <;> linarith
  · obtain ⟨-, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hn'.resolve_left (by omega)
    refine ⟨ofInt ![n 2 + a, -(n 3 + b), -(n 2 + 2 * a), n 3 + 2 * b], ofInt_mem _, ?_⟩
    rw [piL_three, ofInt_mul]; congr 1; funext i; fin_cases i <;> simp [mulCoord] <;> linarith

end EichlerBound
