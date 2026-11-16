import ZInQKernel.Contrib.OneProof.CdOptimal.Unif
import ZInQKernel.Contrib.OneProof.GrossZagierOptimal

/-!
# cd-optimal: the period lattice of `f_d` is a `ℤ[i]`-module stable under complex conjugation

Task cd-optimal (2026-11-16). Report: `docs/research/cd-optimal.md`; log: `scratch/cd-optimal/log.md`.

`Λ_d` (`LamCd d`) is the subgroup of `ℂ` spanned by the periods `Φ_d(γτ) − Φ_d(τ)`, `γ ∈ Γ₀(32d²)`, of
gz-weil's Eichler integral `Φ_d = Σ heckeCoeff d n / n · qⁿ` (for a newform `f` of `C_d` it is
gz-optimal's `periodLattice f`: `periodLattice_eq_LamCd`).

* `Φ_d(τ + 1/4) = i Φ_d(τ)` (`aₙ = 0` unless `n ≡ 1 mod 4`), and `γ ↦ T^{1/4} γ T^{-1/4}` preserves
  `Γ₀(32d²)`: `i Λ_d ⊆ Λ_d` (`I_mul_mem_LamCd`).
* `aₙ ∈ ℤ`, so `conj Φ_d(τ) = Φ_d(−τ̄)`, and `γ ↦ diag(1,−1) γ diag(1,−1)` preserves `Γ₀(32d²)`:
  `conj Λ_d ⊆ Λ_d` (`conj_mem_LamCd`).
* every period lattice `L` of `C_d` is `i`-stable and conjugation-stable (uniqueness of the lattice,
  `Unif.lean`).
* a lattice stable under `i` is `ℤ[i] ω` for a shortest `ω` (Gaussian rounding); stability under
  conjugation forces the ratio of two such generators into `ℤ · {1, i, 1 ± i}`.

Hence (`lattice_eq_of_periods`): if `Λ_d ⊆ L` and some period is not in `(1 + i) L`, then `L = c₀ Λ_d`
with `c₀ ∈ ℚ`. No `sorry`, no `axiom`.
-/

noncomputable section

open Complex CongruenceSubgroup Filter Topology
open scoped UpperHalfPlane
open ZInQ.Contrib.HeckeFE (heckeCoeff unitOf normFiber mem_normFiber gz)
open ZInQ.GZWeil (eichlerCd)
open Matrix.GeneralLinearGroup (upperRightHom)
open Matrix.SpecialLinearGroup (mapGL)
open scoped MatrixGroups ComplexConjugate

namespace ZInQ.CdOpt

/-! ## §1. `aₙ(C_d) = 0` unless `n ≡ 1 (mod 4)` -/

theorem unitOf_eq_zero {t : ZMod 4 × ZMod 4} (h : t.1 ^ 2 + t.2 ^ 2 ≠ 1) : unitOf t = 0 := by
  obtain ⟨a, b⟩ := t
  fin_cases a <;> fin_cases b <;> first | (simp (config := {decide := true}) [unitOf]; done) |
    exact absurd h (by decide)

theorem heckeCoeff_eq_zero (d : ℕ) {n : ℕ} (hn : n % 4 ≠ 1) : heckeCoeff d n = 0 := by
  unfold heckeCoeff
  rw [Finset.sum_eq_zero, mul_zero]
  intro p hp
  have hp' := mem_normFiber.mp hp
  rw [unitOf_eq_zero, mul_zero, zero_mul]
  intro h
  apply hn
  have h1 : (((p.1 ^ 2 + p.2 ^ 2 : ℤ)) : ZMod 4) = 1 := by push_cast; exact h
  rw [hp'] at h1
  have h2 : ((n : ℕ) : ZMod 4) = 1 := by exact_mod_cast h1
  have := ZMod.val_natCast (n := 4) n
  rw [h2] at this
  rw [← this]; rfl

/-! ## §2. `Φ_d(z + 1/4) = i Φ_d(z)` and `conj Φ_d(z) = Φ_d(−z̄)` -/

theorem eichlerCd_add_quarter (d : ℕ) (z : ℂ) : eichlerCd d (z + 1 / 4) = I * eichlerCd d z := by
  unfold eichlerCd
  rw [← tsum_mul_left]
  congr 1
  funext n
  by_cases h : (n + 1) % 4 = 1
  · obtain ⟨k, hk⟩ : ∃ k, n = 4 * k := ⟨n / 4, by omega⟩
    have he : cexp (2 * Real.pi * I * ((n : ℂ) + 1) * (z + 1 / 4)) =
        I * cexp (2 * Real.pi * I * ((n : ℂ) + 1) * z) := by
      have : 2 * Real.pi * I * ((n : ℂ) + 1) * (z + 1 / 4) =
          2 * Real.pi * I * ((n : ℂ) + 1) * z + ((k : ℕ) * (2 * Real.pi * I) + Real.pi / 2 * I) := by
        rw [hk]; push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I,
        Complex.exp_pi_div_two_mul_I]
      ring
    rw [he]; ring
  · rw [heckeCoeff_eq_zero d h]; simp

theorem heckeCoeff_conj {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {n : ℕ} (hn : n ≠ 0) :
    conj (heckeCoeff d n) = heckeCoeff d n := by
  rw [← ZInQ.GZStatements.LFunction_cd_eq_heckeCoeff hd4 hsq hn]
  exact map_intCast _ _

theorem conj_eichlerCd {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) (z : ℂ) :
    conj (eichlerCd d z) = eichlerCd d (-conj z) := by
  unfold eichlerCd
  rw [Complex.conj_tsum]
  congr 1
  funext n
  rw [map_mul, map_div₀, heckeCoeff_conj hd4 hsq (Nat.succ_ne_zero n), ← Complex.exp_conj]
  congr 2
  · simp
  · simp only [map_mul, map_add, map_natCast, map_one, Complex.conj_ofReal, Complex.conj_I,
      map_ofNat]
    ring

/-! ## §3. The period lattice `Λ_d` -/

/-- **`Λ_d`**: the subgroup of `ℂ` spanned by the periods `Φ_d(γτ) − Φ_d(τ)`, `γ ∈ Γ₀(32 d²)`,
`τ ∈ ℍ`. -/
def LamCd (d : ℕ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {w | ∃ γ ∈ Gamma0 (32 * d ^ 2), ∃ τ : ℍ,
    w = eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ)}

/-- For a newform `f` of `C_d`, gz-optimal's `periodLattice f` is `Λ_d` (level `32 d²`, Eichler
integral `Φ_d`). -/
theorem periodLattice_eq_LamCd {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {N : ℕ} [NeZero N]
    (f : HeckeRing.GL2.Newform N 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) :
    ZInQ.GZOptimal.periodLattice f = LamCd d := by
  have hN := ZInQ.GZStatements.level_eq_of_coeff_cd hd4 hsq f hχ hf
  subst hN
  unfold ZInQ.GZOptimal.periodLattice LamCd
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, ZInQ.GZWeil.eichler_eq_eichlerCd hd4 hsq f hf]

theorem gamma0_data {d : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (32 * d ^ 2)) :
    ∃ k : ℤ, γ 1 0 = 32 * d ^ 2 * k ∧ γ 1 1 % 2 = 1 := by
  rw [Gamma0_mem] at hγ
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) (32 * d ^ 2)).1 hγ
  refine ⟨k, by exact_mod_cast hk, ?_⟩
  have hdet0 : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  rw [hk] at hdet0
  have hodd : Odd (γ 0 0 * γ 1 1) :=
    ⟨16 * (γ 0 1 * d ^ 2 * k), by push_cast at hdet0; linear_combination hdet0⟩
  exact Int.odd_iff.1 (Int.odd_mul.1 hodd).2

theorem sq_odd_zmod4 {e : ℤ} (he : e % 2 = 1) : ((e : ZMod 4)) ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, e = 2 * m + 1 := ⟨e / 2, by omega⟩
  have : ((2 * m + 1 : ℤ) : ZMod 4) ^ 2 = (((4 * (m ^ 2 + m) + 1 : ℤ)) : ZMod 4) := by
    push_cast; ring
  rw [this]
  push_cast
  rw [show (4 : ZMod 4) = 0 from rfl]
  ring

/-- **`i Λ_d ⊆ Λ_d`.** -/
theorem I_mul_mem_LamCd (d : ℕ) {w : ℂ} (hw : w ∈ LamCd d) : I * w ∈ LamCd d := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, τ, rfl⟩ := hx
    obtain ⟨k, hk, hodd⟩ := gamma0_data hγ
    obtain ⟨γ', -, hγ'1, -, hγ'eq⟩ :=
      TauCeti.exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom (M := 4) γ
        (c := 2 * d ^ 2 * k) (a := 1) (a' := 1) (by rw [hk]; push_cast; ring)
        (by push_cast; rw [sq_odd_zmod4 hodd]; ring)
    set τ' : ℍ := (((1 : ℤ) : ℝ) / (4 : ℕ)) +ᵥ τ with hτ'
    have hmove : ((γ • τ : ℍ) : ℂ) + 1 / 4 = ((γ' • τ' : ℍ) : ℂ) := by
      have h := congrArg (fun g : GL (Fin 2) ℝ => g • τ) hγ'eq
      simp only [mul_smul, TauCeti.Matrix.GeneralLinearGroup.upperRightHom_smul] at h
      have h' := congrArg (fun z : ℍ => (z : ℂ)) h
      simp only [UpperHalfPlane.coe_vadd] at h'
      rw [ModularGroup.sl_moeb, ModularGroup.sl_moeb, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
        TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← h']
      push_cast
      ring
    have hτc : ((τ' : ℍ) : ℂ) = (τ : ℂ) + 1 / 4 := by
      rw [hτ', UpperHalfPlane.coe_vadd]; push_cast; ring
    refine Submodule.subset_span ⟨γ', ?_, τ', ?_⟩
    · rw [Gamma0_mem, hγ'1]; exact (Gamma0_mem.mp hγ)
    · rw [← hmove, hτc, eichlerCd_add_quarter, eichlerCd_add_quarter]; ring
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul n x _ hx =>
    rw [show I * (n • x) = n • (I * x) by rw [zsmul_eq_mul, zsmul_eq_mul]; ring]
    exact Submodule.smul_mem _ n hx

/-- `diag(1, −1) γ diag(1, −1)`. -/
def flipSL (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this
    rw [Matrix.det_fin_two_of]; linear_combination this⟩

/-- `−τ̄`. -/
def negConj (τ : ℍ) : ℍ := ⟨-conj (τ : ℂ), by simpa using τ.im_pos⟩

theorem negConj_coe (τ : ℍ) : ((negConj τ : ℍ) : ℂ) = -conj (τ : ℂ) := rfl

theorem flip_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((flipSL γ • negConj τ : ℍ) : ℂ) = -conj ((γ • τ : ℍ) : ℂ) := by
  rw [ZInQ.GZWeil.coe_smul_eq_moeb, ZInQ.GZWeil.coe_smul_eq_moeb]
  simp only [ZInQ.GZWeil.moeb, flipSL, negConj, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, map_div₀, map_add, map_mul, map_intCast, Int.cast_neg]
  ring

/-- **`conj Λ_d ⊆ Λ_d`.** -/
theorem conj_mem_LamCd {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {w : ℂ}
    (hw : w ∈ LamCd d) : conj w ∈ LamCd d := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, τ, rfl⟩ := hx
    refine Submodule.subset_span ⟨flipSL γ, ?_, negConj τ, ?_⟩
    · rw [Gamma0_mem] at hγ ⊢
      simp only [flipSL, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
        Int.cast_neg, hγ, neg_zero]
    · rw [map_sub, conj_eichlerCd hd4 hsq, conj_eichlerCd hd4 hsq, flip_smul]
      rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul n x _ hx =>
    rw [show conj (n • x) = n • conj x by rw [zsmul_eq_mul, zsmul_eq_mul, map_mul, map_intCast]]
    exact Submodule.smul_mem _ n hx

end ZInQ.CdOpt
