import Mathlib

/-!
# Duality area: the tame split local model (4.4)

Manuscript `diophantine_zq.tex`, Section 8, subsection "Actual support comparisons",
tex L3470–3479, display (4.4). At a tame split prime `q` the local free model of the coefficient
representation is the three-term complex
```
M --d⁰--> M ⊕ M --d¹--> M,    d⁰ v = (A v, C v),   d¹ (v, w) = -C v + D w,
A = Φ - 1,   C = g - 1,   D = Φ - N_q(g),   N_q(g) = (q + 1)/2 + (q - 1)/2 · g,   DC = CA,
```
and at augmentation `g = 1` it is the direct sum of the unramified complex `[Φ - 1]` (degrees
zero and one) and the singular quotient `[Φ - q]` (degrees one and two).

Here `R` is the coefficient ring (`A_i` or `A_i[G]`), `M` the free coefficient module, `Φ` the
(`R`-linear) Frobenius and `g ∈ R` the image of the tame inertia generator; in the binary
family `g` lies in the elementary abelian two-group `G`, so `g² = 1`, and `q` is odd. Then
`N_q(g) = 1 + g + ⋯ + g^{q-1}` is the Fox derivative of the tame relation `Φ σ Φ⁻¹ = σ^q`
in the inertia variable (`geom_sum_eq_tameNorm`).

**Classification.** `TameModelNode` is PROVED (`tameModelNode_proof`).

**ELLIOT** (tex L3470–3472): the manuscript displays the model without saying why it computes
the local cochains `RΓ(K_v, M)` (tame cohomology of `⟨Φ, σ | Φ σ Φ⁻¹ = σ^q⟩`). This file proves
the algebraic content of (4.4) only: the formula for `N_q(g)`, the commutation `DC = CA`, that
`d¹ ∘ d⁰ = 0`, and the splitting at augmentation.
-/

namespace ZInQ.Contrib.CloudB3RC53.Duality

open Finset

section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- `N_q(g) = (q + 1)/2 + (q - 1)/2 · g` (tex L3476). -/
def tameNorm (q : ℕ) (g : R) : R := (((q + 1) / 2 : ℕ) : R) + (((q - 1) / 2 : ℕ) : R) * g

/-- For odd `q` and `g² = 1`, `N_q(g) = 1 + g + ⋯ + g^{q-1}` (the inertia Fox derivative of the
tame relation). -/
theorem geom_sum_eq_tameNorm {q : ℕ} (hq : Odd q) {g : R} (hg : g ^ 2 = 1) :
    ∑ k ∈ range q, g ^ k = tameNorm q g := by
  obtain ⟨m, rfl⟩ := hq
  unfold tameNorm
  have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  have h2 : (2 * m + 1 - 1) / 2 = m := by omega
  rw [h1, h2]
  clear h1 h2
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    have e1 : g ^ (2 * m + 1) = g := by rw [pow_succ, pow_mul, hg, one_pow, one_mul]
    have e2 : g ^ (2 * m + 1 + 1) = 1 := by rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul, hg, one_pow]
    rw [e1, e2]; push_cast; ring

/-- `A = Φ - 1`. -/
def tameA (Φ : M →ₗ[R] M) : M →ₗ[R] M := Φ - LinearMap.id

/-- `C = g - 1`. -/
def tameC (g : R) : M →ₗ[R] M := (g - 1) • LinearMap.id

/-- `D = Φ - N_q(g)`. -/
def tameD (q : ℕ) (Φ : M →ₗ[R] M) (g : R) : M →ₗ[R] M := Φ - tameNorm q g • LinearMap.id

/-- `d⁰ v = (A v, C v)`. -/
def tameD0 (Φ : M →ₗ[R] M) (g : R) : M →ₗ[R] M × M := (tameA Φ).prod (tameC g)

/-- `d¹ (v, w) = -C v + D w`. -/
def tameD1 (q : ℕ) (Φ : M →ₗ[R] M) (g : R) : M × M →ₗ[R] M :=
  -(tameC g ∘ₗ LinearMap.fst R M M) + tameD q Φ g ∘ₗ LinearMap.snd R M M

/-- `(N_q(g) - 1)(g - 1) = (q - 1)/2 · (g² - 1)` for odd `q`. -/
theorem tameNorm_sub_one_mul {q : ℕ} (hq : Odd q) (g : R) :
    (tameNorm q g - 1) * (g - 1) = (((q - 1) / 2 : ℕ) : R) * (g ^ 2 - 1) := by
  obtain ⟨m, rfl⟩ := hq
  unfold tameNorm
  have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  have h2 : (2 * m + 1 - 1) / 2 = m := by omega
  rw [h1, h2]
  push_cast
  ring

/-- **`DC - CA = -((q - 1)/2)(g² - 1)`** for odd `q` (with `N_q(g)` the displayed formula, for
an arbitrary tame image `g ∈ R`). -/
theorem tameD_comp_tameC_sub {q : ℕ} (hq : Odd q) (Φ : M →ₗ[R] M) (g : R) :
    tameD q Φ g ∘ₗ tameC g - tameC g ∘ₗ tameA Φ =
      -((((q - 1) / 2 : ℕ) : R) * (g ^ 2 - 1)) • LinearMap.id := by
  ext v
  have key := tameNorm_sub_one_mul hq g
  simp only [tameD, tameC, tameA, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul, ← key]
  simp only [smul_sub, smul_smul, neg_smul, sub_mul, one_mul, sub_smul, mul_comm (g - 1)]
  abel

/-- **`DC = CA`** (tex L3476) as soon as `(q - 1)/2 · (g² - 1) = 0` in `R`: in the binary family
`g² = 1`; at the moving prime `g = 1 + t` and `2^{i+1} ∣ r - 1`. -/
theorem tameD_comp_tameC {q : ℕ} (hq : Odd q) (Φ : M →ₗ[R] M) {g : R}
    (hg : (((q - 1) / 2 : ℕ) : R) * (g ^ 2 - 1) = 0) :
    tameD q Φ g ∘ₗ tameC g = tameC g ∘ₗ tameA Φ := by
  have h := tameD_comp_tameC_sub hq Φ g
  rw [hg, neg_zero, zero_smul, sub_eq_zero] at h
  exact h

theorem tameD1_comp_tameD0 {q : ℕ} (hq : Odd q) (Φ : M →ₗ[R] M) {g : R}
    (hg : (((q - 1) / 2 : ℕ) : R) * (g ^ 2 - 1) = 0) :
    tameD1 q Φ g ∘ₗ tameD0 Φ g = 0 := by
  ext v
  have h := congrArg (fun f => f v) (tameD_comp_tameC hq Φ hg)
  simp only [LinearMap.comp_apply] at h
  change -(tameC g (tameA Φ v)) + tameD q Φ g (tameC g v) = 0
  rw [h, neg_add_cancel]

theorem tameNorm_one {q : ℕ} (hq : Odd q) : tameNorm q (1 : R) = q := by
  obtain ⟨m, rfl⟩ := hq
  unfold tameNorm
  have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  have h2 : (2 * m + 1 - 1) / 2 = m := by omega
  rw [h1, h2]; push_cast; ring

theorem tameD0_one (Φ : M →ₗ[R] M) :
    tameD0 Φ (1 : R) = LinearMap.inl R M M ∘ₗ (Φ - LinearMap.id) := by
  ext v <;> simp [tameD0, tameA, tameC]

theorem tameD1_one {q : ℕ} (hq : Odd q) (Φ : M →ₗ[R] M) :
    tameD1 q Φ (1 : R) = (Φ - (q : R) • LinearMap.id) ∘ₗ LinearMap.snd R M M := by
  ext v <;> simp [tameD1, tameD, tameC, tameNorm_one hq]

end

/-- **The tame split local model (4.4)** (tex L3470–3479). For a commutative coefficient ring
`R`, an `R`-module `M`, an `R`-linear Frobenius `Φ`, an odd residue cardinality `q` and a tame
inertia image `g ∈ R`:
1. if `g² = 1` (the binary family, `g ∈ G`), `N_q(g) = (q+1)/2 + (q-1)/2 · g` equals
   `1 + g + ⋯ + g^{q-1}`;
2. `DC - CA = -((q-1)/2)(g² - 1)`;
3. hence, when `(q-1)/2 · (g² - 1) = 0` (binary family: `g² = 1`; moving prime: `g = 1 + t`
   with `2^{i+1} ∣ r - 1`), `DC = CA` and `d¹ ∘ d⁰ = 0`, so `M → M ⊕ M → M` is a complex;
4. at augmentation `g = 1`: `d⁰ = (Φ - 1, 0)` and `d¹ = (0, Φ - q)`, i.e. the complex is the
   direct sum of the unramified complex `[Φ - 1]` in degrees zero and one and the singular
   quotient `[Φ - q]` in degrees one and two. -/
def TameModelNode : Prop :=
  ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (q : ℕ) (Φ : M →ₗ[R] M)
    (g : R), Odd q →
    (g ^ 2 = 1 → ∑ k ∈ range q, g ^ k = tameNorm q g) ∧
    tameD q Φ g ∘ₗ tameC g - tameC g ∘ₗ tameA Φ =
      -((((q - 1) / 2 : ℕ) : R) * (g ^ 2 - 1)) • LinearMap.id ∧
    ((((q - 1) / 2 : ℕ) : R) * (g ^ 2 - 1) = 0 →
      tameD q Φ g ∘ₗ tameC g = tameC g ∘ₗ tameA Φ ∧ tameD1 q Φ g ∘ₗ tameD0 Φ g = 0) ∧
    tameD0 Φ (1 : R) = LinearMap.inl R M M ∘ₗ (Φ - LinearMap.id) ∧
    tameD1 q Φ (1 : R) = (Φ - (q : R) • LinearMap.id) ∘ₗ LinearMap.snd R M M

theorem tameModelNode_proof : TameModelNode := by
  intro R _ M _ _ q Φ g hq
  exact ⟨fun hg => geom_sum_eq_tameNorm hq hg, tameD_comp_tameC_sub hq Φ g,
    fun hg => ⟨tameD_comp_tameC hq Φ hg, tameD1_comp_tameD0 hq Φ hg⟩, tameD0_one Φ, tameD1_one hq Φ⟩

end ZInQ.Contrib.CloudB3RC53.Duality
