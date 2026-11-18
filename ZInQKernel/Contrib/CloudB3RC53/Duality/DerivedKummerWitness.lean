import ZInQKernel.Contrib.CloudB3RC53.Duality.DerivedKummerTrunc

/-!
# Duality area: the derived Kummer step fails for the untruncated target (a witness)

For `M = ℤ/2` (a condition with two-primary torsion) and an untruncated two-term model of the local
target with `H¹ ≠ 0` torsion, the restricted pairing can vanish on `H¹ × H¹ → H²` and still fail to
be null-homotopic: the class has a component in `Hom(Tor₁(M, M), H¹)` that Elliot's divisibility
argument does not see (tex L3443–3450). Over `S = ℤ₂`:

* `U`: `ℤ₂ --2--> ℤ₂` in degrees `0, 1` (a free resolution of `ℤ/2`, so `U ≃ M[−1]`);
* `T`: `ℤ₂ --2--> ℤ₂ --0--> ℤ₂` in degrees `0, 1, 2` (`H⁰ = 0`, `H¹ = ℤ/2`, `H² = ℤ₂`, the shape of
  `RΓ(F, ℤ₂(1))` with `μ₂ ⊂ H¹`);
* `P : U × U → T` (`pairEx`): `e₀ ∪ e₀ = t₀`, `e₀ ∪ e₁ = t₁`, `e₁ ∪ e₀ = 0`, `e₁ ∪ e₁ = 0`, a
pairing
  of complexes (Leibniz rule PROVED).

Results (PROVED):

* `pairEx_11`: the bidegree `(1, 1)` component vanishes, so the form on `H¹(U) × H¹(U) → H²(T)` is
  zero (and so is every value: finite isotropy holds trivially);
* `pairEx_not_nullHomotopic`: there is NO family `h` of degree `−1` with
  `d h + h d = P` (the isotropy identity of `SelPairData` / `IsotropyData`): evaluating at
  `(e₀, e₁)` gives `2 (p + r) = 1` in `ℤ₂`.

So for the untruncated target the homotopy class is not determined by `Hom(M ⊗ M, ℤ₂)`; for the
truncated target `τ≥2` it is (`derivedKummerStep_trunc`), and the class here vanishes there (its
only
component into degrees `≥ 2` is the zero `(1, 1)` component).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Duality

open ZInQ.Contrib.CloudB3RC53.PairedFunctional

/-- Ranks of `U`: one in degrees `0, 1`. -/
def rkU (i : ℤ) : ℕ := if i = 0 ∨ i = 1 then 1 else 0

/-- Ranks of `T`: one in degrees `0, 1, 2`. -/
def rkT (i : ℤ) : ℕ := if 0 ≤ i ∧ i ≤ 2 then 1 else 0

theorem sum_eq_zero_of_rk {n : ℕ} (hn : n = 0) (x : Fin n → ℤ_[2]) : ∑ a, x a = 0 := by
  subst hn; simp

/-- The differential scalar: `2` out of degree `0`, `0` elsewhere. -/
def cD (i : ℤ) : ℤ_[2] := if i = 0 then 2 else 0

/-- The linear map `x ↦ (c · Σ x)` between rank-function modules. -/
def scal {m n : ℕ} (c : ℤ_[2]) : (Fin m → ℤ_[2]) →ₗ[ℤ_[2]] (Fin n → ℤ_[2]) where
  toFun x := fun _ => c * ∑ a, x a
  map_add' x y := by funext; simp [Finset.sum_add_distrib, mul_add]
  map_smul' r x := by funext; simp [Finset.mul_sum]; ring_nf

theorem sum_scal {m n : ℕ} (c : ℤ_[2]) (x : Fin m → ℤ_[2]) :
    ∑ b : Fin n, scal (n := n) c x b = n * (c * ∑ a, x a) := by
  simp [scal]

/-- `U`: `ℤ₂ --2--> ℤ₂` in degrees `0, 1`. -/
def Uex : GCx ℤ_[2] where
  X i := ModuleCat.of ℤ_[2] (Fin (rkU i) → ℤ_[2])
  d i j _ := scal (cD i)
  d_d i j k hij hjk x := by
    funext m
    change cD j * ∑ b, (cD i * ∑ a, x a) = 0
    by_cases hj : j = 0
    · subst hj
      have : rkU i = 0 := by simp [rkU]; omega
      rw [sum_eq_zero_of_rk this x, mul_zero, Finset.sum_const_zero, mul_zero]
    · simp [cD, hj]

/-- `T`: `ℤ₂ --2--> ℤ₂ --0--> ℤ₂` in degrees `0, 1, 2`. -/
def Tex : GCx ℤ_[2] where
  X i := ModuleCat.of ℤ_[2] (Fin (rkT i) → ℤ_[2])
  d i j _ := scal (cD i)
  d_d i j k hij hjk x := by
    funext m
    change cD j * ∑ b, (cD i * ∑ a, x a) = 0
    by_cases hj : j = 0
    · subst hj
      have : rkT i = 0 := by simp [rkT]; omega
      rw [sum_eq_zero_of_rk this x, mul_zero, Finset.sum_const_zero, mul_zero]
    · simp [cD, hj]

/-- The pairing coefficients: `e₀ ∪ e₀ = t₀`, `e₀ ∪ e₁ = t₁`, others `0`. -/
def coefP (i j : ℤ) : ℤ_[2] := if i = 0 ∧ (j = 0 ∨ j = 1) then 1 else 0

/-- The bilinear map `(x, y) ↦ c · Σ x · Σ y`. -/
def bil {m n r : ℕ} (c : ℤ_[2]) :
    (Fin m → ℤ_[2]) →ₗ[ℤ_[2]] (Fin n → ℤ_[2]) →ₗ[ℤ_[2]] (Fin r → ℤ_[2]) :=
  LinearMap.mk₂ ℤ_[2] (fun x y => fun _ => c * (∑ a, x a) * ∑ b, y b)
    (fun x x' y => by funext; simp [Finset.sum_add_distrib]; ring)
    (fun s x y => by
      funext
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring)
    (fun x y y' => by funext; simp [Finset.sum_add_distrib]; ring)
    (fun s x y => by
      funext
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring)

theorem rkU_of {i : ℤ} (h : ¬ (i = 0 ∨ i = 1)) : rkU i = 0 := by simp [rkU, h]

/-- **The pairing** `U × U → T`: `e₀ ∪ e₀ = t₀`, `e₀ ∪ e₁ = t₁`, others zero. -/
def pairEx : GPair Uex Uex Tex where
  P i j _ _ := bil (coefP i j)
  leib i i₁ j j₁ k k₁ h hi hj hk x y := by
    funext m
    change cD k * ∑ b : Fin (rkT k), (coefP i j * (∑ a, x a) * ∑ a, y a) =
      coefP i₁ j * (∑ b : Fin (rkU i₁), cD i * ∑ a, x a) * (∑ a, y a) +
        (sgn i : ℤ_[2]) * (coefP i j₁ * (∑ a, x a) * ∑ b : Fin (rkU j₁), cD j * ∑ a, y a)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    by_cases hi0 : i = 0 ∨ i = 1
    · by_cases hj0 : j = 0 ∨ j = 1
      · rcases hi0 with rfl | rfl <;> rcases hj0 with rfl | rfl
        all_goals
          obtain rfl : i₁ = _ := hi.symm
          obtain rfl : j₁ = _ := hj.symm
          obtain rfl : k = _ := h.symm
          obtain rfl : k₁ = _ := hk.symm
          simp [rkU, rkT, cD, coefP, sgn]
        all_goals ring
      · rw [sum_eq_zero_of_rk (rkU_of hj0) y]; ring
    · rw [sum_eq_zero_of_rk (rkU_of hi0) x]; ring

/-- **The form on `H¹ × H¹ → H²` vanishes**: the bidegree `(1, 1)` component is zero. -/
theorem pairEx_11 (u v : Uex.X 1) : pairEx.P 1 1 2 rfl u v = 0 := by
  funext m
  change coefP 1 1 * (∑ a, u a) * (∑ a, v a) = 0
  simp [coefP]

/-- `2` is not invertible in `ℤ₂`: `2 c ≠ 1`. -/
theorem two_mul_ne_one (c : ℤ_[2]) : 2 * c ≠ 1 := by
  intro h
  have h1 : ‖(2 : ℤ_[2]) * c‖ = 1 := by rw [h, norm_one]
  rw [norm_mul] at h1
  have hp : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
    have := PadicInt.norm_p (p := 2); exact_mod_cast this
  have := PadicInt.norm_le_one c
  rw [hp] at h1
  nlinarith [norm_nonneg c]

/-- **The pairing is not null-homotopic** (untruncated target): no family of degree `−1` satisfies
the isotropy identity `d h + h d = P`. -/
theorem pairEx_not_nullHomotopic :
    ¬ ∃ hh : ∀ i j k : ℤ, i + j = k + 1 → Uex.X i →ₗ[ℤ_[2]] Uex.X j →ₗ[ℤ_[2]] Tex.X k,
      ∀ (i i₁ j j₁ l l₁ : ℤ) (h : i + j = l + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
        (hl : l + 1 = l₁) (x : Uex.X i) (y : Uex.X j),
        Tex.d l l₁ hl (hh i j l h x y) + hh i₁ j l₁ (by omega) (Uex.d i i₁ hi x) y +
          sgn i • hh i j₁ l₁ (by omega) x (Uex.d j j₁ hj y) =
        pairEx.P i j l₁ (by omega) x y := by
  rintro ⟨hh, hid⟩
  let e0 : Uex.X 0 := fun _ => 1
  let e1 : Uex.X 1 := fun _ => 1
  have key := congrFun (hid 0 1 1 2 0 1 rfl rfl rfl rfl e0 e1) ⟨0, by simp [rkT]⟩
  have hd0 : Uex.d 0 1 rfl e0 = (2 : ℤ_[2]) • e1 := by
    funext m
    change cD 0 * ∑ a : Fin (rkU 0), (1 : ℤ_[2]) = 2 * 1
    simp only [cD, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [rkU]
  have h2 : Subsingleton (Uex.X 2) := by
    change Subsingleton (Fin (rkU 2) → ℤ_[2])
    have : rkU 2 = 0 := by simp [rkU]
    rw [this]; infer_instance
  rw [hd0, Subsingleton.elim (Uex.d 1 2 rfl e1) 0, map_smul, map_zero, smul_zero,
    add_zero] at key
  change cD 0 * (∑ a : Fin (rkT 0), hh 0 1 0 rfl e0 e1 a) +
    (2 : ℤ_[2]) * hh 1 1 1 rfl e1 e1 ⟨0, by simp [rkT]⟩ =
      coefP 0 1 * (∑ a : Fin (rkU 0), e0 a) * ∑ a : Fin (rkU 1), e1 a at key
  simp only [cD, coefP, ↓reduceIte, true_and, or_true, one_mul] at key
  have hs0 : ∑ a : Fin (rkU 0), e0 a = 1 := by
    simp only [e0, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp [rkU]
  have hs1 : ∑ a : Fin (rkU 1), e1 a = 1 := by
    simp only [e1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp [rkU]
  rw [hs0, hs1, mul_one, ← mul_add] at key
  exact two_mul_ne_one _ key

end ZInQ.Contrib.CloudB3RC53.Duality
