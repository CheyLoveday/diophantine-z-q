import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.SignSplitting

/-!
# RC53 SwitchInputs: the local action `J` on `F` and `−J` on `S` at an inert derivative prime

Proposition `ex:limits-uniform-lower-bound`, proof, tex L5027–5037:

> At a new inert derivative prime write `F, S` for the finite and singular planes. The action on
> `F` is `J`, and that on `S` is `−J`. Indeed, the local rational Frobenius acts on the Tate module
> by `J`; it fixes its square, the finite Frobenius generator, and conjugates tame inertia by its
> `ℓ`-th power. The retained congruences give `ℓ = −1` in the limit, so pullback on the tame
> coordinate contributes `ℓ⁻¹ = −1`.

This file proves that computation on degree-one cochains of a group `G` (the tame local Galois
group at the derivative prime), and discharges the local clause `hloc` of
`GaloisInvolution.galoisCocycleInvolution_genuine` from it.

Setup (all hypotheses explicit):
* `ρ : G →* End_k(T)`, `T = k²` (the Tate-module coefficients reduced to the fibre field);
* `Φ ∈ G` the local rational Frobenius (the element `τ` of the involution at a `τ`-fixed place),
  `J = ρ Φ`, `J² = 1`;
* `φ = Φ²` the finite Frobenius generator;
* `σ ∈ G` a tame inertia generator acting trivially on `T` (`ρ σ = 1`, inertia acts trivially at
  the inert, good prime), with `Φ⁻¹ σ Φ = σ^m` for an integer `m` that is `−1` in `k` (the retained
  congruence `ℓ ≡ −1`, so `ℓ⁻¹ ≡ −1`).
* The cocycle action is `c ↦ (g ↦ ρ Φ (c (Φ⁻¹ g Φ)))`, the degree-one component of the involution
  `c ↦ ρ(τ) ∘ c(τ⁻¹ · τ)` (GaloisInvolution, `ConjData.localMap` at a fixed place with
  `β = conjugation by Φ`, `T = ρ Φ`).
* The coordinates of a cocycle are `(c φ, c σ)`: since `φ` and `σ` act trivially on `T`, the
  unramified (finite) part is read off at `φ` and the tame (singular) part at `σ`, and coboundaries
  have coordinates zero (`coord_coboundary`).

Nodes (PROVED):
* `cocycle_zpow_of_trivial`: `c(σⁿ) = n • c(σ)` when `ρ σ = 1`.
* `IsCocycle.act`: the action preserves cocycles.
* `LocalJAction` (tex L5027–5037): `coord (act c) = localInv J (coord c)`, i.e. `J` on `F`, `−J` on
  `S`.
* `hloc_of_cocycleRep`: the clause `hloc` of `galoisCocycleInvolution_genuine` (in its exact shape
  `locH (Hσ v) = localInv J (locH v)`) for any localization `locH` represented by local cocycles on
  which the involution acts by the cocycle action up to a coboundary.
* Non-vacuity: the infinite dihedral group with `σ = r 1`, `Φ = sr 0`, `m = −1`,
  `ρ(r i) = 1`, `ρ(sr i) = diag(1, −1)` over `ℚ`, and a cocycle with nonzero singular coordinate.

GLUE left (stated as the hypotheses of `hloc_of_cocycleRep`): that the local component of the
genuine Selmer involution at the derivative prime is this cocycle action on local representatives,
and that the genuine localization `locH` is read off as `(c φ, c σ)` on them (the identification of
`F`, `S` with the cochain coordinates).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs


variable {k : Type} [Field k] {G : Type} [Group G]

/-- Degree-one cocycles for `ρ`: `c (g h) = c g + ρ g (c h)`. -/
def IsCocycle (ρ : G →* Module.End k (Fin 2 → k)) (c : G → (Fin 2 → k)) : Prop :=
  ∀ g h, c (g * h) = c g + ρ g (c h)

/-- The cocycle action `c ↦ (g ↦ ρ Φ (c (Φ⁻¹ g Φ)))` (tex L5009–5011 at a `τ`-fixed place). -/
def cocAct (ρ : G →* Module.End k (Fin 2 → k)) (Φ : G) (c : G → (Fin 2 → k)) : G → (Fin 2 → k) :=
  fun g => ρ Φ (c (Φ⁻¹ * g * Φ))

/-- The coordinates `(c φ, c σ)` of a cochain on `F ⊕ S`. -/
def coord (φ σ : G) (c : G → (Fin 2 → k)) : (Fin 2 → k) × (Fin 2 → k) := (c φ, c σ)

/-- A cocycle vanishes at `1`. -/
theorem IsCocycle.map_one {ρ : G →* Module.End k (Fin 2 → k)} {c : G → (Fin 2 → k)}
    (hc : IsCocycle ρ c) : c 1 = 0 := by
  have h := hc 1 1
  rw [mul_one, ρ.map_one, Module.End.one_apply] at h
  have : c 1 + c 1 = c 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

/-- **`c(σⁿ) = n • c(σ)` for `σ` acting trivially.** PROVED. -/
theorem cocycle_zpow_of_trivial {ρ : G →* Module.End k (Fin 2 → k)} {c : G → (Fin 2 → k)}
    (hc : IsCocycle ρ c) {σ : G} (hσ : ρ σ = 1) (n : ℤ) : c (σ ^ n) = n • c σ := by
  have hpow : ∀ m : ℤ, ρ (σ ^ m) = 1 := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ i ih => rw [zpow_add_one, ρ.map_mul, ih, hσ, one_mul]
    | pred i ih =>
      have h := ρ.map_mul (σ ^ (-(i : ℤ) - 1)) σ
      rw [← zpow_add_one, sub_add_cancel, ih, hσ, mul_one] at h
      exact h.symm
  induction n using Int.induction_on with
  | zero => simp [hc.map_one]
  | succ i ih =>
    rw [zpow_add_one, hc, ih, hpow, Module.End.one_apply, add_smul, one_smul]
  | pred i ih =>
    have h := hc (σ ^ (-(i : ℤ) - 1)) σ
    rw [← zpow_add_one, sub_add_cancel, ih, hpow, Module.End.one_apply] at h
    have : c (σ ^ (-(i : ℤ) - 1)) = (-(i : ℤ)) • c σ - c σ := by rw [h]; abel
    rw [this, sub_smul, one_smul]

/-- **The action preserves cocycles.** PROVED. -/
theorem IsCocycle.act {ρ : G →* Module.End k (Fin 2 → k)} {c : G → (Fin 2 → k)}
    (hc : IsCocycle ρ c) (Φ : G) : IsCocycle ρ (cocAct ρ Φ c) := by
  intro g h
  simp only [cocAct]
  have e : Φ⁻¹ * (g * h) * Φ = (Φ⁻¹ * g * Φ) * (Φ⁻¹ * h * Φ) := by group
  rw [e, hc, map_add]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/-- **Coboundaries have zero coordinates** when `φ`, `σ` act trivially. PROVED. -/
theorem coord_coboundary (ρ : G →* Module.End k (Fin 2 → k)) {φ σ : G} (hφ : ρ φ = 1)
    (hσ : ρ σ = 1) (t : Fin 2 → k) : coord φ σ (fun g => ρ g t - t) = 0 := by
  simp [coord, hφ, hσ]

/-- **The local action is `J` on `F` and `−J` on `S`** (tex L5027–5037). For `J = ρ Φ`, `φ = Φ²`,
`σ` acting trivially with `Φ⁻¹ σ Φ = σ^m`, `m = −1` in `k`, and every cocycle `c`:
`coord (act c) = localInv J (coord c)`. Classification: PROVED. -/
def LocalJAction : Prop :=
  ∀ (k : Type) [Field k] (G : Type) [Group G] (ρ : G →* Module.End k (Fin 2 → k)) (φ σ Φ : G)
    (m : ℤ), φ = Φ * Φ → Φ⁻¹ * σ * Φ = σ ^ m → ρ σ = 1 → (m : k) = -1 →
    ∀ c : G → (Fin 2 → k), IsCocycle ρ c →
      coord φ σ (cocAct ρ Φ c) = localInv (ρ Φ) (coord φ σ c)

theorem localJAction_proof : LocalJAction := by
  intro k _ G _ ρ φ σ Φ m hφ hconj hσ hm c hc
  rw [localInv_apply]
  simp only [coord, cocAct]
  refine Prod.ext ?_ ?_
  · -- `Φ` commutes with `φ = Φ²`
    have : Φ⁻¹ * φ * Φ = φ := by rw [hφ]; group
    simp only [this]
  · simp only
    rw [hconj, cocycle_zpow_of_trivial hc hσ m]
    rw [show (m • c σ : Fin 2 → k) = (m : k) • c σ by rw [Int.cast_smul_eq_zsmul], hm, neg_one_smul,
      map_neg]

/-- **The clause `hloc` from local cocycle representatives** (the exact shape of the hypothesis
`hloc` of `GaloisInvolution.galoisCocycleInvolution_genuine`). Let `V` be the fibre cohomology,
`Hσ` its involution, `locH : V → F ⊕ S` the localization at the derivative prime. Suppose every `v`
has a local cocycle representative `rep v` with `coord (rep v) = locH v`, and the involution acts on
representatives by the cocycle action up to a coboundary. Then `locH (Hσ v) = localInv J (locH v)`
with `J = ρ Φ`. Classification: PROVED (from the stated representation hypotheses). -/
theorem hloc_of_cocycleRep (ρ : G →* Module.End k (Fin 2 → k)) (φ σ Φ : G) (m : ℤ)
    (hφ : φ = Φ * Φ) (hconj : Φ⁻¹ * σ * Φ = σ ^ m) (hσ : ρ σ = 1) (hm : (m : k) = -1)
    (hJ2 : ρ Φ * ρ Φ = 1)
    {V : Type} (Hσ : V → V) (locH : V → (Fin 2 → k) × (Fin 2 → k)) (rep : V → G → (Fin 2 → k))
    (hrep : ∀ v, IsCocycle ρ (rep v)) (hcoord : ∀ v, coord φ σ (rep v) = locH v)
    (hact : ∀ v, ∃ t : Fin 2 → k, ∀ g, rep (Hσ v) g = cocAct ρ Φ (rep v) g + (ρ g t - t)) :
    ∀ v, locH (Hσ v) = localInv (ρ Φ) (locH v) := by
  intro v
  have hφ1 : ρ φ = 1 := by rw [hφ, map_mul, hJ2]
  obtain ⟨t, ht⟩ := hact v
  rw [← hcoord, ← hcoord]
  have e : coord φ σ (rep (Hσ v)) = coord φ σ (cocAct ρ Φ (rep v)) +
      coord φ σ (fun g => ρ g t - t) := by
    simp only [coord, ht, Prod.mk_add_mk]
  rw [e, coord_coboundary ρ hφ1 hσ, add_zero]
  exact localJAction_proof k G ρ φ σ Φ m hφ hconj hσ hm (rep v) (hrep v)

/-! ### Non-vacuity -/

/-- `J₀ = diag(1, −1)` as an endomorphism of `ℚ²`. -/
def exJ : Module.End ℚ (Fin 2 → ℚ) := Matrix.toLin' (Matrix.diagonal ![1, -1])

theorem exJ_mul_self : exJ * exJ = 1 := by
  rw [exJ, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.diagonal_mul_diagonal]
  have : Matrix.diagonal (fun i => ![(1 : ℚ), -1] i * ![(1 : ℚ), -1] i) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [this, Matrix.toLin'_one]
  rfl

/-- The representation of the infinite dihedral group: rotations (tame inertia) act trivially,
reflections (Frobenius-type) act by `J₀`. -/
def exRho : DihedralGroup 0 →* Module.End ℚ (Fin 2 → ℚ) where
  toFun g := match g with
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => exJ
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · simp [DihedralGroup.r_mul_r]
    · simp [DihedralGroup.r_mul_sr]
    · simp [DihedralGroup.sr_mul_r]
    · simp only [DihedralGroup.sr_mul_sr]; exact exJ_mul_self.symm

theorem exRho_r (i : ZMod 0) : exRho (DihedralGroup.r i) = 1 := rfl

theorem exRho_sr (i : ZMod 0) : exRho (DihedralGroup.sr i) = exJ := rfl

/-- **Non-vacuity of the hypotheses** (non-vacuity): in the infinite dihedral group, `σ = r 1` (tame
inertia), `Φ = sr 0` (rational Frobenius), `φ = Φ² = 1`, `m = −1`: the relations hold, `σ` acts
trivially, `J₀² = 1`, so `LocalJAction` and `hloc_of_cocycleRep` apply. PROVED. -/
theorem exLocalJ_hyps :
    (1 : DihedralGroup 0) = DihedralGroup.sr 0 * DihedralGroup.sr 0 ∧
    (DihedralGroup.sr 0)⁻¹ * DihedralGroup.r 1 * DihedralGroup.sr 0 =
      (DihedralGroup.r 1 : DihedralGroup 0) ^ (-1 : ℤ) ∧
    exRho (DihedralGroup.r 1) = 1 ∧ ((-1 : ℤ) : ℚ) = -1 ∧
    exRho (DihedralGroup.sr 0) * exRho (DihedralGroup.sr 0) = 1 := by
  refine ⟨?_, ?_, rfl, by norm_num, exJ_mul_self⟩
  · rw [DihedralGroup.sr_mul_sr]; rfl
  · rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, zpow_neg, zpow_one,
      DihedralGroup.inv_r]
    congr 1

/-- `e₁ = (0, 1)`, a `−1`-eigenvector of `J₀`. -/
def exE1 : Fin 2 → ℚ := ![0, 1]

theorem exJ_e1 : exJ exE1 = -exE1 := by
  ext i; fin_cases i <;> simp [exJ, exE1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- The underlying integer of an element of `ZMod 0 = ℤ`. -/
def zi (i : ZMod 0) : ℤ := i

/-- A cocycle with nonzero singular coordinate: `c(r i) = i • e₁`, `c(sr i) = −i • e₁`. -/
def exCoc : DihedralGroup 0 → (Fin 2 → ℚ)
  | DihedralGroup.r i => zi i • exE1
  | DihedralGroup.sr i => (-zi i) • exE1

theorem exCoc_cocycle : IsCocycle exRho exCoc := by
  have hadd : ∀ i j : ZMod 0, zi (i + j) = zi i + zi j := fun _ _ => rfl
  have hsub : ∀ i j : ZMod 0, zi (j - i) = zi j - zi i := fun _ _ => rfl
  rintro (i | i) (j | j)
  · simp only [DihedralGroup.r_mul_r, exCoc, exRho_r,
      Module.End.one_apply]
    rw [hadd, add_smul]
  · simp only [DihedralGroup.r_mul_sr, exCoc, exRho_r,
      Module.End.one_apply]
    rw [hsub, ← add_smul]; congr 1; ring
  · simp only [DihedralGroup.sr_mul_r, exCoc, exRho_sr]
    rw [hadd, map_zsmul, exJ_e1, smul_neg, ← neg_smul, ← add_smul]; congr 1; ring
  · simp only [DihedralGroup.sr_mul_sr, exCoc, exRho_sr]
    rw [hsub, map_zsmul, exJ_e1, smul_neg, ← neg_smul, ← add_smul]; congr 1; ring

/-- **The computation on the example** (non-vacuity): the singular coordinate of `exCoc` is
`e₁ ≠ 0`, and `LocalJAction` gives the transformed coordinates `localInv J₀ (0, e₁) = (0, e₁)`
(since `−J₀ e₁ = e₁`). PROVED. -/
theorem exLocalJ_coords :
    coord (1 : DihedralGroup 0) (DihedralGroup.r 1) exCoc = (0, exE1) ∧ exE1 ≠ 0 ∧
    coord (1 : DihedralGroup 0) (DihedralGroup.r 1) (cocAct exRho (DihedralGroup.sr 0) exCoc) =
      localInv (exRho (DihedralGroup.sr 0)) (0, exE1) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := exLocalJ_hyps
  have hc : coord (1 : DihedralGroup 0) (DihedralGroup.r 1) exCoc = (0, exE1) := by
    simp only [coord]
    refine Prod.ext ?_ ?_
    · exact exCoc_cocycle.map_one
    · change zi 1 • exE1 = exE1
      rw [show zi 1 = 1 from rfl, one_smul]
  refine ⟨hc, ?_, ?_⟩
  · intro h
    have := congrFun h 1
    simp [exE1] at this
  · rw [← hc]
    exact localJAction_proof ℚ (DihedralGroup 0) exRho 1 (DihedralGroup.r 1) (DihedralGroup.sr 0)
      (-1) h1 h2 h3 h4 exCoc exCoc_cocycle

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
