import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericSides

/-!
# RC53 SwitchInputs: non-vacuity and an obstruction for the field-generic tame coordinates

Manuscript `diophantine_zq.tex`, tex L5027–5037 (the coordinates `H¹(W_rel) ≅ k² × k²` at an inert
derivative prime from the tame quotient `⟨φ, σ | φσφ⁻¹ = σ^q⟩`).

* `homOfZ1K`, `ev1K_one_of_trivial`, `ev1K_inv_of_trivial`, `ev1K_zpow_of_trivial` (PROVED): with
  the trivial action, `1`-cocycles are additive maps `G → M`.
* **Non-vacuity** (`tameCoordinatesTrivialK_example`, PROVED): the GLUE input
  `TameCoordinatesTrivialK` holds over `k = ℚ` for the discrete group `G = ℤ²` (written
  multiplicatively), `M = ℚ²` with the trivial action and its usual (non-discrete) topology,
  `φ = (1, 0)`, `σ = (0, 1)`, `I = ⟨σ⟩`. Here `φσφ⁻¹ = σ`, i.e. the tame relation holds
  with `q = 1`.
* **Obstruction** (PROVED): `ev1K_mul` (the cocycle identity `z(gh) = z(g) + g • z(h)`);
  `ev1K_eq_zero_of_tame'`: if `φ`, `σ` act trivially on `M` and `φσφ⁻¹ = σ^q` with `(q : k) ≠ 1`,
  every `1`-cocycle vanishes at `σ`; hence `not_bijective_coordQK_of_tame`: for `M ≠ 0` the tame
  coordinates `[z] ↦ (z(φ), z(σ))` are not surjective, whatever the action of the rest of `G`, and
  `not_tameCoordinatesTrivialK_of_tame`: `TameCoordinatesTrivialK k M I φ σ` fails. In a local
  Galois group `G_{K_q}` (`q = |𝓀_q|`) a Frobenius lift and a tame generator satisfy
  `φσφ⁻¹ = σ^q` in the tame quotient (modulo the pro-`p` wild inertia), and `(q : k) ≠ 1` in
  characteristic zero; so wherever the relation holds in the group acting on the cochains (or the
  cocycles vanish on the wild inertia), the tame coordinates of `DerivativeCoords` /
  `GenericCoords` cannot be bijective over a characteristic-zero `k = k(𝔭)` (contrast `𝔽₂`, where
  `q` is odd and `(q : 𝔽₂) = 1`). The example above has `q = 1`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Manuscript.RC.SelmerComplex

section Additive

variable {k : Type} [Field k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- A `1`-cocycle vanishes at the identity (trivial action). PROVED. -/
theorem ev1K_one_of_trivial (htriv : ∀ (g : G) (m : M), g • m = m) (z : Z1K k G M) :
    ev1K (z : (contCochains k G M).X 1) 1 = 0 := by
  have h := ev1K_mul_of_trivial htriv z 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

/-- With the trivial action, a `1`-cocycle is an additive map `Additive G →+ M`. -/
def homOfZ1K (htriv : ∀ (g : G) (m : M), g • m = m) (z : Z1K k G M) : Additive G →+ M where
  toFun g := ev1K (z : (contCochains k G M).X 1) g.toMul
  map_zero' := ev1K_one_of_trivial htriv z
  map_add' g h := ev1K_mul_of_trivial htriv z g.toMul h.toMul

/-- `z(g⁻¹) = −z(g)` (trivial action). PROVED. -/
theorem ev1K_inv_of_trivial (htriv : ∀ (g : G) (m : M), g • m = m) (z : Z1K k G M) (g : G) :
    ev1K (z : (contCochains k G M).X 1) g⁻¹ = -ev1K (z : (contCochains k G M).X 1) g :=
  map_neg (homOfZ1K htriv z) (Additive.ofMul g)

/-- `z(gⁿ) = n • z(g)` (trivial action). PROVED. -/
theorem ev1K_zpow_of_trivial (htriv : ∀ (g : G) (m : M), g • m = m) (z : Z1K k G M) (g : G)
    (n : ℤ) :
    ev1K (z : (contCochains k G M).X 1) (g ^ n) = n • ev1K (z : (contCochains k G M).X 1) g :=
  map_zsmul (homOfZ1K htriv z) n (Additive.ofMul g)

/-- `z(gⁿ) = n • z(g)` for `n : ℕ` (trivial action). PROVED. -/
theorem ev1K_pow_of_trivial (htriv : ∀ (g : G) (m : M), g • m = m) (z : Z1K k G M) (g : G)
    (n : ℕ) :
    ev1K (z : (contCochains k G M).X 1) (g ^ n) = n • ev1K (z : (contCochains k G M).X 1) g :=
  map_nsmul (homOfZ1K htriv z) n (Additive.ofMul g)

/-! ### The obstruction: the tame relation with `q ≠ 1` in `k` -/

/-- **The cocycle identity** `z(gh) = z(g) + g • z(h)` for `1`-cocycles. PROVED. -/
theorem ev1K_mul (z : Z1K k G M) (g h : G) :
    ev1K (z : (contCochains k G M).X 1) (g * h) =
      ev1K (z : (contCochains k G M).X 1) g + g • ev1K (z : (contCochains k G M).X 1) h := by
  have hd := contCochains_d_apply (k := k) (G := G) (M := M) 1 (z : (contCochains k G M).X 1)
    ![g, h]
  have hz : ((contCochains k G M).d 1 (1 + 1)).hom (z : (contCochains k G M).X 1) = 0 := z.2
  rw [hz] at hd
  have e0 : (fun i : Fin 1 => (![g, h] : Fin 2 → G) i.succ) = fun _ => h := by
    funext i; fin_cases i; rfl
  have e1 : Fin.contractNth (0 : Fin 2) (· * ·) (![g, h] : Fin 2 → G) = fun _ => g * h := by
    funext i; fin_cases i; simp [Fin.contractNth]
  have e2 : Fin.contractNth (1 : Fin 2) (· * ·) (![g, h] : Fin 2 → G) = fun _ => g := by
    funext i; fin_cases i; simp [Fin.contractNth]
  rw [Fin.sum_univ_two, e0, e1, e2] at hd
  simp only [Fin.val_zero, Fin.val_one, zero_add, pow_one, neg_smul, one_smul] at hd
  change (0 : M) = g • ev1K (z : (contCochains k G M).X 1) h +
      (-ev1K (z : (contCochains k G M).X 1) (g * h) +
    (-1 : k) ^ (1 + 1) • ev1K (z : (contCochains k G M).X 1) g) at hd
  rw [show ((-1 : k) ^ (1 + 1)) = 1 by norm_num, one_smul] at hd
  rw [← sub_eq_zero]
  rw [eq_comm, ← sub_eq_zero] at hd
  rw [← neg_eq_zero, ← hd]
  abel

/-- **With `φ`, `σ` acting trivially and the tame relation `φσφ⁻¹ = σ^q`, `(q : k) ≠ 1`, every
`1`-cocycle vanishes at `σ`** (tex L5027–5037); the rest of `G` may act arbitrarily. PROVED. -/
theorem ev1K_eq_zero_of_tame' {φ σ : G} (hφ : ∀ m : M, φ • m = m) (hσ : ∀ m : M, σ • m = m)
    (q : ℕ) (hrel : φ * σ * φ⁻¹ = σ ^ q) (hq : (q : k) ≠ 1) (z : Z1K k G M) :
    ev1K (z : (contCochains k G M).X 1) σ = 0 := by
  set f := fun g => ev1K (z : (contCochains k G M).X 1) g with hf
  have h1 : f 1 = 0 := by
    have h := ev1K_mul z 1 1
    rw [mul_one, one_smul] at h
    exact left_eq_add.mp h
  have hinv : f φ⁻¹ = -f φ := by
    have h := ev1K_mul z φ φ⁻¹
    rw [mul_inv_cancel, hφ] at h
    exact eq_neg_of_add_eq_zero_right (h1.symm.trans h).symm
  have hσpow : ∀ n : ℕ, ∀ m : M, σ ^ n • m = m := by
    intro n m
    induction n with
    | zero => rw [pow_zero, one_smul]
    | succ n ih => rw [pow_succ, mul_smul, hσ, ih]
  have hpow : ∀ n : ℕ, f (σ ^ n) = n • f σ := by
    intro n
    induction n with
    | zero => rw [pow_zero, h1, zero_smul]
    | succ n ih =>
      have h := ev1K_mul z (σ ^ n) σ
      rw [← pow_succ, hσpow] at h
      change f (σ ^ (n + 1)) = f (σ ^ n) + f σ at h
      rw [h, ih, succ_nsmul]
  have hconj : f (φ * σ * φ⁻¹) = f σ := by
    have h := ev1K_mul z (φ * σ) φ⁻¹
    have h' := ev1K_mul z φ σ
    change f (φ * σ * φ⁻¹) = f (φ * σ) + (φ * σ) • f φ⁻¹ at h
    change f (φ * σ) = f φ + φ • f σ at h'
    rw [h, h', hφ, mul_smul, hσ, hφ, hinv]
    abel
  rw [hrel, hpow, ← Nat.cast_smul_eq_nsmul k] at hconj
  have h2 : ((q : k) - 1) • f σ = 0 := by
    rw [sub_smul, one_smul, hconj, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hq)

/-- **The tame coordinates are never bijective when `(q : k) ≠ 1`** (tex L5027–5037): if `M ≠ 0`,
`φ`, `σ` act trivially and `φσφ⁻¹ = σ^q` with `(q : k) ≠ 1`, then `[z] ↦ (z(φ), z(σ))` is not
surjective (whatever the action of the rest of `G`). PROVED. -/
theorem not_bijective_coordQK_of_tame [Nontrivial M] {φ σ : G} (hφ : ∀ m : M, φ • m = m)
    (hσ : ∀ m : M, σ • m = m) (q : ℕ) (hrel : φ * σ * φ⁻¹ = σ ^ q) (hq : (q : k) ≠ 1) :
    ¬ Function.Bijective (coordQK (k := k) (G := G) (M := M) φ σ hφ hσ) := by
  intro hbij
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨y, hy⟩ := hbij.2 (0, m)
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    rw [coordQK_mk] at hy
    have h := congrArg Prod.snd hy
    simp only at h
    rw [ev1K_eq_zero_of_tame' hφ hσ q hrel hq z] at h
    exact hm h.symm


/-- **With the trivial action and the tame relation `φσφ⁻¹ = σ^q`, `(q : k) ≠ 1`, every
`1`-cocycle vanishes at `σ`** (tex L5027–5037). PROVED. -/
theorem ev1K_eq_zero_of_tame (htriv : ∀ (g : G) (m : M), g • m = m) {φ σ : G} (q : ℕ)
    (hrel : φ * σ * φ⁻¹ = σ ^ q) (hq : (q : k) ≠ 1) (z : Z1K k G M) :
    ev1K (z : (contCochains k G M).X 1) σ = 0 := by
  have h1 : ev1K (z : (contCochains k G M).X 1) (φ * σ * φ⁻¹) =
      ev1K (z : (contCochains k G M).X 1) σ := by
    rw [ev1K_mul_of_trivial htriv, ev1K_mul_of_trivial htriv, ev1K_inv_of_trivial htriv]
    abel
  rw [hrel, ev1K_pow_of_trivial htriv, ← Nat.cast_smul_eq_nsmul k] at h1
  have h2 : ((q : k) - 1) • ev1K (z : (contCochains k G M).X 1) σ = 0 := by
    rw [sub_smul, one_smul, h1, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hq)

/-- **No tame coordinates with the trivial action when `(q : k) ≠ 1`** (tex L5027–5037): if
`M ≠ 0` and `φσφ⁻¹ = σ^q` with `(q : k) ≠ 1`, then `TameCoordinatesTrivialK k M I φ σ` fails (the
coordinate `(0, m)`, `m ≠ 0`, is not attained). PROVED. -/
theorem not_tameCoordinatesTrivialK_of_tame [Nontrivial M] {I : Subgroup G} {φ σ : G} (q : ℕ)
    (hrel : φ * σ * φ⁻¹ = σ ^ q) (hq : (q : k) ≠ 1) :
    ¬ TameCoordinatesTrivialK k M I φ σ :=
  fun T => not_bijective_coordQK_of_tame (T.htriv φ) (T.htriv σ) q hrel hq T.hbij

end Additive

/-! ### Non-vacuity over `ℚ`: the discrete group `ℤ²` -/

section Example

/-- The discrete group `ℤ²`, written multiplicatively. -/
abbrev GZ2 : Type := Multiplicative (ℤ × ℤ)

/-- `ℚ²` with the trivial action of `ℤ²` (usual topology). -/
abbrev MQ2 : Type := TrivMod GZ2 (Fin 2 → ℚ)

/-- The generator `φ = (1, 0)`. -/
abbrev φZ2 : GZ2 := Multiplicative.ofAdd (1, 0)

/-- The generator `σ = (0, 1)`. -/
abbrev σZ2 : GZ2 := Multiplicative.ofAdd (0, 1)

/-- The "inertia" `I = ⟨σ⟩`. -/
abbrev IZ2 : Subgroup GZ2 := Subgroup.zpowers σZ2

theorem gZ2_eq (g : GZ2) : g = φZ2 ^ (g.toAdd.1) * σZ2 ^ (g.toAdd.2) := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_zpow, toAdd_ofAdd, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
    Prod.mk_add_mk, add_zero, zero_add]

/-- **Non-vacuity of `TameCoordinatesTrivialK`** over `ℚ` (tex L5027–5037): `G = ℤ²` discrete,
`M = ℚ²` with the trivial action, `φ = (1, 0)`, `σ = (0, 1)`, `I = ⟨σ⟩`. PROVED. -/
theorem tameCoordinatesTrivialK_example : TameCoordinatesTrivialK ℚ MQ2 IZ2 φZ2 σZ2 := by
  have htriv : ∀ (g : GZ2) (m : MQ2), g • m = m := fun _ _ => rfl
  have hval : ∀ z : Z1K ℚ GZ2 MQ2, ∀ g : GZ2, ev1K (z : (contCochains ℚ GZ2 MQ2).X 1) g =
      g.toAdd.1 • ev1K (z : (contCochains ℚ GZ2 MQ2).X 1) φZ2 +
        g.toAdd.2 • ev1K (z : (contCochains ℚ GZ2 MQ2).X 1) σZ2 := by
    intro z g
    conv_lhs => rw [gZ2_eq g]
    rw [ev1K_mul_of_trivial htriv, ev1K_zpow_of_trivial htriv, ev1K_zpow_of_trivial htriv]
  refine ⟨htriv, ⟨LinearEquiv.refl ℚ (Fin 2 → ℚ)⟩, Subgroup.mem_zpowers σZ2, ⟨?_, ?_⟩, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      rw [LinearMap.mem_ker, coordQK_mk, Prod.mk_eq_zero] at hy
      have hz : z = 0 := by
        apply Subtype.ext
        apply Subtype.ext
        funext x
        have hx : x = fun _ => x 0 := by funext i; fin_cases i; rfl
        rw [hx]
        change ev1K (z : (contCochains ℚ GZ2 MQ2).X 1) (x 0) = 0
        rw [hval, hy.1, hy.2, smul_zero, smul_zero, add_zero]
      rw [hz, Submodule.mem_bot, Submodule.Quotient.mk_zero]
  · rintro ⟨m₁, m₂⟩
    let F : GZ2 → MQ2 := fun g => g.toAdd.1 • m₁ + g.toAdd.2 • m₂
    let cF : (contCochains ℚ GZ2 MQ2).X 1 :=
      ⟨(fun x => F (x 0) : (groupCohomology.inhomogeneousCochains (rep ℚ GZ2 MQ2)).X 1),
        mem_contCochain.mpr continuous_of_discreteTopology⟩
    have hev : ∀ g, ev1K cF g = F g := fun g => rfl
    have hZ : cF ∈ Z1K ℚ GZ2 MQ2 := mem_Z1K_of_additive htriv cF (fun g h => by
      rw [hev, hev, hev]
      simp only [F, toAdd_mul, Prod.fst_add, Prod.snd_add, add_smul]
      abel)
    refine ⟨Submodule.Quotient.mk ⟨cF, hZ⟩, ?_⟩
    rw [coordQK_mk]
    simp only [hev, F, toAdd_ofAdd, one_smul, zero_smul, add_zero, zero_add]
  · intro z hz h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [ev1K_zpow_of_trivial htriv, hz, smul_zero]

end Example

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
