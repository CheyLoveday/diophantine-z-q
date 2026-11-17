import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Transfer

/-!
# HeegnerCohomology, part 7: Shapiro followed by the coefficient map (H20)–(H21)

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 7,
tex 3202–3250: "Under Shapiro, followed by the equivariant coefficient map
`E[2^m] ⊗ A[Δ_f] → (E[2^m] ⊗ A)(θ)`, `v ⊗ [δ] ↦ θ(δ) v` (H20), obtain the class `P_{I,m}` over `K`.
Here the induced module is written with the diagonal Tate action and the left regular action on
its class-group basis. … These are the integral Shapiro and transfer maps of [Nekovář,
8.1.1–8.1.6], written with left cosets."

We write the induced module `M ⊗ A[Δ]` as functions `F : Δ → M` (`F = ∑_δ F(δ) ⊗ [δ]`), with the
diagonal action `(g F)(δ) = ρ(g) F(g⁻¹ δ)` (`indRep`), and prove (all `PROVED`):

* `shapiro_cochain_map`: the explicit Shapiro cochain map `Sh` from `H`-cochains in `M` to
  `G`-cochains in the induced module, `Sh(c)(g)(δ') = ρ(r_{δ'}) c(h-tuple of g at
  (g_0⋯g_{n-1})⁻¹ δ')`, defined as the untwisted transfer of `ι ∘ c` with `ι(m) = m ⊗ [1]`,
  commutes with the inhomogeneous differentials in every degree;
* `coeff_shapiro_eq_transfer`: the coefficient map (H20) applied to `Sh(c)` is exactly Elliot's
  twisted transfer `𝒯_θ c` (H21): `𝒯_θ = (H20) ∘ Shapiro`, in every degree;
* `coeff_equivariant`: the coefficient map (H20) is equivariant from the induced module to the
  `θρ`-twisted module (RC10 proves the same as `H20_equivariant`).
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

namespace TwistedTransfer

open Finset

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] (r : G ⧸ H → G)
  (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)
  {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ)

/-- The induced module `M ⊗ A[Δ]` as functions `Δ → M`, with the diagonal action
`(g F)(δ) = ρ(g) F(g⁻¹ δ)` (tex 3210–3211). -/
def indRep : G →* Module.End A (G ⧸ H → M) where
  toFun g :=
    { toFun := fun F δ => ρ g (F (((g : G) : G ⧸ H)⁻¹ * δ))
      map_add' := fun F F' => by funext δ; simp
      map_smul' := fun a F => by funext δ; simp }
  map_one' := by
    apply LinearMap.ext; intro F; funext δ; simp
  map_mul' g k := by
    apply LinearMap.ext; intro F; funext δ
    simp [mul_assoc, Module.End.mul_apply]

@[simp] theorem indRep_apply (g : G) (F : G ⧸ H → M) (δ : G ⧸ H) :
    indRep H ρ g F δ = ρ g (F (((g : G) : G ⧸ H)⁻¹ * δ)) := rfl

/-- `ι(m) = m ⊗ [1]`. -/
noncomputable def iota : M →+ (G ⧸ H → M) := by
  classical exact AddMonoidHom.single (fun _ => M) (1 : G ⧸ H)

theorem iota_apply [DecidableEq (G ⧸ H)] (m : M) (δ : G ⧸ H) :
    iota H m δ = if δ = 1 then m else 0 := by
  unfold iota
  by_cases h : δ = 1
  · subst h; simp
  · simp [h]

/-- The coefficient map (H20): `v ⊗ [δ] ↦ θ(δ) v`, i.e. `F ↦ ∑_δ θ(δ) F(δ)`. -/
def coeff [Fintype (G ⧸ H)] (F : G ⧸ H → M) : M := ∑ δ : G ⧸ H, (θ δ : A) • F δ

/-- **(H20) is equivariant** (tex 3214–3215: "left translation multiplies the value by
`θ(g)`"), `PROVED`. -/
theorem coeff_equivariant [Fintype (G ⧸ H)] (g : G) (F : G ⧸ H → M) :
    coeff H θ (indRep H ρ g F) = R H ρ θ g (coeff H θ F) := by
  simp only [coeff, indRep_apply, R, LinearMap.smul_apply, map_sum, map_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft (((g : G) : G ⧸ H))⁻¹) _ _ (fun δ => ?_)
  simp only [Equiv.coe_mulLeft]
  rw [smul_smul, ← Units.val_mul, mul_comm (θ _) (θ ((g : G) : G ⧸ H)), ← map_mul,
    mul_inv_cancel_left]

variable [Fintype (G ⧸ H)]

/-- The Shapiro cochain map: the untwisted transfer (trivial character) of `ι ∘ c` into the induced
module.  Explicitly `Sh(c)(g)(δ') = ρ(r_{δ'}) c(h-tuple at (g_0⋯g_{n-1})⁻¹ δ')`. -/
noncomputable def Sh (n : ℕ) (c : (Fin n → H) → M) : (Fin n → G) → (G ⧸ H → M) :=
  T H r hr (indRep H ρ) 1 n (fun x => iota H (c x))

omit [Fintype (G ⧸ H)] in
theorem R_trivial (g : G) : R H (indRep H ρ) (1 : G ⧸ H →* Aˣ) g = indRep H ρ g := by
  simp [R]

omit [Fintype (G ⧸ H)] in
theorem iota_equivariant (x : H) (m : M) :
    indRep H ρ (x : G) (iota H m) = iota H (ρ (x : G) m) := by
  classical
  funext δ
  have hx : ((x : G) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff _).mpr x.2
  rw [indRep_apply, hx, inv_one, one_mul, iota_apply, iota_apply]
  split_ifs <;> simp

omit [Fintype (G ⧸ H)] in
theorem iota_dInh (n : ℕ) (c : (Fin n → H) → M) :
    (fun x => iota H (dInh (fun (x : H) m => ρ (x : G) m) n c x)) =
      dInh (fun (x : H) F => indRep H ρ (x : G) F) n (fun x => iota H (c x)) := by
  funext x
  simp only [dInh, map_add, map_sum, map_zsmul, iota_equivariant]

/-- **The Shapiro map is a cochain map in every degree**, `PROVED`. -/
theorem shapiro_cochain_map (n : ℕ) (c : (Fin n → H) → M) (g : Fin (n + 1) → G) :
    dInh (fun x F => indRep H ρ x F) n (Sh H r hr ρ n c) g =
      Sh H r hr ρ (n + 1) (dInh (fun (x : H) m => ρ (x : G) m) n c) g := by
  have h := dT_eq_Td H r hr (indRep H ρ) (1 : G ⧸ H →* Aˣ) n (fun x => iota H (c x)) g
  simp only [R_trivial] at h
  rw [Sh, h, Sh, iota_dInh]

/-- **`𝒯_θ = (H20) ∘ Shapiro`** (tex 3202–3227 and 3237–3249: "under Shapiro, followed by the
equivariant coefficient map … the transferred cocycle is (H21)"), `PROVED` in every degree. -/
theorem coeff_shapiro_eq_transfer (n : ℕ) (c : (Fin n → H) → M) (g : Fin n → G) :
    coeff H θ (Sh H r hr ρ n c g) = T H r hr ρ θ n c g := by
  classical
  simp only [Sh, T, coeff, R_trivial, Finset.sum_apply, smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun δ _ => ?_
  set y : G ⧸ H := ((tprod n g : G) : G ⧸ H) * δ
  simp only [indRep_apply, hr, iota_apply]
  rw [Finset.sum_eq_single y]
  · simp [R, hr]
  · intro b _ hb
    rw [if_neg]
    · simp
    · intro h
      exact hb (inv_mul_eq_one.mp h).symm
  · simp

end TwistedTransfer

/-- **Node (H20)–(H21): Shapiro followed by the coefficient map**, tex 3202–3249, `PROVED`: for
every group `G`, normal subgroup `H` of finite index with a section `r` of `G → G/H`,
representation `ρ` on an `A`-module `M` and character `θ : G/H → Aˣ`, in every degree `n`:
the Shapiro map into the induced module is a cochain map, the coefficient map (H20) is
equivariant, and their composite is the twisted transfer (H21). -/
def ShapiroNode : Prop :=
  ∀ (G : Type) [Group G] (H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)] (r : G ⧸ H → G)
    (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (n : ℕ) (c : (Fin n → H) → M),
    (∀ g, TwistedTransfer.dInh (fun x F => TwistedTransfer.indRep H ρ x F) n
        (TwistedTransfer.Sh H r hr ρ n c) g =
      TwistedTransfer.Sh H r hr ρ (n + 1)
        (TwistedTransfer.dInh (fun (x : H) m => ρ (x : G) m) n c) g) ∧
    (∀ (g : G) (F : G ⧸ H → M), TwistedTransfer.coeff H θ (TwistedTransfer.indRep H ρ g F) =
      TwistedTransfer.R H ρ θ g (TwistedTransfer.coeff H θ F)) ∧
    (∀ g, TwistedTransfer.coeff H θ (TwistedTransfer.Sh H r hr ρ n c g) =
      TwistedTransfer.T H r hr ρ θ n c g)

theorem shapiroNode_proof : ShapiroNode := by
  intro G _ H _ _ r hr A M _ _ _ ρ θ n c
  exact ⟨TwistedTransfer.shapiro_cochain_map H r hr ρ n c,
    TwistedTransfer.coeff_equivariant H ρ θ,
    TwistedTransfer.coeff_shapiro_eq_transfer H r hr ρ θ n c⟩

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology
