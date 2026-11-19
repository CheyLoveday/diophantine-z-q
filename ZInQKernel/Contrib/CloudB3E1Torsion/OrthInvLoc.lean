import ZInQKernel.Contrib.CloudB3E1Torsion.ModTwo

/-!
# The orthogonal comparison inverse at the text's localization

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-paired-functional`,
tex 3704–3790 (in particular 3720, 3727–3732, 3736–3753, 3779–3781, 3787–3789).

Lane E2's `DualPres.OrthComparisonInverse` asks for the inverse of the orthogonal comparison
`c_T : C_{T⊥} → C'_T` at a finite stage, where it does not exist (`not_orthComparisonInverse_ecurve`).
The text inverts `c_T` only after a localization in which the full local complexes at the
places passing from zero to full are contracted by explicit homotopies. It writes them with
units `A = Φ − 1`, `D = Φ − N_q(g)` at active primes (tex 3727–3732) and `C = (inertia − 1) =
t · unit` at the moving prime (tex 3787–3789); no comparison is needed at unused primes (tex
3779–3781). This file states that input and proves the inverse from it.

* `LocHInv` (structure): a homotopy inverse of a morphism of local conditions `f : (U₁, ι₁) →
  (U₂, ι₂)` over the same local complex `L`. It consists of `g : U₂ → U₁`, a homotopy
  `H : U₂ → L[−1]` with `ι₁ g − ι₂ = −(dH + Hd)`, and homotopies `s₂, K₂` (resp. `s₁, K₁`) with
  `f g − 1 = d s₂ + s₂ d` and `H + ι₂ s₂ = −(dK₂ + K₂ d)` on cocycles (resp. `g f − 1`). All
  identities are stated in the degrees the `H¹` comparison reads.
* `LocContraction` (structure): `h¹ : L¹ → L⁰`, `h² : L² → L¹` with `h¹d⁰ = 1` and
  `d⁰h¹ + h²d¹ = 1`, the displayed contraction of a full local complex (tex 3727–3732, 3787–3789).
  **`LocContraction.toLocHInv`** (definition, PROVED fields): it inverts zero → full
  (`g = 0`, `H = h`, `s₂ = −h`).
* `LocHInv.id` (definition): the identity comparison.
* **`selHInvψ`** (definition) and **`selHInvψ_d0`**, **`selHInvψ_d1`**, **`selHInv_right`**,
  **`selHInv_left`** (PROVED): for a morphism of local conditions with a `LocHInv` at every
  place, `ψ(a, u, x) = (a, g u, x + H u)` commutes with the differential in degrees `0 → 1 → 2`.
  It is inverse to `condMap` on `H¹` from both sides.
* **`OrthComparisonInverseLoc`** (structure; named input for RC32, to be instantiated over a
  coefficient ring in which the units above are invertible, `Frac Λ`, or `𝒪[G]` after the inner
  limit): `φo` with a `LocHInv` at each old place, and a `LocContraction` at every new place.
  **`OrthComparisonInverseLoc.ψ`** with `hd`, `hd₁`, `hright`, `hleft` (PROVED): the fields of
  lane E2's `OrthComparisonInverse` other than `hsw`.
* `orthComparisonInverseLoc_of_isEmpty` (PROVED, non-vacuity): for no new places and `φo` the
  identity of the old conditions.

What the actual instance needs: at the places passing from zero to full, `h¹, h²` built from the
inverses of `A = Φ − 1`, `D = Φ − N_q(g)` (active primes) and `C = t · unit` (moving prime) in the
localized coefficients (tex 3727–3732, 3787–3789). Those inverses exist in `Frac Λ`, not at a
finite stage.

Remainder (not proved here): lane E2's `hsw` (`j ∘ ψ_{T ∪ {p}} ∘ i' = ψ_T`) does not hold on the
nose for this `ψ`. At the places above `p`, `ψ_T` keeps the unramified component `u`, while
`j ∘ ψ_{T ∪ {p}} ∘ i'` sends it to `0` and adds `h_p(ι u)` to the local component. They agree on
cocycles up to a coboundary, so `hlift_of_transport` needs its up-to-`d` variant.

Kinds: definitions, named input (`OrthComparisonInverseLoc`), PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex

universe u

/-! ### Homotopy inverses of local conditions -/

section Local

variable {k : Type u} [CommRing k] {L U₁ U₂ : GCx k}

/-- **A homotopy inverse of a morphism of local conditions** `f : (U₁, ι₁) → (U₂, ι₂)` over `L`,
in the degrees read by the `H¹` comparison. Kind: definition (structure). -/
structure LocHInv (ι₁ : GHom U₁ L) (ι₂ : GHom U₂ L) (f : GHom U₁ U₂) where
  /-- the inverse -/
  g : GHom U₂ U₁
  /-- the homotopy of the condition maps, `U₂ → L[−1]`, in degrees `0, 1, 2` -/
  H0 : U₂.X 0 →ₗ[k] L.X (-1)
  H1 : U₂.X 1 →ₗ[k] L.X 0
  H2 : U₂.X 2 →ₗ[k] L.X 1
  /-- `ι₁ g − ι₂ = −(dH + Hd)` in degree `0` -/
  hH0 : ∀ x : U₂.X 0, ι₁.f 0 0 rfl (g.f 0 0 rfl x) - ι₂.f 0 0 rfl x =
    -(L.d (-1) 0 rfl (H0 x) + H1 (U₂.d 0 1 rfl x))
  /-- `ι₁ g − ι₂ = −(dH + Hd)` in degree `1` -/
  hH1 : ∀ x : U₂.X 1, ι₁.f 1 1 rfl (g.f 1 1 rfl x) - ι₂.f 1 1 rfl x =
    -(L.d 0 1 rfl (H1 x) + H2 (U₂.d 1 2 rfl x))
  /-- the homotopy `f g ≃ 1` in degree `1` -/
  s₂ : U₂.X 1 →ₗ[k] U₂.X 0
  /-- `f g − 1 = d s₂` on cocycles -/
  hs₂ : ∀ x : U₂.X 1, U₂.d 1 2 rfl x = 0 → f.f 1 1 rfl (g.f 1 1 rfl x) - x = U₂.d 0 1 rfl (s₂ x)
  /-- the coherence homotopy `U₂¹ → L⁻¹` -/
  K₂ : U₂.X 1 →ₗ[k] L.X (-1)
  /-- `H + ι₂ s₂ = −d K₂` on cocycles -/
  hK₂ : ∀ x : U₂.X 1, U₂.d 1 2 rfl x = 0 → H1 x + ι₂.f 0 0 rfl (s₂ x) = -L.d (-1) 0 rfl (K₂ x)
  /-- the homotopy `g f ≃ 1` in degree `1` -/
  s₁ : U₁.X 1 →ₗ[k] U₁.X 0
  /-- `g f − 1 = d s₁` on cocycles -/
  hs₁ : ∀ x : U₁.X 1, U₁.d 1 2 rfl x = 0 → g.f 1 1 rfl (f.f 1 1 rfl x) - x = U₁.d 0 1 rfl (s₁ x)
  /-- the coherence homotopy `U₁¹ → L⁻¹` -/
  K₁ : U₁.X 1 →ₗ[k] L.X (-1)
  /-- `H f + ι₁ s₁ = −d K₁` on cocycles -/
  hK₁ : ∀ x : U₁.X 1, U₁.d 1 2 rfl x = 0 →
    H1 (f.f 1 1 rfl x) + ι₁.f 0 0 rfl (s₁ x) = -L.d (-1) 0 rfl (K₁ x)

/-- **A contraction of a full local complex in low degrees** (tex 3727–3732, 3787–3789):
`h¹ : L¹ → L⁰`, `h² : L² → L¹` with `h¹d⁰ = 1` and `d⁰h¹ + h²d¹ = 1`. Kind: definition
(structure). -/
structure LocContraction (L : GCx k) where
  /-- `h¹` -/
  h1 : L.X 1 →ₗ[k] L.X 0
  /-- `h²` -/
  h2 : L.X 2 →ₗ[k] L.X 1
  /-- `h¹ d⁰ = 1` -/
  hc0 : ∀ x : L.X 0, h1 (L.d 0 1 rfl x) = x
  /-- `d⁰ h¹ + h² d¹ = 1` -/
  hc1 : ∀ x : L.X 1, L.d 0 1 rfl (h1 x) + h2 (L.d 1 2 rfl x) = x

open ZInQ.Contrib.CloudB3RC53.SelmerDuality (idGHom zeroGHom)
open ZInQ.Manuscript.RC.SelmerComplex (zeroCx)

/-- **A contraction inverts zero → full** (PROVED fields): `g = 0`, `H = h`, `s₂ = −h¹`.
Kind: definition. -/
def LocContraction.toLocHInv (c : LocContraction L) :
    LocHInv (zeroGHom (zeroCx k) L) (idGHom L) (zeroGHom (zeroCx k) L) where
  g := zeroGHom L (zeroCx k)
  H0 := 0
  H1 := c.h1
  H2 := c.h2
  hH0 x := by
    change (0 : L.X 0) - x = -(L.d (-1) 0 rfl 0 + c.h1 (L.d 0 1 rfl x))
    rw [map_zero, zero_add, c.hc0, zero_sub]
  hH1 x := by
    change (0 : L.X 1) - x = -(L.d 0 1 rfl (c.h1 x) + c.h2 (L.d 1 2 rfl x))
    rw [c.hc1, zero_sub]
  s₂ := -c.h1
  hs₂ x hx := by
    change (0 : L.X 1) - x = L.d 0 1 rfl (-c.h1 x)
    have := c.hc1 x
    rw [hx, map_zero, add_zero] at this
    rw [map_neg, this, zero_sub]
  K₂ := 0
  hK₂ x _ := by
    change c.h1 x + (-c.h1 x) = -L.d (-1) 0 rfl 0
    rw [add_neg_cancel, map_zero, neg_zero]
  s₁ := 0
  hs₁ _ _ := Subsingleton.elim (α := PUnit) _ _
  K₁ := 0
  hK₁ x _ := by
    change c.h1 0 + 0 = -L.d (-1) 0 rfl 0
    rw [map_zero, map_zero, add_zero, neg_zero]

/-- **The identity comparison** (PROVED fields). Kind: definition. -/
def LocHInv.id (ι : GHom U₁ L) : LocHInv ι ι (idGHom U₁) where
  g := idGHom U₁
  H0 := 0
  H1 := 0
  H2 := 0
  hH0 x := by
    change ι.f 0 0 rfl x - ι.f 0 0 rfl x = -(L.d (-1) 0 rfl 0 + 0)
    rw [sub_self, map_zero, add_zero, neg_zero]
  hH1 x := by
    change ι.f 1 1 rfl x - ι.f 1 1 rfl x = -(L.d 0 1 rfl 0 + 0)
    rw [sub_self, map_zero, add_zero, neg_zero]
  s₂ := 0
  hs₂ x _ := by
    change x - x = U₁.d 0 1 rfl 0
    rw [sub_self, map_zero]
  K₂ := 0
  hK₂ x _ := by
    change (0 : L.X 0) + ι.f 0 0 rfl 0 = -L.d (-1) 0 rfl 0
    rw [map_zero, map_zero, add_zero, neg_zero]
  s₁ := 0
  hs₁ x _ := by
    change x - x = U₁.d 0 1 rfl 0
    rw [sub_self, map_zero]
  K₁ := 0
  hK₁ x _ := by
    change (0 : L.X 0) + ι.f 0 0 rfl 0 = -L.d (-1) 0 rfl 0
    rw [map_zero, map_zero, add_zero, neg_zero]

end Local

/-! ### The inverse on Selmer complexes -/

section Sel

variable {k : Type u} [CommRing k] {GS : Type u} [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS] {ι : Type u} {Gv : ι → Type u} [∀ v, Group (Gv v)]
  [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  {Δ₁ Δ₂ : LocalConditions k GS Gv loc M} {F : ∀ v, GHom (Δ₁.U v) (Δ₂.U v)}
  (I : ∀ v, LocHInv (Δ₁.i v) (Δ₂.i v) (F v))

/-- `g` on the product of the conditions. Kind: definition. -/
abbrev gU (n : ℤ) : (selData k GS Gv loc M Δ₂).U.X n →ₗ[k] (selData k GS Gv loc M Δ₁).U.X n :=
  (piMap fun v => (I v).g).f n n rfl

/-- `H` on the product, degree `0`. Kind: definition. -/
def HU0 : (selData k GS Gv loc M Δ₂).U.X 0 →ₗ[k] (selData k GS Gv loc M Δ₂).L.X (0 - 1) :=
  (LinearMap.pi fun v => (I v).H0.comp (LinearMap.proj v) :
    (piCx Δ₂.U).X 0 →ₗ[k] ∀ v, (localCx k GS Gv loc M v).X (-1))

/-- `H` on the product, degree `1`. Kind: definition. -/
def HU1 : (selData k GS Gv loc M Δ₂).U.X 1 →ₗ[k] (selData k GS Gv loc M Δ₂).L.X (1 - 1) :=
  (LinearMap.pi fun v => (I v).H1.comp (LinearMap.proj v) :
    (piCx Δ₂.U).X 1 →ₗ[k] ∀ v, (localCx k GS Gv loc M v).X (0))

/-- `H` on the product, degree `2`. Kind: definition. -/
def HU2 : (selData k GS Gv loc M Δ₂).U.X 2 →ₗ[k] (selData k GS Gv loc M Δ₂).L.X (2 - 1) :=
  (LinearMap.pi fun v => (I v).H2.comp (LinearMap.proj v) :
    (piCx Δ₂.U).X 2 →ₗ[k] ∀ v, (localCx k GS Gv loc M v).X (1))

/-- **`ψ(a, u, x) = (a, g u, x + H u)`**, degree `0`. Kind: definition. -/
def ψ0 : (selCx (selData k GS Gv loc M Δ₂)).X 0 →ₗ[k] (selCx (selData k GS Gv loc M Δ₁)).X 0 where
  toFun c := show selT (selData k GS Gv loc M Δ₁) 0 from
    ((c : selT (selData k GS Gv loc M Δ₂) 0).1, gU I 0 (c : selT (selData k GS Gv loc M Δ₂) 0).2.1,
      (c : selT (selData k GS Gv loc M Δ₂) 0).2.2 + HU0 I (c : selT (selData k GS Gv loc M Δ₂) 0).2.1)
  map_add' c c' := by
    obtain ⟨a, u, x⟩ := c
    obtain ⟨a', u', x'⟩ := c'
    refine Prod.ext rfl (Prod.ext (map_add _ _ _) ?_)
    change (x + x') + HU0 I (u + u') = (x + HU0 I u) + (x' + HU0 I u')
    rw [map_add]
    abel
  map_smul' r c := by
    obtain ⟨a, u, x⟩ := c
    refine Prod.ext rfl (Prod.ext (map_smul _ _ _) ?_)
    change r • x + HU0 I (r • u) = r • (x + HU0 I u)
    rw [map_smul, smul_add]

/-- `ψ`, degree `1`. Kind: definition. -/
def ψ1 : (selCx (selData k GS Gv loc M Δ₂)).X 1 →ₗ[k] (selCx (selData k GS Gv loc M Δ₁)).X 1 where
  toFun c := show selT (selData k GS Gv loc M Δ₁) 1 from
    ((c : selT (selData k GS Gv loc M Δ₂) 1).1, gU I 1 (c : selT (selData k GS Gv loc M Δ₂) 1).2.1,
      (c : selT (selData k GS Gv loc M Δ₂) 1).2.2 + HU1 I (c : selT (selData k GS Gv loc M Δ₂) 1).2.1)
  map_add' c c' := by
    obtain ⟨a, u, x⟩ := c
    obtain ⟨a', u', x'⟩ := c'
    refine Prod.ext rfl (Prod.ext (map_add _ _ _) ?_)
    change (x + x') + HU1 I (u + u') = (x + HU1 I u) + (x' + HU1 I u')
    rw [map_add]
    abel
  map_smul' r c := by
    obtain ⟨a, u, x⟩ := c
    refine Prod.ext rfl (Prod.ext (map_smul _ _ _) ?_)
    change r • x + HU1 I (r • u) = r • (x + HU1 I u)
    rw [map_smul, smul_add]

/-- `ψ`, degree `2`. Kind: definition. -/
def ψ2 : (selCx (selData k GS Gv loc M Δ₂)).X 2 →ₗ[k] (selCx (selData k GS Gv loc M Δ₁)).X 2 where
  toFun c := show selT (selData k GS Gv loc M Δ₁) 2 from
    ((c : selT (selData k GS Gv loc M Δ₂) 2).1, gU I 2 (c : selT (selData k GS Gv loc M Δ₂) 2).2.1,
      (c : selT (selData k GS Gv loc M Δ₂) 2).2.2 + HU2 I (c : selT (selData k GS Gv loc M Δ₂) 2).2.1)
  map_add' c c' := by
    obtain ⟨a, u, x⟩ := c
    obtain ⟨a', u', x'⟩ := c'
    refine Prod.ext rfl (Prod.ext (map_add _ _ _) ?_)
    change (x + x') + HU2 I (u + u') = (x + HU2 I u) + (x' + HU2 I u')
    rw [map_add]
    abel
  map_smul' r c := by
    obtain ⟨a, u, x⟩ := c
    refine Prod.ext rfl (Prod.ext (map_smul _ _ _) ?_)
    change r • x + HU2 I (r • u) = r • (x + HU2 I u)
    rw [map_smul, smul_add]

/-- **`ψ` commutes with `d` in degree `0`.** Kind: PROVED. -/
theorem ψ_d0 (x : (selCx (selData k GS Gv loc M Δ₂)).X 0) :
    ψ1 I ((selCx (selData k GS Gv loc M Δ₂)).d 0 1 rfl x) =
      (selCx (selData k GS Gv loc M Δ₁)).d 0 1 rfl (ψ0 I x) := by
  obtain ⟨a, u, w⟩ := x
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext v
    exact ((I v).g.comm 0 1 0 1 rfl rfl rfl rfl (u v))
  · funext v
    change (resS k GS Gv loc M).f 0 0 rfl a v - (Δ₂.i v).f 0 0 rfl (u v) -
        (localCx k GS Gv loc M v).d (-1) 0 rfl (show (localCx k GS Gv loc M v).X (-1) from w v) +
          (I v).H1 ((Δ₂.U v).d 0 1 rfl (u v)) =
      (resS k GS Gv loc M).f 0 0 rfl a v - (Δ₁.i v).f 0 0 rfl ((I v).g.f 0 0 rfl (u v)) -
        (localCx k GS Gv loc M v).d (-1) 0 rfl
          ((show (localCx k GS Gv loc M v).X (-1) from w v) + (I v).H0 (u v))
    have h := (I v).hH0 (u v)
    rw [map_add, sub_eq_iff_eq_add.mp h]
    abel

/-- **`ψ` commutes with `d` in degree `1`.** Kind: PROVED. -/
theorem ψ_d1 (x : (selCx (selData k GS Gv loc M Δ₂)).X 1) :
    ψ2 I ((selCx (selData k GS Gv loc M Δ₂)).d 1 2 rfl x) =
      (selCx (selData k GS Gv loc M Δ₁)).d 1 2 rfl (ψ1 I x) := by
  obtain ⟨a, u, w⟩ := x
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext v
    exact ((I v).g.comm 1 2 1 2 rfl rfl rfl rfl (u v))
  · funext v
    change (resS k GS Gv loc M).f 1 1 rfl a v - (Δ₂.i v).f 1 1 rfl (u v) -
        (localCx k GS Gv loc M v).d 0 1 rfl (show (localCx k GS Gv loc M v).X 0 from w v) +
          (I v).H2 ((Δ₂.U v).d 1 2 rfl (u v)) =
      (resS k GS Gv loc M).f 1 1 rfl a v - (Δ₁.i v).f 1 1 rfl ((I v).g.f 1 1 rfl (u v)) -
        (localCx k GS Gv loc M v).d 0 1 rfl
          ((show (localCx k GS Gv loc M v).X 0 from w v) + (I v).H1 (u v))
    have h := (I v).hH1 (u v)
    rw [map_add, sub_eq_iff_eq_add.mp h]
    abel

variable (hF : ∀ v (i : ℤ) (u : (Δ₁.U v).X i),
  (Δ₂.i v).f i i rfl ((F v).f i i rfl u) = (Δ₁.i v).f i i rfl u)

/-- **`c ∘ ψ = 1` on `H¹`** (PROVED): every degree-one cocycle `x` of `C₂` satisfies
`c(ψ x) = x + d y`. -/
theorem selHInv_right (x : (selCx (selData k GS Gv loc M Δ₂)).X 1)
    (hx : (selCx (selData k GS Gv loc M Δ₂)).d 1 2 rfl x = 0) :
    ∃ y : (selCx (selData k GS Gv loc M Δ₂)).X 0,
      (condMap Δ₁ Δ₂ F hF).f 1 1 rfl (ψ1 I x) = x + (selCx (selData k GS Gv loc M Δ₂)).d 0 1 rfl y := by
  obtain ⟨a, u, w⟩ := x
  have hu : ∀ v, (Δ₂.U v).d 1 2 rfl (u v) = 0 := fun v =>
    congrFun (congrArg (fun c : selT (selData k GS Gv loc M Δ₂) 2 => c.2.1) hx) v
  refine ⟨((0, fun v => (I v).s₂ (u v), fun v => (I v).K₂ (u v)) :
    selT (selData k GS Gv loc M Δ₂) 0), Prod.ext ?_ (Prod.ext ?_ ?_)⟩
  · change a = a + (selData k GS Gv loc M Δ₂).G.d 0 1 rfl 0
    rw [map_zero, add_zero]
  · funext v
    change (F v).f 1 1 rfl ((I v).g.f 1 1 rfl (u v)) = u v + (Δ₂.U v).d 0 1 rfl ((I v).s₂ (u v))
    rw [← (I v).hs₂ (u v) (hu v), add_sub_cancel]
  · funext v
    change (show (localCx k GS Gv loc M v).X 0 from w v) + (I v).H1 (u v) =
      (show (localCx k GS Gv loc M v).X 0 from w v) + ((resS k GS Gv loc M).f 0 0 rfl 0 v -
        (Δ₂.i v).f 0 0 rfl ((I v).s₂ (u v)) - (localCx k GS Gv loc M v).d (-1) 0 rfl ((I v).K₂ (u v)))
    have h := (I v).hK₂ (u v) (hu v)
    rw [map_zero]
    change _ = _ + ((0 : (localCx k GS Gv loc M v).X 0) - _ - _)
    rw [neg_eq_iff_eq_neg.mp h.symm]
    abel

/-- **`ψ ∘ c = 1` on `H¹`** (PROVED): every degree-one cocycle `z` of `C₁` satisfies
`ψ(c z) = z + d y`. -/
theorem selHInv_left (z : (selCx (selData k GS Gv loc M Δ₁)).X 1)
    (hz : (selCx (selData k GS Gv loc M Δ₁)).d 1 2 rfl z = 0) :
    ∃ y : (selCx (selData k GS Gv loc M Δ₁)).X 0,
      ψ1 I ((condMap Δ₁ Δ₂ F hF).f 1 1 rfl z) = z + (selCx (selData k GS Gv loc M Δ₁)).d 0 1 rfl y := by
  obtain ⟨a, u, w⟩ := z
  have hu : ∀ v, (Δ₁.U v).d 1 2 rfl (u v) = 0 := fun v =>
    congrFun (congrArg (fun c : selT (selData k GS Gv loc M Δ₁) 2 => c.2.1) hz) v
  refine ⟨((0, fun v => (I v).s₁ (u v), fun v => (I v).K₁ (u v)) :
    selT (selData k GS Gv loc M Δ₁) 0), Prod.ext ?_ (Prod.ext ?_ ?_)⟩
  · change a = a + (selData k GS Gv loc M Δ₁).G.d 0 1 rfl 0
    rw [map_zero, add_zero]
  · funext v
    change (I v).g.f 1 1 rfl ((F v).f 1 1 rfl (u v)) = u v + (Δ₁.U v).d 0 1 rfl ((I v).s₁ (u v))
    rw [← (I v).hs₁ (u v) (hu v), add_sub_cancel]
  · funext v
    change (show (localCx k GS Gv loc M v).X 0 from w v) + (I v).H1 ((F v).f 1 1 rfl (u v)) =
      (show (localCx k GS Gv loc M v).X 0 from w v) + ((resS k GS Gv loc M).f 0 0 rfl 0 v -
        (Δ₁.i v).f 0 0 rfl ((I v).s₁ (u v)) - (localCx k GS Gv loc M v).d (-1) 0 rfl ((I v).K₁ (u v)))
    have h := (I v).hK₁ (u v) (hu v)
    rw [map_zero]
    change _ = _ + ((0 : (localCx k GS Gv loc M v).X 0) - _ - _)
    rw [neg_eq_iff_eq_neg.mp h.symm]
    abel

end Sel

end ZInQ.Contrib.CloudB3E1Torsion
