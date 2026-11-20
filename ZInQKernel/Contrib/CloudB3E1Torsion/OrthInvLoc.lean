import ZInQKernel.Contrib.CloudB3E1Torsion.ModTwo

/-!
# The orthogonal comparison inverse at the text's localization

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-paired-functional`,
tex 3704–3790 (in particular 3720, 3727–3732, 3736–3753, 3779–3781, 3787–3789).

Lane E2's `DualPres.OrthComparisonInverse` asks for the inverse of the orthogonal comparison
`c_T : C_{T⊥} → C'_T` at a finite stage,
where it does not exist (`not_orthComparisonInverse_ecurve`).
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
* `UrSurj` (named input: `Φ − 1` onto the unramified condition at the new places),
  `newPlace_switch`, `place_switch`, **`hswUpToD_of_urSurj`**, **`hlift_of_urSurj`** (PROVED):
  the switch compatibility up to coboundaries, and the paired strict lift, from `UrSurj`.
* `HswUpToD` and **`hlift_of_transport_loc`** (PROVED): the bridge. Lane E2's
  `hlift_of_transport` holds with the switch compatibility up to coboundaries on cocycles, and
  its conclusion holds up to a coboundary of `C_{T⊥}`.
* `orthComparisonInverseLoc_of_isEmpty` (PROVED, non-vacuity): for no new places and `φo` the
  identity of the old conditions (`LocHInv.id`). A non-degenerate instance needs the localized
  coefficients.

What the actual instance needs: at the places passing from zero to full, `h¹, h²` built from the
inverses of `A = Φ − 1`, `D = Φ − N_q(g)` (active primes) and `C = t · unit` (moving prime) in the
localized coefficients (tex 3727–3732, 3787–3789). Those inverses exist in `Frac Λ`, not at a
finite stage.

The bridge to `hlift_of_transport`: lane E2's `hsw`
(`j ∘ ψ_{T ∪ {p}} ∘ i' = ψ_T`) does not hold on the nose for this `ψ`. At the places above `p`,
`ψ_T` keeps the unramified component `u_p`, while `j ∘ ψ_{T ∪ {p}} ∘ i'` sends it to `0` and adds
`h¹_p(ι u_p)` to the local component. The difference `(0, −u_p, h¹_p(ι u_p))` is a coboundary of
`C_{T⊥}` exactly when `u_p ∈ (Φ − 1)W` up to the contraction. That holds once the unramified
condition `[W --(Φ−1)--> W]` at `p` is contracted too, which is the unit `A = Φ − 1` of tex
3727–3732. So the bridge goes through `HswUpToD`, which is PROVED from `UrSurj` (`Φ − 1` onto the
unramified condition at the new places, the unit `A` of tex 3727–3732):
`hswUpToD_of_urSurj`, `hlift_of_urSurj`.

Remaining named inputs, both localized (true at the text's localization, false at a finite
stage): `OrthComparisonInverseLoc` (the contractions) and `UrSurj` (`Φ − 1` onto). Passing to
`Frac Λ` gives them once `det(Φ − 1) ≠ 0` and the units `D`, `C` are invertible there (tex
3727–3732, 3787–3789); that arithmetic input is RC32's.

Kinds: definitions, named inputs (`OrthComparisonInverseLoc`, `UrSurj`), PROVED.
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
      (c : selT (selData k GS Gv loc M Δ₂) 0).2.2 +
        HU0 I (c : selT (selData k GS Gv loc M Δ₂) 0).2.1)
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
      (c : selT (selData k GS Gv loc M Δ₂) 1).2.2 +
        HU1 I (c : selT (selData k GS Gv loc M Δ₂) 1).2.1)
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
      (c : selT (selData k GS Gv loc M Δ₂) 2).2.2 +
        HU2 I (c : selT (selData k GS Gv loc M Δ₂) 2).2.1)
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
      (condMap Δ₁ Δ₂ F hF).f 1 1 rfl (ψ1 I x) =
        x + (selCx (selData k GS Gv loc M Δ₂)).d 0 1 rfl y := by
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
        (Δ₂.i v).f 0 0 rfl ((I v).s₂ (u v)) -
          (localCx k GS Gv loc M v).d (-1) 0 rfl ((I v).K₂ (u v)))
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
      ψ1 I ((condMap Δ₁ Δ₂ F hF).f 1 1 rfl z) =
        z + (selCx (selData k GS Gv loc M Δ₁)).d 0 1 rfl y := by
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
        (Δ₁.i v).f 0 0 rfl ((I v).s₁ (u v)) -
          (localCx k GS Gv loc M v).d (-1) 0 rfl ((I v).K₁ (u v)))
    have h := (I v).hK₁ (u v) (hu v)
    rw [map_zero]
    change _ = _ + ((0 : (localCx k GS Gv loc M v).X 0) - _ - _)
    rw [neg_eq_iff_eq_neg.mp h.symm]
    abel

end Sel

/-! ### The localized input for lane E2's presentation -/

section Pres

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3E2.DualPres
open ZInQ.Manuscript.RC.Limits (SplitInclusion)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (idGHom zeroGHom)

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ' Δ'' : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M)
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)))

/-- **The orthogonal comparison inverse at the localization** (named input for lane RC32;
tex 3704–3790): the old-place comparison `φo` with a homotopy inverse at every old place, and the
displayed contraction of the full local complex at every new place (built in the localized
coefficients from the units `A = Φ − 1`, `D = Φ − N_q(g)` at active primes, tex 3727–3732, and
`C = t · unit` at the moving prime, tex 3787–3789). Kind: definition (named input). -/
structure OrthComparisonInverseLoc where
  /-- the comparison of the old orthogonal conditions with the transported ones -/
  φo : ∀ v₀ : Places K S₀, GHom (Δ'.U v₀) (Δ''.U v₀)
  /-- it is compatible with the maps to the local complexes -/
  φo_compat : ∀ v₀ (n : ℤ) (x : (Δ'.U v₀).X n),
    (Δ''.i v₀).f n n rfl ((φo v₀).f n n rfl x) = (Δ'.i v₀).f n n rfl x
  /-- a homotopy inverse at every old place -/
  φoInv : ∀ v₀, LocHInv (Δ'.i v₀) (Δ''.i v₀) (φo v₀)
  /-- the contraction of the full local complex at every new place -/
  ctr : ∀ j, LocContraction (genuineLq K S k M (place j))

variable {K S₀ S k M Δ' Δ'' place X EU}

/-- The homotopy inverse at a new place: the contraction (zero → full) or the identity.
Kind: definition. -/
def newInv {j : ι × Bool} (c : LocContraction (genuineLq K S k M (place j))) : (b : Bool) →
    LocHInv (dcondιS K S k M place X EU j b) (condιS K S k M place X EU j b)
      (dcomp K S k M place X j b)
  | true => c.toLocHInv
  | false => LocHInv.id _

/-- The homotopy inverses at every place of the presentation. Kind: definition. -/
def presInv (Ψ : OrthComparisonInverseLoc K S₀ S k M Δ' Δ'' place) (T : Finset ι) :
    ∀ v : Places K S₀ ⊕ (ι × Bool), LocHInv ((dpresCondS K S₀ S k M Δ' place X EU T).i v)
      ((presCondS K S₀ S k M Δ'' place X EU T).i v)
      (presComparison K S₀ S k M Δ' Δ'' place X EU Ψ.φo T v)
  | .inl v₀ => Ψ.φoInv v₀
  | .inr j => newInv (Ψ.ctr j) (decide (j.1 ∈ T))

/-- **`Φ − 1` is onto the unramified condition at every new place** (the unit `A = Φ − 1` of
tex 3727–3732, at the localization). Kind: definition (named input). -/
def UrSurj : Prop :=
  ∀ j (y : (genuineUq K S k (place j) (X j)).X 1),
    ∃ w, (genuineUq K S k (place j) (X j)).d 0 1 rfl w = y

omit [DecidableEq ι] in
/-- **The switch at one new place** (PROVED): the per-place components of
`j ∘ ψ_{T ∪ {p}} ∘ i' − ψ_T` are those of a coboundary. -/
theorem newPlace_switch (c : LocContraction (genuineLq K S k M (place j))) (b b' : Bool)
    (h : b = true → b' = true)
    (hsurj : ∀ y : (genuineUq K S k (place j) (X j)).X 1,
      ∃ w, (genuineUq K S k (place j) (X j)).d 0 1 rfl w = y)
    (u : (condCxS K S k M place X j b).X 1) :
    ∃ w : (dcondCxS K S k place X j b).X 0,
      (dcondSplit K S k place X j b b' h).f 1 1 rfl ((newInv (EU := EU) c b').g.f 1 1 rfl
          ((condSplitS K S k M place X EU j b b' h).i.f 1 1 rfl u)) =
        (newInv (EU := EU) c b).g.f 1 1 rfl u + (dcondCxS K S k place X j b).d 0 1 rfl w ∧
      (newInv (EU := EU) c b').H1 ((condSplitS K S k M place X EU j b b' h).i.f 1 1 rfl u) =
        (newInv (EU := EU) c b).H1 u - (dcondιS K S k M place X EU j b).f 0 0 rfl w := by
  cases b <;> cases b'
  · refine ⟨0, ?_, ?_⟩
    · rw [map_zero, add_zero]; rfl
    · rw [map_zero, sub_zero]; rfl
  · obtain ⟨w₀, hw₀⟩ := hsurj u
    refine ⟨-w₀, ?_, ?_⟩
    · change (0 : (dcondCxS K S k place X j false).X 1) =
        (show (genuineUq K S k (place j) (X j)).X 1 from u) +
          (genuineUq K S k (place j) (X j)).d 0 1 rfl (-w₀)
      rw [map_neg, hw₀, add_neg_cancel]
      rfl
    · change c.h1 ((EU j).i.f 1 1 rfl u) = (0 : (genuineLq K S k M (place j)).X 0) -
        (EU j).i.f 0 0 rfl (-w₀)
      rw [← hw₀, (EU j).i.comm 0 1 0 1 rfl rfl rfl rfl w₀, c.hc0, map_neg, zero_sub, neg_neg]
  · exact absurd (h rfl) (by decide)
  · refine ⟨0, ?_, ?_⟩
    · rw [map_zero, add_zero]; rfl
    · rw [map_zero, sub_zero]; rfl

namespace OrthComparisonInverseLoc

variable (Ψ : OrthComparisonInverseLoc K S₀ S k M Δ' Δ'' place)

/-- **The inverse `ψ_T : C'_T → C_{T⊥}`** in degree `1`. Kind: definition. -/
def ψ (T : Finset ι) : (suppCxS K S₀ S k M Δ'' place X EU T).X 1 →ₗ[k]
    (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).X 1 :=
  ψ1 (presInv (EU := EU) Ψ T)

/-- **`ψ_T` commutes with the differential** in degree `0` (PROVED). -/
theorem hd (T : Finset ι) (x : (suppCxS K S₀ S k M Δ'' place X EU T).X 0) :
    Ψ.ψ (X := X) (EU := EU) T ((suppCxS K S₀ S k M Δ'' place X EU T).d 0 1 rfl x) =
      (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 0 1 rfl (ψ0 (presInv Ψ T) x) :=
  ψ_d0 (presInv Ψ T) x

/-- **`ψ_T` commutes with the differential** in degree `1` (PROVED). -/
theorem hd₁ (T : Finset ι) (x : (suppCxS K S₀ S k M Δ'' place X EU T).X 1) :
    ψ2 (presInv (EU := EU) Ψ T) ((suppCxS K S₀ S k M Δ'' place X EU T).d 1 2 rfl x) =
      (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 1 2 rfl (Ψ.ψ (X := X) (EU := EU) T x) :=
  ψ_d1 (presInv Ψ T) x

/-- **`c_T ∘ ψ_T = 1` on `H¹`** (PROVED). -/
theorem hright (T : Finset ι) (x : (suppCxS K S₀ S k M Δ'' place X EU T).X 1)
    (hx : (suppCxS K S₀ S k M Δ'' place X EU T).d 1 2 rfl x = 0) :
    ∃ y : (suppCxS K S₀ S k M Δ'' place X EU T).X 0,
      (orthComparison K S₀ S k M Δ' Δ'' place X EU Ψ.φo Ψ.φo_compat T).f 1 1 rfl
        (Ψ.ψ (X := X) (EU := EU) T x) =
        x + (suppCxS K S₀ S k M Δ'' place X EU T).d 0 1 rfl y :=
  selHInv_right (presInv Ψ T)
    (presComparison_compat K S₀ S k M Δ' Δ'' place X EU Ψ.φo Ψ.φo_compat T) x hx

/-- **`ψ_T ∘ c_T = 1` on `H¹`** (PROVED). -/
theorem hleft (T : Finset ι) (z : (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).X 1)
    (hz : (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 1 2 rfl z = 0) :
    ∃ y : (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).X 0,
      Ψ.ψ (X := X) (EU := EU) T
        ((orthComparison K S₀ S k M Δ' Δ'' place X EU Ψ.φo Ψ.φo_compat T).f 1 1 rfl z) =
        z + (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 0 1 rfl y :=
  selHInv_left (presInv Ψ T)
    (presComparison_compat K S₀ S k M Δ' Δ'' place X EU Ψ.φo Ψ.φo_compat T) z hz

/-- **The switch compatibility up to coboundaries** (the remainder; see the module docstring):
for `p ∉ T` and a degree-one cocycle `x` of `C'_T`, `j(ψ_{T ∪ {p}}(i' x)) = ψ_T x + d b`.
Kind: definition (named input). -/
def HswUpToD : Prop :=
  ∀ (T : Finset ι) (p : ι), p ∉ T → ∀ x : (suppCxS K S₀ S k M Δ'' place X EU T).X 1,
    (suppCxS K S₀ S k M Δ'' place X EU T).d 1 2 rfl x = 0 →
      ∃ b : (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).X 0,
        jmap T p 1 (Ψ.ψ (X := X) (EU := EU) (insert p T)
            ((suppInclS K S₀ S k M Δ'' place X EU T p).f 1 1 rfl x)) =
          Ψ.ψ (X := X) (EU := EU) T x + (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 0 1 rfl b

/-- **The switch at every place** (PROVED, from `UrSurj`). -/
theorem place_switch (hsurj : UrSurj (K := K) (S := S) (k := k) (place := place) (X := X))
    (T : Finset ι) (p : ι) (v : Places K S₀ ⊕ (ι × Bool))
    (y : ((presCondS K S₀ S k M Δ'' place X EU T).U v).X 1) :
    ∃ w : ((dpresCondS K S₀ S k M Δ' place X EU T).U v).X 0,
      (dpresSplit K S₀ S k M Δ' place X EU T p v).f 1 1 rfl
          ((presInv (EU := EU) Ψ (insert p T) v).g.f 1 1 rfl
            ((presSplitS K S₀ S k M Δ'' place X EU T p v).i.f 1 1 rfl y)) =
        (presInv (EU := EU) Ψ T v).g.f 1 1 rfl y +
          ((dpresCondS K S₀ S k M Δ' place X EU T).U v).d 0 1 rfl w ∧
      (presInv (EU := EU) Ψ (insert p T) v).H1
          ((presSplitS K S₀ S k M Δ'' place X EU T p v).i.f 1 1 rfl y) =
        (presInv (EU := EU) Ψ T v).H1 y -
          ((dpresCondS K S₀ S k M Δ' place X EU T).i v).f 0 0 rfl w := by
  match v with
  | .inl v₀ =>
    refine ⟨0, ?_, ?_⟩
    · rw [map_zero, add_zero]; rfl
    · rw [map_zero, sub_zero]; rfl
  | .inr j =>
    exact newPlace_switch (Ψ.ctr j) _ _ _ (hsurj j) y

/-- **The paired strict lift at the localization** (PROVED from `HswUpToD`; tex 4169–4171): from
the transported norm identity `z'_R = e · i'(z'_P) + d b'` with `z'_P` a cocycle, the lift
`j z_S = e z_{P⊥} + d b` for `z_S = ψ_{T ∪ {p}}(z'_R)`, `z_{P⊥} = ψ_T(z'_P)`: lane E2's
`hlift_of_transport` with `hsw` up to coboundaries. -/
theorem hlift_of_transport_loc (hsw : Ψ.HswUpToD (X := X) (EU := EU)) {T : Finset ι} {p : ι}
    (hp : p ∉ T) (zR : (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).X 1)
    (zP : (suppCxS K S₀ S k M Δ'' place X EU T).X 1)
    (hzP : (suppCxS K S₀ S k M Δ'' place X EU T).d 1 2 rfl zP = 0) (e : k)
    (b' : (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).X 0)
    (hnorm : zR = e • (suppInclS K S₀ S k M Δ'' place X EU T p).f 1 1 rfl zP +
      (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).d 0 1 rfl b') :
    ∃ b : (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).X 0,
      jmap T p 1 (Ψ.ψ (X := X) (EU := EU) (insert p T) zR) =
        e • Ψ.ψ (X := X) (EU := EU) T zP +
          (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 0 1 rfl b := by
  obtain ⟨b₁, hb₁⟩ := hsw T p hp zP hzP
  refine ⟨e • b₁ + jmap T p 0 (ψ0 (presInv Ψ (insert p T)) b'), ?_⟩
  rw [hnorm, map_add, map_smul, Ψ.hd, map_add, map_smul, hb₁, jmap_d, map_add, map_smul, smul_add]
  abel

/-- **`HswUpToD` from `UrSurj`** (PROVED; tex 3727–3732): with `Φ − 1` onto the unramified
condition at the new places, `j ∘ ψ_{T ∪ {p}} ∘ i' = ψ_T + d b`, where `b = (0, w, 0)` and `w`
is chosen place by place (`place_switch`). -/
theorem hswUpToD_of_urSurj (hsurj : UrSurj (K := K) (S := S) (k := k) (place := place) (X := X)) :
    Ψ.HswUpToD (X := X) (EU := EU) := by
  intro T p _ x _
  obtain ⟨a, u, z⟩ := x
  choose w hw using fun v => Ψ.place_switch hsurj T p v (u v)
  refine ⟨((0, w, 0) : selT (dsuppDataS K S₀ S k M Δ' place X EU T) 0),
    Prod.ext ?_ (Prod.ext ?_ ?_)⟩
  · change (show (globalCx k (GKS K S) M).X 1 from a) =
      (show (globalCx k (GKS K S) M).X 1 from a) + (globalCx k (GKS K S) M).d 0 1 rfl 0
    rw [map_zero, add_zero]
  · funext v
    exact (hw v).1
  · funext v
    change (show (localCx k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M v).X 0
        from z v) + (presInv (EU := EU) Ψ (insert p T) v).H1
          ((presSplitS K S₀ S k M Δ'' place X EU T p v).i.f 1 1 rfl (u v)) =
      ((show (localCx k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M v).X 0
        from z v) + (presInv (EU := EU) Ψ T v).H1 (u v)) +
        ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M).f 0 0 rfl 0 v -
          ((dpresCondS K S₀ S k M Δ' place X EU T).i v).f 0 0 rfl (w v) -
          (localCx k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M v).d (-1) 0 rfl
            (0 : (localCx k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M v).X (-1)))
    rw [(hw v).2, map_zero, map_zero]
    change _ = _ + ((0 : (localCx k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M v).X 0)
      - _ - 0)
    abel

/-- **The paired strict lift at the localization, from `UrSurj`** (PROVED). Kind: PROVED. -/
theorem hlift_of_urSurj (hsurj : UrSurj (K := K) (S := S) (k := k) (place := place) (X := X))
    {T : Finset ι} {p : ι}
    (hp : p ∉ T) (zR : (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).X 1)
    (zP : (suppCxS K S₀ S k M Δ'' place X EU T).X 1)
    (hzP : (suppCxS K S₀ S k M Δ'' place X EU T).d 1 2 rfl zP = 0) (e : k)
    (b' : (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).X 0)
    (hnorm : zR = e • (suppInclS K S₀ S k M Δ'' place X EU T p).f 1 1 rfl zP +
      (suppCxS K S₀ S k M Δ'' place X EU (insert p T)).d 0 1 rfl b') :
    ∃ b : (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).X 0,
      jmap T p 1 (Ψ.ψ (X := X) (EU := EU) (insert p T) zR) =
        e • Ψ.ψ (X := X) (EU := EU) T zP +
          (selCx (dsuppDataS K S₀ S k M Δ' place X EU T)).d 0 1 rfl b :=
  Ψ.hlift_of_transport_loc (Ψ.hswUpToD_of_urSurj hsurj) hp zR zP hzP e b' hnorm

end OrthComparisonInverseLoc

omit [TopologicalSpace k] [DecidableEq ι] in
/-- **Non-vacuity** (PROVED): with no new places and `φo` the identity of the old conditions,
the localized input exists. Kind: PROVED. -/
theorem orthComparisonInverseLoc_of_isEmpty [IsEmpty ι] :
    Nonempty (OrthComparisonInverseLoc K S₀ S k M Δ' Δ' place) :=
  ⟨⟨fun _ => idGHom _, fun _ _ _ => rfl, fun _ => LocHInv.id _, fun j => isEmptyElim j.1⟩⟩

end Pres

end ZInQ.Contrib.CloudB3E1Torsion
