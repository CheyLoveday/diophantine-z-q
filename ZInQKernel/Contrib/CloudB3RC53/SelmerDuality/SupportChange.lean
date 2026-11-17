import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Duality

/-!
# Selmer duality, part 3: change of local conditions and the support change (4.4)

Manuscript `diophantine_zq.tex`, subsection "Actual support comparisons", tex L3480–3496:

> The support-change theorem [Nekovář, Proposition 7.8.8(ii)] retains arbitrary old local
> conditions and puts the unramified condition at new places. [...] Replacing the unramified
> condition by the full condition then gives the singular quotient by a cone of Selmer cones. In
> particular the old complex is an actual subcomplex of an upper triangular model, not just a
> complex with the same Euler characteristic.

Over the Selmer complexes `selCx` of `PairedFunctional/SelmerPairing.lean`
(`C^n = G^n ⊕ U^n ⊕ L^{n−1}`), over an arbitrary commutative ring `S`:

* `RelaxedQuotientNode` (PROVED, tex L3489–3494): for a short exact sequence of local conditions
  `0 → U' → U → W → 0` over the same full local complex (`ι' = ι ∘ f`; for the text
  `U' = U^{ur}_q ⊕ (old)`, `U = L_q ⊕ (old)`, `W = L_q / U^{ur}_q` the singular quotient, by (4.4)
  the complex `[Φ − q]` in degrees one and two), the comparison `C(U') → C(U)` is injective with
  cokernel `W`: `0 → C(U') → C(U) → W → 0` is a short exact sequence of complexes. The old complex
  is an actual subcomplex, and its cohomology differs from the relaxed one by the long exact
  sequence of `W`.
* `SupportChangeData`, `supportMap` (PROVED): the comparison map
  `j : C_S(U) → C_{S ∪ q}(U⁺)`, `(a, u, x) ↦ (g a, μ u + r a, λ x)`, attached to an inflation
  `g : G_S → G_{S∪q}`, a map of local complexes `λ`, a map of local conditions `μ` and a
  factorization `r` of the new restrictions of inflated classes through the new local condition
  (`res⁺ ∘ g = λ ∘ res + ι⁺ ∘ r`, `ι⁺ ∘ μ = λ ∘ ι`); it is a chain map.
* `Nekovar788ii` (PRINT, UNVERIFIED; Nekovář, *Selmer complexes*, Proposition 7.8.8(ii), as cited
  at tex L3480): when the coefficient module is unramified at the new places and the new local
  conditions are the unramified ones, `j` is a quasi-isomorphism.

The five uses listed at tex L3484–3489 are instances of `Nekovar788ii` for the actual Galois
cochain complexes; they are not statable here (no Galois cochain complexes of all degrees in the
library), and enter consumers as instances of the print.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SelmerDuality

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional HomologicalComplex

universe u

variable {S : Type u} [CommRing S]

/-! ### Change of local conditions -/

section Change

variable (D : SelData S) {U' W : GCx S} (f : GHom U' D.U) (g : GHom D.U W)

/-- The Selmer data with local condition `ι ∘ f : U' → L`. -/
def restrictData : SelData S := ⟨D.G, U', D.L, D.res, ghomComp f D.ι⟩

omit D in
/-- Reindexing a composite of relation-indexed chain maps. -/
theorem ghom_reindex {A B C : GCx S} (f : GHom A B) (g : GHom B C) (i j : ℤ) (h : i = j)
    (x : A.X i) : g.f j j rfl (f.f i j h x) = g.f i j h (f.f i i rfl x) := by
  subst h; rfl

/-- The comparison `C(U') → C(U)`, `(a, u', x) ↦ (a, f u', x)`. -/
def changeMap : GHom (selCx (restrictData D f)) (selCx D) where
  f i j h := h ▸ (LinearMap.id : D.G.X i →ₗ[S] D.G.X i).prodMap
    ((f.f i i rfl).prodMap (LinearMap.id : D.L.X (i - 1) →ₗ[S] D.L.X (i - 1)))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    change (D.G.d i i₁ h₁ a, f.f i₁ i₁ rfl (U'.d i i₁ h₁ u),
        D.res.f i (i₁ - 1) (by omega) a - D.ι.f (i₁ - 1) (i₁ - 1) rfl (f.f i (i₁ - 1) (by omega) u) -
          D.L.d (i - 1) (i₁ - 1) (by omega) x) =
      (D.G.d i i₁ h₂ a, D.U.d i i₁ h₂ (f.f i i rfl u),
        D.res.f i (i₁ - 1) (by omega) a - D.ι.f i (i₁ - 1) (by omega) (f.f i i rfl u) -
          D.L.d (i - 1) (i₁ - 1) (by omega) x)
    rw [f.comm i i₁ i i₁ rfl h₁ h₂ rfl u, ghom_reindex f D.ι i (i₁ - 1) (by omega) u]

/-- The projection `C(U) → W`, `(a, u, x) ↦ g u`. -/
def quotMap : GHom (selCx D) W where
  f i j h := h ▸ (g.f i i rfl).comp ((LinearMap.fst S (D.U.X i) (D.L.X (i - 1))).comp
    (LinearMap.snd S (D.G.X i) (D.U.X i × D.L.X (i - 1))))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    exact g.comm i i₁ i i₁ rfl h₁ h₂ rfl u

/-- The short complex `C(U') → C(U) → W`. -/
def changeSES (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0) :
    ShortComplex (CochainComplex (ModuleCat.{u} S) ℤ) :=
  ShortComplex.mk (GHom.toCC (changeMap D f)) (GHom.toCC (quotMap D g)) (by
    rw [GHom.toCC_comp]
    ext i c
    obtain ⟨a, u, x⟩ := c
    exact hfg i u)

/-- **The relaxed condition gives the singular quotient by a cone of Selmer cones** (tex
L3489–3494). For Selmer data `G --res--> L <--ι-- U` and a degreewise short exact sequence of
complexes `0 → U' --f--> U --g--> W → 0`, the sequence of Selmer complexes
`0 → C(U') → C(U) → W → 0` (with `C(U')` for the local condition `ι ∘ f`) is short exact. -/
def RelaxedQuotientNode : Prop :=
  ∀ (S : Type u) [CommRing S] (D : SelData S) (U' W : GCx S) (f : GHom U' D.U) (g : GHom D.U W)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0),
    (∀ i, Function.Injective (f.f i i rfl)) → (∀ i, Function.Surjective (g.f i i rfl)) →
    (∀ i (u : D.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u) →
    (changeSES D f g hfg).ShortExact

theorem relaxedQuotientNode_proof : RelaxedQuotientNode.{u} := by
  intro S _ D U' W f g hfg hinj hsurj hex
  refine shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    obtain ⟨a, u, x⟩ := c
    change g.f i i rfl u = 0 at hc
    obtain ⟨u', rfl⟩ := hex i u hc
    exact ⟨(a, u', x), rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    intro c c' h
    obtain ⟨a, u, x⟩ := c
    obtain ⟨a', u', x'⟩ := c'
    change (a, f.f i i rfl u, x) = (a', f.f i i rfl u', x') at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, hu, rfl⟩ := h
    rw [hinj i hu]
  · rw [ModuleCat.epi_iff_surjective]
    intro w
    obtain ⟨u, rfl⟩ := hsurj i w
    exact ⟨(0, u, 0), rfl⟩

end Change

/-! ### The support change -/

/-- **Support-change data** (tex L3480–3496): Selmer data `D` for the support `S` and `D⁺` for
`S ∪ {q}`, with chain maps `g : G → G⁺` (inflation), `λ : L → L⁺` (the old local complexes inside
the new ones), `μ : U → U⁺` (the old local conditions inside the new ones) and `r : G → U⁺` (the
new local components of inflated cochains, which lie in the new — unramified — condition), such
that `res⁺ ∘ g = λ ∘ res + ι⁺ ∘ r` and `ι⁺ ∘ μ = λ ∘ ι`. -/
structure SupportChangeData (S : Type u) [CommRing S] where
  /-- The old Selmer data. -/
  D : SelData S
  /-- The new Selmer data. -/
  Dp : SelData S
  /-- Inflation. -/
  g : GHom D.G Dp.G
  /-- Old local complexes into new. -/
  lam : GHom D.L Dp.L
  /-- Old local conditions into new. -/
  mu : GHom D.U Dp.U
  /-- New local components of inflated cochains. -/
  r : GHom D.G Dp.U
  /-- `res⁺ ∘ g = λ ∘ res + ι⁺ ∘ r` (relation-indexed). -/
  hres : ∀ i j (h : i = j) (a : D.G.X i), Dp.res.f i j h (g.f i i rfl a) =
    lam.f j j rfl (D.res.f i j h a) + Dp.ι.f i j h (r.f i i rfl a)
  /-- `ι⁺ ∘ μ = λ ∘ ι` (relation-indexed). -/
  hι : ∀ i j (h : i = j) (u : D.U.X i), Dp.ι.f i j h (mu.f i i rfl u) =
    lam.f j j rfl (D.ι.f i j h u)

/-- **The support comparison** `j : C_S(U) → C_{S∪q}(U⁺)`, `(a, u, x) ↦ (g a, μ u + r a, λ x)`. -/
def supportMap (T : SupportChangeData S) : GHom (selCx T.D) (selCx T.Dp) where
  f i j h := h ▸ (((T.g.f i i rfl).comp (LinearMap.fst S _ _)).prod
    (((T.mu.f i i rfl).comp ((LinearMap.fst S _ _).comp (LinearMap.snd S _ _)) +
        (T.r.f i i rfl).comp (LinearMap.fst S _ _)).prod
      ((T.lam.f (i - 1) (i - 1) rfl).comp ((LinearMap.snd S _ _).comp (LinearMap.snd S _ _)))) :
        (T.D.G.X i × T.D.U.X i × T.D.L.X (i - 1)) →ₗ[S]
          (T.Dp.G.X i × T.Dp.U.X i × T.Dp.L.X (i - 1)))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, u, x⟩ := c
    have e1 := T.g.comm i i₁ i i₁ rfl h₁ h₂ rfl a
    have e2 := T.mu.comm i i₁ i i₁ rfl h₁ h₂ rfl u
    have e3 := T.r.comm i i₁ i i₁ rfl h₁ h₂ rfl a
    have e4 := T.lam.comm (i - 1) (i₁ - 1) (i - 1) (i₁ - 1) rfl (by omega) (by omega) rfl x
    change (T.g.f i₁ i₁ rfl (T.D.G.d i i₁ h₁ a),
        T.mu.f i₁ i₁ rfl (T.D.U.d i i₁ h₁ u) + T.r.f i₁ i₁ rfl (T.D.G.d i i₁ h₁ a),
        T.lam.f (i₁ - 1) (i₁ - 1) rfl (T.D.res.f i (i₁ - 1) (by omega) a -
          T.D.ι.f i (i₁ - 1) (by omega) u - T.D.L.d (i - 1) (i₁ - 1) (by omega) x)) =
      (T.Dp.G.d i i₁ h₂ (T.g.f i i rfl a),
        T.Dp.U.d i i₁ h₂ (T.mu.f i i rfl u + T.r.f i i rfl a),
        T.Dp.res.f i (i₁ - 1) (by omega) (T.g.f i i rfl a) -
          T.Dp.ι.f i (i₁ - 1) (by omega) (T.mu.f i i rfl u + T.r.f i i rfl a) -
          T.Dp.L.d (i - 1) (i₁ - 1) (by omega) (T.lam.f (i - 1) (i - 1) rfl x))
    rw [e1, e2, e3, map_add, map_add, T.hres i (i₁ - 1) (by omega) a,
      T.hι i (i₁ - 1) (by omega) u, ← e4]
    simp only [map_sub]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    abel_nf

/-- **PRINT** (UNVERIFIED; Nekovář, *Selmer complexes*, Proposition 7.8.8(ii), as cited at tex
L3480): for support-change data in which the coefficient module is unramified at the new places
and the new local conditions there are the unramified ones (and the old conditions are retained),
the support comparison `j : C_S(U) → C_{S∪q}(U⁺)` is a quasi-isomorphism. -/
def Nekovar788ii (T : SupportChangeData S) : Prop := QuasiIso (GHom.toCC (supportMap T))

/-! ### Non-vacuity -/

/-- The identity chain map. -/
def idGHom (A : GCx S) : GHom A A where
  f i j h := h ▸ LinearMap.id
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    rfl

/-- The zero chain map. -/
def zeroGHom (A B : GCx S) : GHom A B where
  f _ _ _ := 0
  comm _ _ _ _ _ _ _ _ x := by simp

/-- The trivial support change (no new place): `g, λ, μ` the identities and `r = 0`. -/
abbrev idSupportData (D : SelData S) : SupportChangeData S where
  D := D
  Dp := D
  g := idGHom D.G
  lam := idGHom D.L
  mu := idGHom D.U
  r := zeroGHom D.G D.U
  hres i j h a := by
    subst h
    change D.res.f i i rfl a = D.res.f i i rfl a + D.ι.f i i rfl 0
    rw [map_zero, add_zero]
  hι i j h u := by
    subst h
    rfl

/-- **Non-vacuity of `Nekovar788ii`**: for the trivial support change the comparison is the
identity, hence a quasi-isomorphism. PROVED. -/
theorem nekovar788ii_id (D : SelData S) : Nekovar788ii (idSupportData D) := by
  have h : GHom.toCC (supportMap (idSupportData D)) = 𝟙 _ := by
    ext i c
    obtain ⟨a, u, x⟩ := c
    change ((a, u + 0, x) : D.G.X i × D.U.X i × D.L.X (i - 1)) = (a, u, x)
    rw [add_zero]
  unfold Nekovar788ii
  rw [h]
  infer_instance

end ZInQ.Contrib.CloudB3RC53.SelmerDuality
