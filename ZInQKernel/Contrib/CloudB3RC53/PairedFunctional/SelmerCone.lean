import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Proposition

/-!
# RC53 PairedFunctional: the comparison of Selmer complexes for a change of local conditions

Proof of Proposition `ex:arith-paired-functional`, tex L3842–3849:

> Over `S = 𝒪[G]` the only remaining differences between the transported conditions and their
> orthogonal conditions occur at the active and moving places. Their full local complexes have the
> integral contractions displayed above. Their direct sum, of any finite size, is still an integral
> contraction. The resulting comparison `j : C_{U^⊥} → τ^* C_U` is an integral homotopy equivalence
> over `S`.

A Selmer complex is the (shifted) mapping cone of the difference of the global restriction and the
local condition: for complexes `G` (global), `L` (local) and `U` (local condition) of `S`-modules,
with `res : G ⟶ L` and `i : U ⟶ L`,
`C(U) := Cone(G ⊞ U --(res, −i)--> L)⟦−1⟧`
(Mathlib's `CochainComplex.mappingCone`, biproduct and shift). A change of local conditions is
`f : U' ⟶ U` with `f ≫ i = i'`; it induces `j : C(U') ⟶ C(U)`.

Nodes (PROVED):
* `ConeMapHomotopyEquiv`: in a commutative square whose two vertical maps are homotopy equivalences,
  the induced map of (shifted) mapping cones is a homotopy equivalence with that exact forward map
  (via the triangulated homotopy category: a morphism of distinguished triangles with two
  isomorphisms has its third component an isomorphism).
* `SelmerComparison` (tex L3846–3849): if the change of local conditions `f` has a contractible
  mapping cone (in particular, if it is homotopy equivalent to a finite sum of contractible local
  complexes), then `j : C(U') ⟶ C(U)` is a homotopy equivalence and its mapping cone is
  contractible.
* `PairedFunctionalSelmer` (GLUE, tex L3704–3880): `PairedFunctionalIntegral` for the Selmer
  comparison `j` of a change of local conditions `f` whose mapping cone is homotopy equivalent to
  the sum of the shifted tame local models at the active and moving places. The remaining
  hypothesis is `ELLIOT`: that at the changed places the cone of `f` is (homotopy equivalent to)
  the sum of the full local complexes (4.4) (tex L3740–3743, L3842–3845, with Definition
  `ex:arith-data`); it is a statement about local complexes only.

Not proved here (recorded for completeness): the unconditional homotopy equivalence
`Cone(j) ≃ Cone(f)` (a `3 × 3` argument). It is not needed: the text only uses the case where
`Cone(f)` is contractible, which is `SelmerComparison`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open CategoryTheory Limits HomotopyCategory Pretriangulated

variable {S : Type} [CommRing S]

/-- A map of cochain complexes of `S`-modules is the forward map of a homotopy equivalence iff its
image in the homotopy category is an isomorphism. -/
theorem exists_homotopyEquiv_iff_isIso {K L : CochainComplex (ModuleCat.{0} S) ℤ} (φ : K ⟶ L) :
    (∃ e : HomotopyEquiv K L, e.hom = φ) ↔ IsIso ((quotient _ _).map φ) := by
  have h := inverseImage_quotient_isomorphisms (V := ModuleCat.{0} S) (c := ComplexShape.up ℤ)
  constructor
  · intro hφ
    have : HomologicalComplex.homotopyEquivalences (ModuleCat.{0} S) (ComplexShape.up ℤ) φ := hφ
    rw [← h] at this
    exact this
  · intro hφ
    have : (MorphismProperty.isomorphisms _).inverseImage
        (HomotopyCategory.quotient (ModuleCat.{0} S) (ComplexShape.up ℤ)) φ := hφ
    rw [h] at this
    exact this

/-- The mapping cone of a homotopy equivalence is contractible. -/
theorem cone_contractible_of_homotopyEquiv {K L : CochainComplex (ModuleCat.{0} S) ℤ}
    (φ : K ⟶ L) (h : ∃ e : HomotopyEquiv K L, e.hom = φ) :
    Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone φ)) 0) := by
  have hI := (exists_homotopyEquiv_iff_isIso φ).1 h
  have hZ : IsZero ((CochainComplex.mappingCone.triangleh φ).obj₃) :=
    (Triangle.isZero₃_iff_isIso₁ _ (mappingCone_triangleh_distinguished φ)).2 hI
  exact (isZero_quotient_obj_iff _).1 hZ

/-- A shift of a homotopy equivalence is a homotopy equivalence (with the shifted maps). -/
def homotopyEquivShift {K L : CochainComplex (ModuleCat.{0} S) ℤ} (e : HomotopyEquiv K L)
    (n : ℤ) : HomotopyEquiv (K⟦n⟧) (L⟦n⟧) where
  hom := e.hom⟦n⟧'
  inv := e.inv⟦n⟧'
  homotopyHomInvId := by
    have h := e.homotopyHomInvId.shift n
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact h
  homotopyInvHomId := by
    have h := e.homotopyInvHomId.shift n
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact h

/-- A homotopy between `g, h : Y ⟶ Y'` gives one between `𝟙 ⊞ g` and `𝟙 ⊞ h`. -/
def biprodMapHomotopy {X Y Y' : CochainComplex (ModuleCat.{0} S) ℤ} {g h : Y ⟶ Y'}
    (H : Homotopy g h) : Homotopy (biprod.map (𝟙 X) g) (biprod.map (𝟙 X) h) :=
  (Homotopy.ofEq biprod.map_eq).trans
    (((Homotopy.refl (biprod.fst ≫ 𝟙 X ≫ biprod.inl)).add
      ((H.compRight biprod.inr).compLeft biprod.snd)).trans (Homotopy.ofEq biprod.map_eq.symm))

theorem biprod_map_id_comp {X Y Y' Y'' : CochainComplex (ModuleCat.{0} S) ℤ} (f : Y ⟶ Y')
    (g : Y' ⟶ Y'') : biprod.map (𝟙 X) f ≫ biprod.map (𝟙 X) g = biprod.map (𝟙 X) (f ≫ g) := by
  apply biprod.hom_ext' <;> simp

theorem biprod_map_id_id {X Y : CochainComplex (ModuleCat.{0} S) ℤ} :
    biprod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  apply biprod.hom_ext' <;> simp

/-- `𝟙 ⊞ f` is a homotopy equivalence when `f` is. -/
def biprodMapHomotopyEquiv (X : CochainComplex (ModuleCat.{0} S) ℤ)
    {Y Y' : CochainComplex (ModuleCat.{0} S) ℤ} (e : HomotopyEquiv Y Y') :
    HomotopyEquiv (X ⊞ Y) (X ⊞ Y') where
  hom := biprod.map (𝟙 X) e.hom
  inv := biprod.map (𝟙 X) e.inv
  homotopyHomInvId :=
    (Homotopy.ofEq (biprod_map_id_comp _ _)).trans
      ((biprodMapHomotopy e.homotopyHomInvId).trans (Homotopy.ofEq biprod_map_id_id))
  homotopyInvHomId :=
    (Homotopy.ofEq (biprod_map_id_comp _ _)).trans
      ((biprodMapHomotopy e.homotopyInvHomId).trans (Homotopy.ofEq biprod_map_id_id))

/-- **The map of mapping cones induced by a square of homotopy equivalences is a homotopy
equivalence** (used for tex L3846–3849). For a commutative square `φ₁ ≫ b = a ≫ φ₂` of cochain
complexes of `S`-modules in which `a` and `b` are homotopy equivalences, and every shift `n`, the
induced map `(map φ₁ φ₂ a b)⟦n⟧' : (Cone φ₁)⟦n⟧ ⟶ (Cone φ₂)⟦n⟧` is the forward map of a homotopy
equivalence. Classification: PROVED. -/
def ConeMapHomotopyEquiv : Prop :=
  ∀ (S : Type) [CommRing S] (K₁ L₁ K₂ L₂ : CochainComplex (ModuleCat.{0} S) ℤ) (φ₁ : K₁ ⟶ L₁)
    (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) (n : ℤ),
    (∃ e : HomotopyEquiv K₁ K₂, e.hom = a) → (∃ e : HomotopyEquiv L₁ L₂, e.hom = b) →
      ∃ e : HomotopyEquiv ((CochainComplex.mappingCone φ₁)⟦n⟧)
          ((CochainComplex.mappingCone φ₂)⟦n⟧),
        e.hom = (CochainComplex.mappingCone.map φ₁ φ₂ a b comm)⟦n⟧'

theorem coneMapHomotopyEquiv_proof : ConeMapHomotopyEquiv := by
  intro S _ K₁ L₁ K₂ L₂ φ₁ φ₂ a b comm n ha hb
  have hIa := (exists_homotopyEquiv_iff_isIso a).1 ha
  have hIb := (exists_homotopyEquiv_iff_isIso b).1 hb
  let τ := CochainComplex.mappingCone.trianglehMapOfHomotopy (Homotopy.ofEq comm)
  have h1 : IsIso τ.hom₁ := hIa
  have h2 : IsIso τ.hom₂ := hIb
  have h3 : IsIso τ.hom₃ :=
    isIso₃_of_isIso₁₂ τ (mappingCone_triangleh_distinguished φ₁)
      (mappingCone_triangleh_distinguished φ₂) h1 h2
  have hmap : ∃ e : HomotopyEquiv (CochainComplex.mappingCone φ₁) (CochainComplex.mappingCone φ₂),
      e.hom = CochainComplex.mappingCone.map φ₁ φ₂ a b comm := by
    rw [exists_homotopyEquiv_iff_isIso, CochainComplex.mappingCone.map_eq_mapOfHomotopy]
    exact h3
  obtain ⟨e, he⟩ := hmap
  exact ⟨homotopyEquivShift e n, by rw [← he]; rfl⟩

/-! ### Selmer complexes -/

/-- The difference map `(res, −i) : G ⊞ U ⟶ L`. -/
def selmerDiff {G L U : CochainComplex (ModuleCat.{0} S) ℤ} (res : G ⟶ L) (i : U ⟶ L) :
    G ⊞ U ⟶ L :=
  biprod.desc res (-i)

/-- **The Selmer complex** `C(U) = Cone(G ⊞ U --(res, −i)--> L)⟦−1⟧` of the global complex `G`
with local condition `i : U ⟶ L` (the Selmer-complex formalism cited at tex L3826–3836). -/
def selmerCx {G L U : CochainComplex (ModuleCat.{0} S) ℤ} (res : G ⟶ L) (i : U ⟶ L) :
    CochainComplex (ModuleCat.{0} S) ℤ :=
  (CochainComplex.mappingCone (selmerDiff res i))⟦(-1 : ℤ)⟧

theorem selmerDiff_comm {G L U U' : CochainComplex (ModuleCat.{0} S) ℤ} (res : G ⟶ L)
    (i : U ⟶ L) (i' : U' ⟶ L) (f : U' ⟶ U) (hf : f ≫ i = i') :
    selmerDiff res i' ≫ 𝟙 L = biprod.map (𝟙 G) f ≫ selmerDiff res i := by
  subst hf
  apply biprod.hom_ext' <;> simp [selmerDiff]

/-- **The comparison map** `j : C(U') ⟶ C(U)` induced by a change of local conditions
`f : U' ⟶ U` with `f ≫ i = i'` (identity on `G` and `L`). -/
def selmerMap {G L U U' : CochainComplex (ModuleCat.{0} S) ℤ} (res : G ⟶ L) (i : U ⟶ L)
    (i' : U' ⟶ L) (f : U' ⟶ U) (hf : f ≫ i = i') : selmerCx res i' ⟶ selmerCx res i :=
  (CochainComplex.mappingCone.map (selmerDiff res i') (selmerDiff res i) (biprod.map (𝟙 G) f)
    (𝟙 L) (selmerDiff_comm res i i' f hf))⟦(-1 : ℤ)⟧'

/-- **The Selmer comparison is an integral homotopy equivalence** (tex L3846–3849: "Their direct
sum, of any finite size, is still an integral contraction. The resulting comparison
`j : C_{U^⊥} → τ^* C_U` is an integral homotopy equivalence over `S`"). For complexes of
`S`-modules `G, L, U, U'`, maps `res : G ⟶ L`, `i : U ⟶ L`, `i' : U' ⟶ L` and a change of local
conditions `f : U' ⟶ U` with `f ≫ i = i'`: if the mapping cone of `f` is contractible, then the
induced `j : C(U') ⟶ C(U)` is the forward map of a homotopy equivalence over `S`, and the mapping
cone of `j` is contractible. Classification: PROVED. -/
def SelmerComparison : Prop :=
  ∀ (S : Type) [CommRing S] (G L U U' : CochainComplex (ModuleCat.{0} S) ℤ) (res : G ⟶ L)
    (i : U ⟶ L) (i' : U' ⟶ L) (f : U' ⟶ U) (hf : f ≫ i = i'),
    Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone f)) 0) →
      (∃ e : HomotopyEquiv (selmerCx res i') (selmerCx res i), e.hom = selmerMap res i i' f hf) ∧
      Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone (selmerMap res i i' f hf))) 0)

theorem selmerComparison_proof : SelmerComparison := by
  intro S _ G L U U' res i i' f hf ⟨hcone⟩
  obtain ⟨ef, hef⟩ := homotopyEquiv_of_cone_contractible f hcone
  have ha : ∃ e : HomotopyEquiv (G ⊞ U') (G ⊞ U), e.hom = biprod.map (𝟙 G) f :=
    ⟨biprodMapHomotopyEquiv G ef, by rw [← hef]; rfl⟩
  have hb : ∃ e : HomotopyEquiv L L, e.hom = 𝟙 L := ⟨HomotopyEquiv.refl L, rfl⟩
  have hj := coneMapHomotopyEquiv_proof S _ _ _ _ (selmerDiff res i') (selmerDiff res i)
    (biprod.map (𝟙 G) f) (𝟙 L) (selmerDiff_comm res i i' f hf) (-1) ha hb
  exact ⟨hj, cone_contractible_of_homotopyEquiv _ hj⟩

/-- Non-vacuity of `SelmerComparison`: the identity change of local conditions `f = 𝟙 U` has a
contractible cone, so for every `res, i` the comparison `C(U) ⟶ C(U)` is a homotopy equivalence.
PROVED. -/
theorem selmerComparison_id (G L U : CochainComplex (ModuleCat.{0} S) ℤ) (res : G ⟶ L)
    (i : U ⟶ L) :
    ∃ e : HomotopyEquiv (selmerCx res i) (selmerCx res i),
      e.hom = selmerMap res i i (𝟙 U) (Category.id_comp i) :=
  (selmerComparison_proof S G L U U res i i (𝟙 U) (Category.id_comp i)
    (cone_id_contractible U)).1

/-- **`ex:arith-paired-functional` for the Selmer comparison of a change of local conditions**
(GLUE; tex L3704–3880, with L3842–3849). Over any commutative ring `S`: let `C' = C(U')` and
`C = C(U)` be the Selmer complexes of `res : G ⟶ L` with local conditions `i' : U' ⟶ L` and
`i : U ⟶ L` (`C' = C_{U^⊥}`, `C = τ^* C_U`), `f : U' ⟶ U` a change of local conditions
(`f ≫ i = i'`) and `j = selmerMap` the comparison. Assume (`ELLIOT`, tex L3740–3743, L3842–3845:
the local computation at the active and moving places) that the mapping cone of `f` is homotopy
equivalent to the sum of finitely many shifted tame local models (4.4), each with Frobenius units or
an inertia unit. Then the conclusions of `PairedFunctionalIntegral` hold for `j`: an integral
homotopy inverse `e.inv` with `e.hom = j`, `z^⊥ = e.inv (c z)` a cocycle, `j z^⊥ − c z` a boundary,
`λ_z` closed, and uniqueness up to a coboundary (exponent `a = 0`). Classification: PROVED (from
the stated local hypothesis). -/
def PairedFunctionalSelmer : Prop :=
  ∀ (S : Type) [CommRing S] (G L U U' CU Z : CochainComplex (ModuleCat.{0} S) ℤ) (res : G ⟶ L)
    (i : U ⟶ L) (i' : U' ⟶ L) (f : U' ⟶ U) (hf : f ≫ i = i')
    (c : Z ⟶ selmerCx res i) (z : Z.X 1)
    (pd1 : CU.X 1 →ₗ[S] (selmerCx res i').X 2 →ₗ[S] S)
    (pd2 : CU.X 2 →ₗ[S] (selmerCx res i').X 1 →ₗ[S] S)
    (pd3 : CU.X 3 →ₗ[S] (selmerCx res i').X 0 →ₗ[S] S) (ε ε' : S)
    (ι : Type) [Fintype ι] (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module S (M v)]
    (A Cin D : ∀ v, Module.End S (M v)) (hDC : ∀ v, D v * Cin v = Cin v * A v) (n : ι → ℤ),
    (∀ v, (IsUnit (A v) ∧ IsUnit (D v)) ∨ IsUnit (Cin v)) →
    Nonempty (HomotopyEquiv (CochainComplex.mappingCone f)
      (⨁ fun v => (tameComplex (A v) (Cin v) (D v) (hDC v))⟦n v⟧)) →
    (Z.d 1 2).hom z = 0 →
    (∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w (((selmerCx res i').d 1 2).hom y)) →
    (∀ w y, pd2 w (((selmerCx res i').d 0 1).hom y) = ε' * pd3 ((CU.d 2 3).hom w) y) →
    ∃ e : HomotopyEquiv (selmerCx res i') (selmerCx res i), e.hom = selmerMap res i i' f hf ∧
      ((selmerCx res i').d 1 2).hom ((e.inv.f 1).hom ((c.f 1).hom z)) = 0 ∧
      (∃ b : (selmerCx res i).X 0,
        ((selmerMap res i i' f hf).f 1).hom ((e.inv.f 1).hom ((c.f 1).hom z)) - (c.f 1).hom z =
          ((selmerCx res i).d 0 1).hom b) ∧
      (∀ w : CU.X 1, pairedFunctional pd2 e.inv ((c.f 1).hom z) ((CU.d 1 2).hom w) = 0) ∧
      ∀ e' : HomotopyEquiv (selmerCx res i') (selmerCx res i), e'.hom = selmerMap res i i' f hf →
        ∃ y : (selmerCx res i').X 0, ∀ w : CU.X 2,
          pairedFunctional pd2 e.inv ((c.f 1).hom z) w -
            pairedFunctional pd2 e'.inv ((c.f 1).hom z) w = ε' * pd3 ((CU.d 2 3).hom w) y

theorem pairedFunctionalSelmer_proof : PairedFunctionalSelmer := by
  intro S _ G L U U' CU Z res i i' f hf c z pd1 pd2 pd3 ε ε' ι _ M _ _ A Cin D hDC n hunit
    ⟨eLoc⟩ hz hL1 hL2
  -- the sum of the shifted local models is contractible
  obtain ⟨hsum⟩ : Nonempty (Homotopy
      (𝟙 (⨁ fun v => (tameComplex (A v) (Cin v) (D v) (hDC v))⟦n v⟧)) 0) :=
    contractible_biproduct _ fun v =>
      contractible_shift _ (n v)
        (tameComplexContractible_proof S (M v) (A v) (Cin v) (D v) (hDC v) (hunit v))
  -- so is the cone of `f`, hence the cone of `j`
  have hf' := contractible_of_homotopyEquiv eLoc ⟨hsum⟩
  obtain ⟨-, ⟨hj⟩⟩ := selmerComparison_proof S G L U U' res i i' f hf hf'
  -- the cone of `j` is homotopy equivalent to the sum of the local models (both contractible)
  have hcone : Nonempty (HomotopyEquiv (CochainComplex.mappingCone (selmerMap res i i' f hf))
      (⨁ fun v => (tameComplex (A v) (Cin v) (D v) (hDC v))⟦n v⟧)) :=
    ⟨homotopyEquivOfContractible hj hsum⟩
  exact pairedFunctionalIntegral_proof S CU (selmerCx res i') (selmerCx res i) Z
    (selmerMap res i i' f hf) c z pd1 pd2 pd3 ε ε' ι M A Cin D hDC n hunit hcone hz hL1 hL2

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
