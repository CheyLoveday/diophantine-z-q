import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeafLit

/-!
# Lane RC35: the comparison map from the Kummer model to the integral block model

The ordinary compact Kummer complex has the integral matrix-disk normal form
`blockComplex B₁ B₂ B₃` (a free line in degrees one and two, matrix disks `B₁, B₂, B₃` in
degrees `0 → 1`, `1 → 2`, `2 → 3`). This file compares it with the scalar Kummer model
`kummerModel 0 δ₁ δ₂ δ₃` (the two-term core with zero differential plus scalar disks).

* `ghtpyEquiv`, `quasiIso_toCC_of_htpy`: a pair of relation-indexed chain maps with
  relation-indexed homotopies `1 ≃ g f`, `1 ≃ f g` gives a Mathlib homotopy equivalence, hence a
  quasi-isomorphism.
* `kmBlockMap` (A1): the core of the scalar model maps identically onto the free lines, the disks
  map to zero; `kmBlockMap_quasiIso` (A2): it is a quasi-isomorphism when the disk scalars and
  the disk determinants are units (the homotopy inverse `kmBlockInv` projects onto the free
  lines; the contractions are `δⱼ⁻¹` and `Bⱼ⁻¹`); `kmBlockMap_one`, `kmBlockMap_two` (A3).
* `retainedKMMap`, `retainedKMMap_quasiIso`, `retainedKMMap_compact_quasiIso` (A4): the map into
  the base change of the retained integral model of the compact Kummer complex, through
  `blockComplex (Bⱼ.map φ) ≅ φ^* blockComplex Bⱼ ≅ φ^* retained`, and its composite with the
  base-changed comparison into `φ^* (compactCentralComplex G)`.
* `e₁R`, `e₂R`, `retainedKMFunctional`, `retainedKMFunctional_map`, `retainedKMMap_one` (A5):
  the retained free generators, the base-changed functional `s ⊗ x ↦ s · φ (λ₀ x)`, its value
  `φ (λ₀ e₂R) · y e₂'` on the image of `vec2 y`, and the image `z 0 · (1 ⊗ e₁R)` of the class.
* `block_cycle_coboundary`, `retained_cycle_coboundary` (A6): a degree-one cycle agrees with
  `φ (a₀) · (1 ⊗ e₁R)` up to a coboundary after base change, when the first two base-changed disk
  determinants are units.
* `kmBlockMap_quasiIso_example`, `kmBlockMap_example_values` (A7): non-vacuity over `ℚ` with
  `Bⱼ = (2)`, `δⱼ = 2`.

**Classification.** PROVED (every theorem); definitions are marked as such.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring.KmIdent

open Matrix CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC.SelmerComplex (ofCC)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral

/-! ### Homotopy equivalences from relation-indexed homotopies -/

section Htpy

variable {S : Type} [CommRing S]

/-- Definition: the Mathlib homotopy components of a relation-indexed homotopy family. -/
def ghtpyHom {A B : GCx S} (h : ∀ i j : ℤ, j + 1 = i → A.X i →ₗ[S] B.X j) (i j : ℤ) :
    A.toCC.X i ⟶ B.toCC.X j :=
  if hij : j + 1 = i then ModuleCat.ofHom (h i j hij) else 0

/-- PROVED: the homotopy component on a relation. -/
theorem ghtpyHom_of {A B : GCx S} (h : ∀ i j : ℤ, j + 1 = i → A.X i →ₗ[S] B.X j) {i j : ℤ}
    (hij : j + 1 = i) : ghtpyHom h i j = ModuleCat.ofHom (h i j hij) :=
  dite_eq_left_of_eq_true (eq_true hij)

/-- PROVED: the differential of `GCx.toCC` on a relation. -/
theorem toCC_d_eq (A : GCx S) {i j : ℤ} (h : i + 1 = j) :
    A.toCC.d i j = ModuleCat.ofHom (A.d i j h) :=
  dite_eq_left_of_eq_true (eq_true h)

/-- Definition: a homotopy `𝟙 ≃ p` from a relation-indexed homotopy family satisfying
`x = h (d x) + d (h x) + p x`. -/
def idHtpy {A : GCx S} (p : GHom A A) (h : ∀ i j : ℤ, j + 1 = i → A.X i →ₗ[S] A.X j)
    (e : ∀ (i j k : ℤ) (hj : j + 1 = i) (hk : i + 1 = k) (x : A.X i),
      x = h k i hk (A.d i k hk x) + A.d j i hj (h i j hj x) + p.f i i rfl x) :
    Homotopy (𝟙 A.toCC) (GHom.toCC p) where
  hom := ghtpyHom h
  zero i j hr := by simp [ghtpyHom, show ¬ j + 1 = i from hr]
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1),
      ghtpyHom_of h (rfl : i + 1 = i + 1), ghtpyHom_of h (sub_add_cancel i 1)]
    rw [toCC_d_eq A (rfl : i + 1 = i + 1), toCC_d_eq A (sub_add_cancel i 1)]
    ext x
    exact e i (i - 1) (i + 1) (sub_add_cancel i 1) rfl x

/-- Definition: the Mathlib homotopy equivalence of two relation-indexed chain maps with
relation-indexed homotopies `1 ≃ g f` and `1 ≃ f g`. -/
def ghtpyEquiv {A B : GCx S} (f : GHom A B) (g : GHom B A)
    (hA : ∀ i j : ℤ, j + 1 = i → A.X i →ₗ[S] A.X j)
    (hB : ∀ i j : ℤ, j + 1 = i → B.X i →ₗ[S] B.X j)
    (eA : ∀ (i j k : ℤ) (hj : j + 1 = i) (hk : i + 1 = k) (x : A.X i),
      x = hA k i hk (A.d i k hk x) + A.d j i hj (hA i j hj x) + g.f i i rfl (f.f i i rfl x))
    (eB : ∀ (i j k : ℤ) (hj : j + 1 = i) (hk : i + 1 = k) (x : B.X i),
      x = hB k i hk (B.d i k hk x) + B.d j i hj (hB i j hj x) + f.f i i rfl (g.f i i rfl x)) :
    HomotopyEquiv A.toCC B.toCC where
  hom := GHom.toCC f
  inv := GHom.toCC g
  homotopyHomInvId := by
    rw [GHom.toCC_comp]
    exact (idHtpy (ghomComp f g) hA eA).symm
  homotopyInvHomId := by
    rw [GHom.toCC_comp]
    exact (idHtpy (ghomComp g f) hB eB).symm

/-- PROVED: a relation-indexed chain map with a homotopy inverse is a quasi-isomorphism. -/
theorem quasiIso_toCC_of_htpy {A B : GCx S} (f : GHom A B) (g : GHom B A)
    (hA : ∀ i j : ℤ, j + 1 = i → A.X i →ₗ[S] A.X j)
    (hB : ∀ i j : ℤ, j + 1 = i → B.X i →ₗ[S] B.X j)
    (eA : ∀ (i j k : ℤ) (hj : j + 1 = i) (hk : i + 1 = k) (x : A.X i),
      x = hA k i hk (A.d i k hk x) + A.d j i hj (hA i j hj x) + g.f i i rfl (f.f i i rfl x))
    (eB : ∀ (i j k : ℤ) (hj : j + 1 = i) (hk : i + 1 = k) (x : B.X i),
      x = hB k i hk (B.d i k hk x) + B.d j i hj (hB i j hj x) + f.f i i rfl (g.f i i rfl x)) :
    QuasiIso (GHom.toCC f) :=
  HomotopyEquiv.quasiIso_hom (ghtpyEquiv f g hA hB eA eB)

end Htpy

/-! ### The scalar Kummer model in coordinates -/

section ScalarModel

variable {S : Type} [CommRing S]

/-- Definition: the basis index type of the scalar Kummer model `kummerModel 0 δ₁ δ₂ δ₃`. -/
abbrev KIdx : Type :=
  ((((Empty ⊕ Unit) ⊕ Empty) ⊕ Empty) ⊕ (((Fin 1 ⊕ Empty) ⊕ Unit) ⊕ Unit)) ⊕
    ((((Fin 1 ⊕ Unit) ⊕ Unit) ⊕ Empty) ⊕ (((Empty ⊕ Empty) ⊕ Empty) ⊕ Unit))

/-- Definition: the scalar Kummer model with zero core. -/
abbrev KM (δ₁ δ₂ δ₃ : S) := kummerModel (0 : Matrix (Fin 1) (Fin 1) S) δ₁ δ₂ δ₃

/-- Definition: the core basis index of degree one. -/
abbrev ke₁ : KIdx := .inr (.inl (.inl (.inl (.inl 0))))

/-- Definition: the core basis index of degree two. -/
abbrev ke₂ : KIdx := .inl (.inr (.inl (.inl (.inl 0))))

/-- Definition: the core index of the degree-two coordinates (the argument type of `vec2`). -/
abbrev ke₂' : ((Fin 1 ⊕ Empty) ⊕ Unit) ⊕ Unit := .inl (.inl (.inl 0))

/-- Definition: the total differential of the scalar model, coordinatewise. -/
def dvec (δ₁ δ₂ δ₃ : S) (v : KIdx → S) : KIdx → S
  | .inr (.inl (.inl (.inl (.inr _)))) => δ₁ * v (.inl (.inl (.inl (.inl (.inr ())))))
  | .inl (.inr (.inl (.inr _))) => δ₂ * v (.inr (.inl (.inl (.inr ()))))
  | .inr (.inr (.inr _)) => δ₃ * v (.inl (.inr (.inr ())))
  | _ => 0

/-- PROVED: the total differential of the scalar model is `dvec`. -/
theorem dTot_mulVec (δ₁ δ₂ δ₃ : S) (v : KIdx → S) :
    (KM δ₁ δ₂ δ₃).toBased.dTot *ᵥ v = dvec δ₁ δ₂ δ₃ v := by
  funext x
  rcases x with ((((e | u) | e) | e) | (((i | e) | u) | u)) |
    ((((i | u) | u) | e) | (((e | e) | e) | u))
  all_goals try exact e.elim
  all_goals simp [mulVec, dotProduct, Fintype.sum_sum_type, BasedCx.dTot, FourCx.toBased,
    kummerModel, FourCx.sum, twoTerm, disk01, disk12, disk23, sc, dvec]

/-- Definition: the contraction of the scalar disks, coordinatewise. -/
def hvec (u₁ u₂ u₃ : S) (v : KIdx → S) : KIdx → S
  | .inl (.inl (.inl (.inl (.inr _)))) => u₁ * v (.inr (.inl (.inl (.inl (.inr ())))))
  | .inr (.inl (.inl (.inr _))) => u₂ * v (.inl (.inr (.inl (.inr ()))))
  | .inl (.inr (.inr _)) => u₃ * v (.inr (.inr (.inr ())))
  | _ => 0

/-- Definition: `hvec` as a linear map. -/
def hvecLin (u₁ u₂ u₃ : S) : (KIdx → S) →ₗ[S] (KIdx → S) where
  toFun := hvec u₁ u₂ u₃
  map_add' v w := by
    funext x
    rcases x with ((((e | u) | e) | e) | (((i | e) | u) | u)) |
      ((((i | u) | u) | e) | (((e | e) | e) | u))
    all_goals first | exact e.elim | simp [hvec, mul_add]
  map_smul' c v := by
    funext x
    rcases x with ((((e | u) | e) | e) | (((i | e) | u) | u)) |
      ((((i | u) | u) | e) | (((e | e) | e) | u))
    all_goals first | exact e.elim | (simp [hvec]; done) | (simp [hvec]; ring)

/-- PROVED: the disk contraction lowers degrees by one. -/
theorem hvec_mem (δ₁ δ₂ δ₃ u₁ u₂ u₃ : S) {i j : ℤ} (hj : j + 1 = i) {v : KIdx → S}
    (hv : v ∈ (KM δ₁ δ₂ δ₃).toBased.degSub i) :
    hvec u₁ u₂ u₃ v ∈ (KM δ₁ δ₂ δ₃).toBased.degSub j := by
  intro x hx
  rcases x with ((((e | u) | e) | e) | (((i | e) | u) | u)) |
    ((((i | u) | u) | e) | (((e | e) | e) | u))
  all_goals try first | exact e.elim | rfl
  all_goals
    refine mul_eq_zero_of_right _ (hv _ ?_)
    simp [BasedCx.deg, FourCx.toBased] at hx ⊢
    omega

/-- PROVED: the homotopy identity of the scalar model,
`v = h (d v) + d (h v) + (core projection of v)`. -/
theorem scalar_htpy (δ₁ δ₂ δ₃ u₁ u₂ u₃ : S) (h₁ : u₁ * δ₁ = 1) (h₂ : u₂ * δ₂ = 1)
    (h₃ : u₃ * δ₃ = 1) (h₁' : δ₁ * u₁ = 1) (h₂' : δ₂ * u₂ = 1) (h₃' : δ₃ * u₃ = 1)
    (v : KIdx → S) :
    v = hvec u₁ u₂ u₃ (dvec δ₁ δ₂ δ₃ v) + dvec δ₁ δ₂ δ₃ (hvec u₁ u₂ u₃ v) +
      (Pi.single ke₁ (v ke₁) + Pi.single ke₂ (v ke₂)) := by
  funext x
  rcases x with ((((e | u) | e) | e) | (((i | e) | u) | u)) |
    ((((i | u) | u) | e) | (((e | e) | e) | u))
  all_goals try exact e.elim
  all_goals (try fin_cases i)
  all_goals simp [hvec, dvec, ← mul_assoc, h₁, h₂, h₃, h₁', h₂', h₃']

/-- PROVED: the scalar differential kills a core line. -/
theorem dvec_single₁ (δ₁ δ₂ δ₃ a : S) : dvec δ₁ δ₂ δ₃ (Pi.single ke₁ a) = 0 := by
  funext x
  rcases x with ((((e | u) | e) | e) | (((i | e) | u) | u)) |
    ((((i | u) | u) | e) | (((e | e) | e) | u))
  all_goals first | exact e.elim | simp [dvec]

/-- PROVED: the scalar differential kills the other core line. -/
theorem dvec_single₂ (δ₁ δ₂ δ₃ a : S) : dvec δ₁ δ₂ δ₃ (Pi.single ke₂ a) = 0 := by
  funext x
  rcases x with ((((e | u) | e) | e) | (((i | e) | u) | u)) |
    ((((i | u) | u) | e) | (((e | e) | e) | u))
  all_goals first | exact e.elim | simp [dvec]

/-- Definition: a basis line of the scalar model in the degree of its index. -/
def lineVec (δ₁ δ₂ δ₃ : S) (e : KIdx) (k : ℤ) (he : (KM δ₁ δ₂ δ₃).toBased.deg e = k) :
    S →ₗ[S] (KM δ₁ δ₂ δ₃).toBased.degSub k :=
  LinearMap.codRestrict _ (LinearMap.single S (fun _ => S) e) (fun a x hx => by
    have hne : x ≠ e := fun h => hx (h ▸ he)
    exact Pi.single_eq_of_ne (M := fun _ : KIdx => S) hne a)

/-- PROVED: the value of a basis line. -/
theorem lineVec_val (δ₁ δ₂ δ₃ : S) (e : KIdx) (k : ℤ) (he : (KM δ₁ δ₂ δ₃).toBased.deg e = k)
    (a : S) : ((lineVec δ₁ δ₂ δ₃ e k he a : (KM δ₁ δ₂ δ₃).toBased.degSub k) : KIdx → S) =
      Pi.single e a := rfl

end ScalarModel

/-! ### The block model -/

section BlockModel

variable {S : Type} [CommRing S] {m₁ m₂ m₃ : ℕ}

/-- PROVED: the block model vanishes outside degrees `0, …, 3`. -/
theorem blockX_subsingleton (B₁ : Matrix (Fin m₁) (Fin m₁) S) (B₂ : Matrix (Fin m₂) (Fin m₂) S)
    (B₃ : Matrix (Fin m₃) (Fin m₃) S) {i : ℤ} (hi : i < 0 ∨ 3 < i) :
    Subsingleton ((ofCC (blockComplex B₁ B₂ B₃)).X i) := by
  rcases i with n | n
  · simp only [Int.ofNat_eq_natCast] at hi
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    exact inferInstanceAs (Subsingleton PUnit)
  · exact inferInstanceAs (Subsingleton PUnit)

/-- PROVED: the first block differential as a relation-indexed differential. -/
theorem ofCC_block_d0 (B₁ : Matrix (Fin m₁) (Fin m₁) S) (B₂ : Matrix (Fin m₂) (Fin m₂) S)
    (B₃ : Matrix (Fin m₃) (Fin m₃) S) (h : (0 : ℤ) + 1 = 1) (x : Fin m₁ → S) :
    (ofCC (blockComplex B₁ B₂ B₃)).d 0 1 h x = blockD0 B₁ x := by
  exact LinearMap.congr_fun (blockComplex_d0 B₁ B₂ B₃) x

/-- PROVED: the middle block differential as a relation-indexed differential. -/
theorem ofCC_block_d1 (B₁ : Matrix (Fin m₁) (Fin m₁) S) (B₂ : Matrix (Fin m₂) (Fin m₂) S)
    (B₃ : Matrix (Fin m₃) (Fin m₃) S) (h : (1 : ℤ) + 1 = 2)
    (x : S × (Fin m₁ → S) × (Fin m₂ → S)) :
    (ofCC (blockComplex B₁ B₂ B₃)).d 1 2 h x = blockD1 B₂ x := by
  exact LinearMap.congr_fun (blockComplex_d1 B₁ B₂ B₃) x

/-- PROVED: the last block differential as a relation-indexed differential. -/
theorem ofCC_block_d2 (B₁ : Matrix (Fin m₁) (Fin m₁) S) (B₂ : Matrix (Fin m₂) (Fin m₂) S)
    (B₃ : Matrix (Fin m₃) (Fin m₃) S) (h : (2 : ℤ) + 1 = 3)
    (x : S × (Fin m₂ → S) × (Fin m₃ → S)) :
    (ofCC (blockComplex B₁ B₂ B₃)).d 2 3 h x = blockD2 B₃ x := by
  exact LinearMap.congr_fun (blockComplex_d2 B₁ B₂ B₃) x

end BlockModel

/-! ### The comparison map (A1) -/

section KmMap

variable {S : Type} [CommRing S] {m₁ m₂ m₃ : ℕ}

/-- Definition: the coordinate vector of an element of the scalar model. -/
def kval (δ₁ δ₂ δ₃ : S) {k : ℤ} (x : (KM δ₁ δ₂ δ₃).toBased.toGCx.X k) : KIdx → S :=
  (show (KM δ₁ δ₂ δ₃).toBased.degSub k from x).1

/-- PROVED: the differential of the scalar model on values. -/
theorem km_d_val (δ₁ δ₂ δ₃ : S) {i j : ℤ} (h : i + 1 = j)
    (x : (KM δ₁ δ₂ δ₃).toBased.toGCx.X i) :
    kval δ₁ δ₂ δ₃ ((KM δ₁ δ₂ δ₃).toBased.toGCx.d i j h x) = dvec δ₁ δ₂ δ₃ (kval δ₁ δ₂ δ₃ x) :=
  dTot_mulVec δ₁ δ₂ δ₃ _

/-- Definition: degree one of the comparison map, `v ↦ (v e₁, 0, 0)`. -/
def kmF1 (δ₁ δ₂ δ₃ : S) (m₁ m₂ : ℕ) :
    (KM δ₁ δ₂ δ₃).toBased.degSub 1 →ₗ[S] S × (Fin m₁ → S) × (Fin m₂ → S) :=
  ((LinearMap.proj (R := S) (φ := fun _ : KIdx => S) ke₁).comp (Submodule.subtype _)).prod 0

/-- Definition: degree two of the comparison map, `v ↦ (v e₂, 0, 0)`. -/
def kmF2 (δ₁ δ₂ δ₃ : S) (m₂ m₃ : ℕ) :
    (KM δ₁ δ₂ δ₃).toBased.degSub 2 →ₗ[S] S × (Fin m₂ → S) × (Fin m₃ → S) :=
  ((LinearMap.proj (R := S) (φ := fun _ : KIdx => S) ke₂).comp (Submodule.subtype _)).prod 0

/-- Definition: the degreewise components of the comparison map. -/
def kmFfam (δ₁ δ₂ δ₃ : S) (B₁ : Matrix (Fin m₁) (Fin m₁) S) (B₂ : Matrix (Fin m₂) (Fin m₂) S)
    (B₃ : Matrix (Fin m₃) (Fin m₃) S) :
    ∀ i : ℤ, (KM δ₁ δ₂ δ₃).toBased.toGCx.X i →ₗ[S] (ofCC (blockComplex B₁ B₂ B₃)).X i
  | .ofNat 1 => kmF1 δ₁ δ₂ δ₃ m₁ m₂
  | .ofNat 2 => kmF2 δ₁ δ₂ δ₃ m₂ m₃
  | _ => 0

/-- PROVED: the comparison map vanishes outside degrees one and two. -/
theorem kmFfam_zero (δ₁ δ₂ δ₃ : S) (B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (B₂ : Matrix (Fin m₂) (Fin m₂) S) (B₃ : Matrix (Fin m₃) (Fin m₃) S) {i : ℤ} (h1 : i ≠ 1)
    (h2 : i ≠ 2) : kmFfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i = 0 := by
  rcases i with ((_ | _ | _ | n) | n)
  · rfl
  · exact absurd rfl h1
  · exact absurd rfl h2
  · rfl
  · rfl

/-- **A1.** Definition: the comparison map from the scalar Kummer model (zero core) to the block
model: the core lines map identically onto the free lines, the disks map to zero. -/
def kmBlockMap (δ₁ δ₂ δ₃ : S) (B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (B₂ : Matrix (Fin m₂) (Fin m₂) S) (B₃ : Matrix (Fin m₃) (Fin m₃) S) :
    GHom (kummerModel (0 : Matrix (Fin 1) (Fin 1) S) δ₁ δ₂ δ₃).toBased.toGCx
      (ofCC (blockComplex B₁ B₂ B₃)) where
  f i j h := by subst h; exact kmFfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    change kmFfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i₁ ((KM δ₁ δ₂ δ₃).toBased.toGCx.d i i₁ h₁ x) =
      (ofCC (blockComplex B₁ B₂ B₃)).d i i₁ h₂ (kmFfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i x)
    rcases (show (i < 0 ∨ 2 < i) ∨ i = 0 ∨ i = 1 ∨ i = 2 by omega) with hi | rfl | rfl | rfl
    · rw [kmFfam_zero δ₁ δ₂ δ₃ B₁ B₂ B₃ (i := i) (by omega) (by omega),
        kmFfam_zero δ₁ δ₂ δ₃ B₁ B₂ B₃ (i := i₁) (by omega) (by omega)]
      simp
    · obtain rfl : i₁ = 1 := by omega
      rw [kmFfam_zero δ₁ δ₂ δ₃ B₁ B₂ B₃ (i := 0) (by decide) (by decide), LinearMap.zero_apply,
        map_zero]
      refine Prod.ext ?_ (Prod.ext rfl rfl)
      change kval δ₁ δ₂ δ₃ ((KM δ₁ δ₂ δ₃).toBased.toGCx.d 0 1 h₁ x) ke₁ = 0
      rw [km_d_val]
      rfl
    · obtain rfl : i₁ = 2 := by omega
      change kmF2 δ₁ δ₂ δ₃ m₂ m₃ ((KM δ₁ δ₂ δ₃).toBased.toGCx.d 1 2 h₁ x) =
        (ofCC (blockComplex B₁ B₂ B₃)).d 1 2 h₂ (kmF1 δ₁ δ₂ δ₃ m₁ m₂ x)
      rw [ofCC_block_d1]
      refine Prod.ext ?_ (Prod.ext ?_ rfl)
      · change kval δ₁ δ₂ δ₃ ((KM δ₁ δ₂ δ₃).toBased.toGCx.d 1 2 h₁ x) ke₂ = 0
        rw [km_d_val]
        rfl
      · change 0 = B₂.mulVecLin 0
        rw [map_zero]
    · obtain rfl : i₁ = 3 := by omega
      rw [kmFfam_zero δ₁ δ₂ δ₃ B₁ B₂ B₃ (i := 3) (by decide) (by decide), LinearMap.zero_apply]
      change 0 = (ofCC (blockComplex B₁ B₂ B₃)).d 2 3 h₂ (kmF2 δ₁ δ₂ δ₃ m₂ m₃ x)
      rw [ofCC_block_d2]
      change 0 = B₃.mulVecLin 0
      rw [map_zero]

/-- PROVED: the components of `kmBlockMap`. -/
theorem kmBlockMap_f (δ₁ δ₂ δ₃ : S) (B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (B₂ : Matrix (Fin m₂) (Fin m₂) S) (B₃ : Matrix (Fin m₃) (Fin m₃) S) (i : ℤ) :
    (kmBlockMap δ₁ δ₂ δ₃ B₁ B₂ B₃).f i i rfl = kmFfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i := rfl

/-- **A3.** PROVED: the model class `vec1 (kz z)` maps to `(z 0, 0, 0)`. -/
theorem kmBlockMap_one (δ₁ δ₂ δ₃ : S) (B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (B₂ : Matrix (Fin m₂) (Fin m₂) S) (B₃ : Matrix (Fin m₃) (Fin m₃) S) (z : Fin 1 → S) :
    (kmBlockMap δ₁ δ₂ δ₃ B₁ B₂ B₃).f 1 1 rfl ⟨vec1 (kz z), vec1_mem _ _⟩ =
      ((z 0, 0, 0) : S × (Fin m₁ → S) × (Fin m₂ → S)) := rfl

/-- **A3.** PROVED: a degree-two model vector `vec2 y` maps to `(y e₂', 0, 0)`. -/
theorem kmBlockMap_two (δ₁ δ₂ δ₃ : S) (B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (B₂ : Matrix (Fin m₂) (Fin m₂) S) (B₃ : Matrix (Fin m₃) (Fin m₃) S)
    (y : ((Fin 1 ⊕ Empty) ⊕ Unit) ⊕ Unit → S) :
    (kmBlockMap δ₁ δ₂ δ₃ B₁ B₂ B₃).f 2 2 rfl ⟨vec2 y, vec2_mem _ _⟩ =
      ((y ke₂', 0, 0) : S × (Fin m₂ → S) × (Fin m₃ → S)) := rfl

end KmMap

/-! ### The homotopy inverse and the quasi-isomorphism (A2) -/

section KmQis

variable {S : Type} [CommRing S] {m₁ m₂ m₃ : ℕ}

/-- Definition: degree one of the homotopy inverse, `(a, u, w) ↦ a e₁`. -/
def kmG1 (δ₁ δ₂ δ₃ : S) (m₁ m₂ : ℕ) :
    S × (Fin m₁ → S) × (Fin m₂ → S) →ₗ[S] (KM δ₁ δ₂ δ₃).toBased.degSub 1 :=
  (lineVec δ₁ δ₂ δ₃ ke₁ 1 rfl).comp (LinearMap.fst S S _)

/-- Definition: degree two of the homotopy inverse, `(a, u, w) ↦ a e₂`. -/
def kmG2 (δ₁ δ₂ δ₃ : S) (m₂ m₃ : ℕ) :
    S × (Fin m₂ → S) × (Fin m₃ → S) →ₗ[S] (KM δ₁ δ₂ δ₃).toBased.degSub 2 :=
  (lineVec δ₁ δ₂ δ₃ ke₂ 2 rfl).comp (LinearMap.fst S S _)

/-- Definition: the degreewise components of the homotopy inverse. -/
def kmGfam (δ₁ δ₂ δ₃ : S) (B₁ : Matrix (Fin m₁) (Fin m₁) S) (B₂ : Matrix (Fin m₂) (Fin m₂) S)
    (B₃ : Matrix (Fin m₃) (Fin m₃) S) :
    ∀ i : ℤ, (ofCC (blockComplex B₁ B₂ B₃)).X i →ₗ[S] (KM δ₁ δ₂ δ₃).toBased.toGCx.X i
  | .ofNat 1 => kmG1 δ₁ δ₂ δ₃ m₁ m₂
  | .ofNat 2 => kmG2 δ₁ δ₂ δ₃ m₂ m₃
  | _ => 0

/-- PROVED: the homotopy inverse vanishes outside degrees one and two. -/
theorem kmGfam_zero (δ₁ δ₂ δ₃ : S) (B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (B₂ : Matrix (Fin m₂) (Fin m₂) S) (B₃ : Matrix (Fin m₃) (Fin m₃) S) {i : ℤ} (h1 : i ≠ 1)
    (h2 : i ≠ 2) : kmGfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i = 0 := by
  rcases i with ((_ | _ | _ | n) | n)
  · rfl
  · exact absurd rfl h1
  · exact absurd rfl h2
  · rfl
  · rfl

/-- Definition: the homotopy inverse of `kmBlockMap`, the projection onto the free lines. -/
def kmBlockInv (δ₁ δ₂ δ₃ : S) (B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (B₂ : Matrix (Fin m₂) (Fin m₂) S) (B₃ : Matrix (Fin m₃) (Fin m₃) S) :
    GHom (ofCC (blockComplex B₁ B₂ B₃)) (KM δ₁ δ₂ δ₃).toBased.toGCx where
  f i j h := by subst h; exact kmGfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    change kmGfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i₁ ((ofCC (blockComplex B₁ B₂ B₃)).d i i₁ h₁ x) =
      (KM δ₁ δ₂ δ₃).toBased.toGCx.d i i₁ h₂ (kmGfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i x)
    rcases (show (i < 0 ∨ 2 < i) ∨ i = 0 ∨ i = 1 ∨ i = 2 by omega) with hi | rfl | rfl | rfl
    · rw [kmGfam_zero δ₁ δ₂ δ₃ B₁ B₂ B₃ (i := i) (by omega) (by omega),
        kmGfam_zero δ₁ δ₂ δ₃ B₁ B₂ B₃ (i := i₁) (by omega) (by omega)]
      simp
    · obtain rfl : i₁ = 1 := by omega
      rw [kmGfam_zero δ₁ δ₂ δ₃ B₁ B₂ B₃ (i := 0) (by decide) (by decide), LinearMap.zero_apply,
        map_zero]
      change kmG1 δ₁ δ₂ δ₃ m₁ m₂ ((ofCC (blockComplex B₁ B₂ B₃)).d 0 1 h₁ x) = 0
      refine (congrArg (kmG1 δ₁ δ₂ δ₃ m₁ m₂) (ofCC_block_d0 B₁ B₂ B₃ h₁ x)).trans ?_
      apply Subtype.ext
      exact Pi.single_zero (M := fun _ : KIdx => S) ke₁
    · obtain rfl : i₁ = 2 := by omega
      change kmG2 δ₁ δ₂ δ₃ m₂ m₃ ((ofCC (blockComplex B₁ B₂ B₃)).d 1 2 h₁ x) =
        (KM δ₁ δ₂ δ₃).toBased.toGCx.d 1 2 h₂ (kmG1 δ₁ δ₂ δ₃ m₁ m₂ x)
      refine (congrArg (kmG2 δ₁ δ₂ δ₃ m₂ m₃) (ofCC_block_d1 B₁ B₂ B₃ h₁ x)).trans ?_
      apply Subtype.ext
      refine (Pi.single_zero (M := fun _ : KIdx => S) ke₂).trans ?_
      exact (dvec_single₁ δ₁ δ₂ δ₃ (show S × (Fin m₁ → S) × (Fin m₂ → S) from x).1).symm.trans
        (km_d_val δ₁ δ₂ δ₃ h₂ (kmG1 δ₁ δ₂ δ₃ m₁ m₂ x)).symm
    · obtain rfl : i₁ = 3 := by omega
      rw [kmGfam_zero δ₁ δ₂ δ₃ B₁ B₂ B₃ (i := 3) (by decide) (by decide), LinearMap.zero_apply]
      apply Subtype.ext
      exact (dvec_single₂ δ₁ δ₂ δ₃ (show S × (Fin m₂ → S) × (Fin m₃ → S) from x).1).symm.trans
        (km_d_val δ₁ δ₂ δ₃ h₂ (kmG2 δ₁ δ₂ δ₃ m₂ m₃ x)).symm

/-- Definition: the disk contraction of the scalar model as a relation-indexed family. -/
def kmHtpyA (δ₁ δ₂ δ₃ u₁ u₂ u₃ : S) (i j : ℤ) (h : j + 1 = i) :
    (KM δ₁ δ₂ δ₃).toBased.toGCx.X i →ₗ[S] (KM δ₁ δ₂ δ₃).toBased.toGCx.X j :=
  ((hvecLin u₁ u₂ u₃).domRestrict ((KM δ₁ δ₂ δ₃).toBased.degSub i)).codRestrict
    ((KM δ₁ δ₂ δ₃).toBased.degSub j) (fun v => hvec_mem δ₁ δ₂ δ₃ u₁ u₂ u₃ h v.2)

/-- PROVED: the comparison map followed by its inverse is the core projection. -/
theorem kmGF_val (δ₁ δ₂ δ₃ : S) (B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (B₂ : Matrix (Fin m₂) (Fin m₂) S) (B₃ : Matrix (Fin m₃) (Fin m₃) S) (i : ℤ)
    (x : (KM δ₁ δ₂ δ₃).toBased.toGCx.X i) :
    kval δ₁ δ₂ δ₃ (kmGfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i (kmFfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i x)) =
      Pi.single ke₁ (kval δ₁ δ₂ δ₃ x ke₁) + Pi.single ke₂ (kval δ₁ δ₂ δ₃ x ke₂) := by
  have hx : ∀ y, (KM δ₁ δ₂ δ₃).toBased.deg y ≠ i → kval δ₁ δ₂ δ₃ x y = 0 :=
    (show (KM δ₁ δ₂ δ₃).toBased.degSub i from x).2
  rcases (show (i ≠ 1 ∧ i ≠ 2) ∨ i = 1 ∨ i = 2 by omega) with ⟨h1, h2⟩ | rfl | rfl
  · rw [kmFfam_zero δ₁ δ₂ δ₃ B₁ B₂ B₃ h1 h2, LinearMap.zero_apply, map_zero,
      hx ke₁ (by simp [BasedCx.deg, FourCx.toBased]; omega),
      hx ke₂ (by simp [BasedCx.deg, FourCx.toBased]; omega), Pi.single_zero, Pi.single_zero,
      add_zero]
    rfl
  · rw [hx ke₂ (by simp [BasedCx.deg, FourCx.toBased]), Pi.single_zero, add_zero]
    rfl
  · rw [hx ke₁ (by simp [BasedCx.deg, FourCx.toBased]), Pi.single_zero, zero_add]
    rfl

/-- PROVED: the homotopy identity on the scalar model, `x = h d x + d h x + g f x`. -/
theorem kmHtpyA_eq (δ₁ δ₂ δ₃ u₁ u₂ u₃ : S) (h₁ : u₁ * δ₁ = 1) (h₂ : u₂ * δ₂ = 1)
    (h₃ : u₃ * δ₃ = 1) (h₁' : δ₁ * u₁ = 1) (h₂' : δ₂ * u₂ = 1) (h₃' : δ₃ * u₃ = 1)
    (B₁ : Matrix (Fin m₁) (Fin m₁) S) (B₂ : Matrix (Fin m₂) (Fin m₂) S)
    (B₃ : Matrix (Fin m₃) (Fin m₃) S) (i j k : ℤ) (hj : j + 1 = i) (hk : i + 1 = k)
    (x : (KM δ₁ δ₂ δ₃).toBased.toGCx.X i) :
    x = kmHtpyA δ₁ δ₂ δ₃ u₁ u₂ u₃ k i hk ((KM δ₁ δ₂ δ₃).toBased.toGCx.d i k hk x) +
      (KM δ₁ δ₂ δ₃).toBased.toGCx.d j i hj (kmHtpyA δ₁ δ₂ δ₃ u₁ u₂ u₃ i j hj x) +
        (kmBlockInv δ₁ δ₂ δ₃ B₁ B₂ B₃).f i i rfl ((kmBlockMap δ₁ δ₂ δ₃ B₁ B₂ B₃).f i i rfl x) := by
  apply Subtype.ext
  change kval δ₁ δ₂ δ₃ x = hvec u₁ u₂ u₃ (kval δ₁ δ₂ δ₃ ((KM δ₁ δ₂ δ₃).toBased.toGCx.d i k hk x)) +
    kval δ₁ δ₂ δ₃ ((KM δ₁ δ₂ δ₃).toBased.toGCx.d j i hj (kmHtpyA δ₁ δ₂ δ₃ u₁ u₂ u₃ i j hj x)) +
      kval δ₁ δ₂ δ₃ (kmGfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i (kmFfam δ₁ δ₂ δ₃ B₁ B₂ B₃ i x))
  rw [km_d_val, km_d_val, kmGF_val]
  exact scalar_htpy δ₁ δ₂ δ₃ u₁ u₂ u₃ h₁ h₂ h₃ h₁' h₂' h₃' _

/-- Definition: the contraction of the first matrix disk, `(a, u, w) ↦ C₁ u`. -/
def kB0 (C₁ : Matrix (Fin m₁) (Fin m₁) S) (m₂ : ℕ) :
    S × (Fin m₁ → S) × (Fin m₂ → S) →ₗ[S] (Fin m₁ → S) :=
  C₁.mulVecLin ∘ₗ (LinearMap.fst S _ _) ∘ₗ (LinearMap.snd S S _)

/-- Definition: the contraction of the middle matrix disk, `(a, u, w) ↦ (0, 0, C₂ u)`. -/
def kB1 (C₂ : Matrix (Fin m₂) (Fin m₂) S) (m₁ m₃ : ℕ) :
    S × (Fin m₂ → S) × (Fin m₃ → S) →ₗ[S] S × (Fin m₁ → S) × (Fin m₂ → S) :=
  (0 : _ →ₗ[S] S).prod ((0 : _ →ₗ[S] (Fin m₁ → S)).prod
    (C₂.mulVecLin ∘ₗ (LinearMap.fst S _ _) ∘ₗ (LinearMap.snd S S _)))

/-- Definition: the contraction of the last matrix disk, `w ↦ (0, 0, C₃ w)`. -/
def kB2 (C₃ : Matrix (Fin m₃) (Fin m₃) S) (m₂ : ℕ) :
    (Fin m₃ → S) →ₗ[S] S × (Fin m₂ → S) × (Fin m₃ → S) :=
  (0 : _ →ₗ[S] S).prod ((0 : _ →ₗ[S] (Fin m₂ → S)).prod C₃.mulVecLin)

/-- Definition: the disk contraction of the block model as a relation-indexed family. -/
def kmHtpyB (C₁ : Matrix (Fin m₁) (Fin m₁) S) (C₂ : Matrix (Fin m₂) (Fin m₂) S)
    (C₃ : Matrix (Fin m₃) (Fin m₃) S) (B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (B₂ : Matrix (Fin m₂) (Fin m₂) S) (B₃ : Matrix (Fin m₃) (Fin m₃) S) :
    ∀ i j : ℤ, j + 1 = i →
      (ofCC (blockComplex B₁ B₂ B₃)).X i →ₗ[S] (ofCC (blockComplex B₁ B₂ B₃)).X j
  | .ofNat 1, .ofNat 0, _ => kB0 C₁ m₂
  | .ofNat 2, .ofNat 1, _ => kB1 C₂ m₁ m₃
  | .ofNat 3, .ofNat 2, _ => kB2 C₃ m₂
  | _, _, _ => 0

/-- PROVED: the homotopy identity of the block model in degree zero. -/
theorem blk_htpy0 (C₁ B₁ : Matrix (Fin m₁) (Fin m₁) S) (h : C₁ * B₁ = 1) (x : Fin m₁ → S) :
    x = kB0 C₁ m₂ (blockD0 B₁ x) := by
  change x = C₁ *ᵥ (B₁ *ᵥ x)
  rw [mulVec_mulVec, h, one_mulVec]

/-- PROVED: the homotopy identity of the block model in degree one. -/
theorem blk_htpy1 (δ₁ δ₂ δ₃ : S) (C₁ B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (C₂ B₂ : Matrix (Fin m₂) (Fin m₂) S) (h₁ : B₁ * C₁ = 1) (h₂ : C₂ * B₂ = 1)
    (x : S × (Fin m₁ → S) × (Fin m₂ → S)) :
    x = kB1 C₂ m₁ m₃ (blockD1 B₂ x) + blockD0 B₁ (kB0 C₁ m₂ x) +
      kmF1 δ₁ δ₂ δ₃ m₁ m₂ (kmG1 δ₁ δ₂ δ₃ m₁ m₂ x) := by
  obtain ⟨a, u, w⟩ := x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change a = 0 + 0 + Pi.single (M := fun _ : KIdx => S) ke₁ a ke₁
    simp
  · change u = 0 + B₁ *ᵥ (C₁ *ᵥ u) + 0
    rw [mulVec_mulVec, h₁, one_mulVec, zero_add, add_zero]
  · change w = C₂ *ᵥ (B₂ *ᵥ w) + 0 + 0
    rw [mulVec_mulVec, h₂, one_mulVec, add_zero, add_zero]

/-- PROVED: the homotopy identity of the block model in degree two. -/
theorem blk_htpy2 (δ₁ δ₂ δ₃ : S) (C₂ B₂ : Matrix (Fin m₂) (Fin m₂) S)
    (C₃ B₃ : Matrix (Fin m₃) (Fin m₃) S) (h₂ : B₂ * C₂ = 1) (h₃ : C₃ * B₃ = 1)
    (x : S × (Fin m₂ → S) × (Fin m₃ → S)) :
    x = kB2 C₃ m₂ (blockD2 B₃ x) + blockD1 B₂ (kB1 C₂ m₁ m₃ x) +
      kmF2 δ₁ δ₂ δ₃ m₂ m₃ (kmG2 δ₁ δ₂ δ₃ m₂ m₃ x) := by
  obtain ⟨a, u, w⟩ := x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change a = 0 + 0 + Pi.single (M := fun _ : KIdx => S) ke₂ a ke₂
    simp
  · change u = 0 + B₂ *ᵥ (C₂ *ᵥ u) + 0
    rw [mulVec_mulVec, h₂, one_mulVec, zero_add, add_zero]
  · change w = C₃ *ᵥ (B₃ *ᵥ w) + 0 + 0
    rw [mulVec_mulVec, h₃, one_mulVec, add_zero, add_zero]

/-- PROVED: the homotopy identity of the block model in degree three. -/
theorem blk_htpy3 (C₃ B₃ : Matrix (Fin m₃) (Fin m₃) S) (h₃ : B₃ * C₃ = 1) (x : Fin m₃ → S) :
    x = blockD2 B₃ (kB2 C₃ m₂ x) := by
  change x = B₃ *ᵥ (C₃ *ᵥ x)
  rw [mulVec_mulVec, h₃, one_mulVec]

/-- PROVED: the homotopy identity on the block model, `x = h d x + d h x + f g x`. -/
theorem kmHtpyB_eq (δ₁ δ₂ δ₃ : S) (C₁ B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (C₂ B₂ : Matrix (Fin m₂) (Fin m₂) S) (C₃ B₃ : Matrix (Fin m₃) (Fin m₃) S)
    (h₁ : C₁ * B₁ = 1) (h₁' : B₁ * C₁ = 1) (h₂ : C₂ * B₂ = 1) (h₂' : B₂ * C₂ = 1)
    (h₃ : C₃ * B₃ = 1) (h₃' : B₃ * C₃ = 1) (i j k : ℤ) (hj : j + 1 = i) (hk : i + 1 = k)
    (x : (ofCC (blockComplex B₁ B₂ B₃)).X i) :
    x = kmHtpyB C₁ C₂ C₃ B₁ B₂ B₃ k i hk ((ofCC (blockComplex B₁ B₂ B₃)).d i k hk x) +
      (ofCC (blockComplex B₁ B₂ B₃)).d j i hj (kmHtpyB C₁ C₂ C₃ B₁ B₂ B₃ i j hj x) +
        (kmBlockMap δ₁ δ₂ δ₃ B₁ B₂ B₃).f i i rfl ((kmBlockInv δ₁ δ₂ δ₃ B₁ B₂ B₃).f i i rfl x) := by
  rcases (show (i < 0 ∨ 3 < i) ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with
    hi | rfl | rfl | rfl | rfl
  · have := blockX_subsingleton B₁ B₂ B₃ hi
    exact Subsingleton.elim _ _
  · obtain rfl : j = -1 := by omega
    obtain rfl : k = 1 := by omega
    have := blockX_subsingleton B₁ B₂ B₃ (i := -1) (by norm_num)
    have e1 : (ofCC (blockComplex B₁ B₂ B₃)).d (-1) 0 hj
        (kmHtpyB C₁ C₂ C₃ B₁ B₂ B₃ 0 (-1) hj x) = 0 := by
      rw [Subsingleton.elim (kmHtpyB C₁ C₂ C₃ B₁ B₂ B₃ 0 (-1) hj x) 0, map_zero]
    have e3 : (kmBlockMap δ₁ δ₂ δ₃ B₁ B₂ B₃).f 0 0 rfl
        ((kmBlockInv δ₁ δ₂ δ₃ B₁ B₂ B₃).f 0 0 rfl x) = 0 := by
      change kmFfam δ₁ δ₂ δ₃ B₁ B₂ B₃ 0 (kmGfam δ₁ δ₂ δ₃ B₁ B₂ B₃ 0 x) = 0
      rw [kmGfam_zero δ₁ δ₂ δ₃ B₁ B₂ B₃ (i := 0) (by decide) (by decide), LinearMap.zero_apply,
        map_zero]
    rw [e1, e3, add_zero, add_zero]
    exact (blk_htpy0 (m₂ := m₂) C₁ B₁ h₁ x).trans
      (congrArg (kB0 C₁ m₂) (ofCC_block_d0 B₁ B₂ B₃ hk x)).symm
  · obtain rfl : j = 0 := by omega
    obtain rfl : k = 2 := by omega
    have e1 : kmHtpyB C₁ C₂ C₃ B₁ B₂ B₃ 2 1 hk ((ofCC (blockComplex B₁ B₂ B₃)).d 1 2 hk x) =
        kB1 C₂ m₁ m₃ (blockD1 B₂ x) := congrArg (kB1 C₂ m₁ m₃) (ofCC_block_d1 B₁ B₂ B₃ hk x)
    have e2 : (ofCC (blockComplex B₁ B₂ B₃)).d 0 1 hj (kmHtpyB C₁ C₂ C₃ B₁ B₂ B₃ 1 0 hj x) =
        blockD0 B₁ (kB0 C₁ m₂ x) := ofCC_block_d0 B₁ B₂ B₃ hj _
    exact (blk_htpy1 (m₃ := m₃) δ₁ δ₂ δ₃ C₁ B₁ C₂ B₂ h₁' h₂ x).trans
      (congrArg₂ (· + ·) (congrArg₂ (· + ·) e1.symm e2.symm) rfl)
  · obtain rfl : j = 1 := by omega
    obtain rfl : k = 3 := by omega
    have e1 : kmHtpyB C₁ C₂ C₃ B₁ B₂ B₃ 3 2 hk ((ofCC (blockComplex B₁ B₂ B₃)).d 2 3 hk x) =
        kB2 C₃ m₂ (blockD2 B₃ x) := congrArg (kB2 C₃ m₂) (ofCC_block_d2 B₁ B₂ B₃ hk x)
    have e2 : (ofCC (blockComplex B₁ B₂ B₃)).d 1 2 hj (kmHtpyB C₁ C₂ C₃ B₁ B₂ B₃ 2 1 hj x) =
        blockD1 B₂ (kB1 C₂ m₁ m₃ x) := ofCC_block_d1 B₁ B₂ B₃ hj _
    exact (blk_htpy2 (m₁ := m₁) δ₁ δ₂ δ₃ C₂ B₂ C₃ B₃ h₂' h₃ x).trans
      (congrArg₂ (· + ·) (congrArg₂ (· + ·) e1.symm e2.symm) rfl)
  · obtain rfl : j = 2 := by omega
    obtain rfl : k = 4 := by omega
    have := blockX_subsingleton B₁ B₂ B₃ (i := 4) (by norm_num)
    have e1 : kmHtpyB C₁ C₂ C₃ B₁ B₂ B₃ 4 3 hk ((ofCC (blockComplex B₁ B₂ B₃)).d 3 4 hk x) =
        0 := by
      rw [Subsingleton.elim ((ofCC (blockComplex B₁ B₂ B₃)).d 3 4 hk x) 0, map_zero]
    have e2 : (ofCC (blockComplex B₁ B₂ B₃)).d 2 3 hj (kmHtpyB C₁ C₂ C₃ B₁ B₂ B₃ 3 2 hj x) =
        blockD2 B₃ (kB2 C₃ m₂ x) := ofCC_block_d2 B₁ B₂ B₃ hj _
    have e3 : (kmBlockMap δ₁ δ₂ δ₃ B₁ B₂ B₃).f 3 3 rfl
        ((kmBlockInv δ₁ δ₂ δ₃ B₁ B₂ B₃).f 3 3 rfl x) = 0 := by
      change kmFfam δ₁ δ₂ δ₃ B₁ B₂ B₃ 3 (kmGfam δ₁ δ₂ δ₃ B₁ B₂ B₃ 3 x) = 0
      rw [kmGfam_zero δ₁ δ₂ δ₃ B₁ B₂ B₃ (i := 3) (by decide) (by decide), LinearMap.zero_apply,
        map_zero]
    rw [e1, e3, zero_add, add_zero]
    exact (blk_htpy3 (m₂ := m₂) C₃ B₃ h₃' x).trans e2.symm

/-- **A2.** PROVED: the comparison map is a quasi-isomorphism when the disk scalars and the
disk determinants are units (a homotopy equivalence: both sides contract onto the free lines). -/
theorem kmBlockMap_quasiIso {δ₁ δ₂ δ₃ : S} {B₁ : Matrix (Fin m₁) (Fin m₁) S}
    {B₂ : Matrix (Fin m₂) (Fin m₂) S} {B₃ : Matrix (Fin m₃) (Fin m₃) S} (hδ₁ : IsUnit δ₁)
    (hδ₂ : IsUnit δ₂) (hδ₃ : IsUnit δ₃) (hB₁ : IsUnit B₁.det) (hB₂ : IsUnit B₂.det)
    (hB₃ : IsUnit B₃.det) : QuasiIso (GHom.toCC (kmBlockMap δ₁ δ₂ δ₃ B₁ B₂ B₃)) := by
  obtain ⟨U₁, rfl⟩ := hδ₁
  obtain ⟨U₂, rfl⟩ := hδ₂
  obtain ⟨U₃, rfl⟩ := hδ₃
  exact quasiIso_toCC_of_htpy _ (kmBlockInv _ _ _ B₁ B₂ B₃)
    (kmHtpyA _ _ _ ((U₁⁻¹ : Sˣ) : S) ((U₂⁻¹ : Sˣ) : S) ((U₃⁻¹ : Sˣ) : S))
    (kmHtpyB B₁⁻¹ B₂⁻¹ B₃⁻¹ B₁ B₂ B₃)
    (kmHtpyA_eq _ _ _ _ _ _ U₁.inv_mul U₂.inv_mul U₃.inv_mul U₁.mul_inv U₂.mul_inv U₃.mul_inv
      B₁ B₂ B₃)
    (kmHtpyB_eq _ _ _ _ _ _ _ _ _ (nonsing_inv_mul B₁ hB₁) (mul_nonsing_inv B₁ hB₁)
      (nonsing_inv_mul B₂ hB₂) (mul_nonsing_inv B₂ hB₂) (nonsing_inv_mul B₃ hB₃)
      (mul_nonsing_inv B₃ hB₃))

end KmQis

/-! ### Mathlib maps between `ofCC` complexes -/

section OfCCMap

variable {S : Type} [CommRing S]

/-- Definition: a Mathlib cochain map as a relation-indexed chain map of `ofCC` complexes. -/
def ofCCMap {X Y : CochainComplex (ModuleCat.{0} S) ℤ} (u : X ⟶ Y) : GHom (ofCC X) (ofCC Y) where
  f i j h := by subst h; exact (u.f i).hom
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    exact (congrArg (fun g => g.hom x) (u.comm i i₁)).symm

/-- PROVED: `ofCCMap` respects composition after `GHom.toCC`. -/
theorem toCC_ofCCMap_comp {X Y Z : CochainComplex (ModuleCat.{0} S) ℤ} (u : X ⟶ Y)
    (v : Y ⟶ Z) :
    GHom.toCC (ghomComp (ofCCMap u) (ofCCMap v)) = GHom.toCC (ofCCMap (u ≫ v)) :=
  GHom.toCC_ext fun _ _ => rfl

/-- PROVED: `ofCCMap` of an identity is an identity after `GHom.toCC`. -/
theorem toCC_ofCCMap_id (X : CochainComplex (ModuleCat.{0} S) ℤ) :
    GHom.toCC (ofCCMap (𝟙 X)) = 𝟙 (ofCC X).toCC := by
  rw [← toCC_idGHom]
  exact GHom.toCC_ext fun _ _ => rfl

/-- PROVED: `ofCCMap` of an isomorphism is an isomorphism after `GHom.toCC`. -/
theorem isIso_toCC_ofCCMap {X Y : CochainComplex (ModuleCat.{0} S) ℤ} (e : X ≅ Y) :
    IsIso (GHom.toCC (ofCCMap e.hom)) :=
  ⟨⟨GHom.toCC (ofCCMap e.inv), by
      rw [GHom.toCC_comp, toCC_ofCCMap_comp, e.hom_inv_id, toCC_ofCCMap_id],
    by rw [GHom.toCC_comp, toCC_ofCCMap_comp, e.inv_hom_id, toCC_ofCCMap_id]⟩⟩

/-- Definition: the identification `(ofCC X).toCC ≅ X` (identity components). -/
def ofCCIso (X : CochainComplex (ModuleCat.{0} S) ℤ) : (ofCC X).toCC ≅ X :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    rw [toCC_d_eq (ofCC X) hij]
    rfl)

end OfCCMap

/-! ### The retained integral model of the compact Kummer complex (A4) -/

section Retained

open ZInQ.Contrib.RC53Assist.CalibrationModel ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)

variable {S : Type} [CommRing S] {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ}

/-- Definition: the reduced block model of the retained complex is the base change of the
retained complex: `blockComplex (Bⱼ.map φ) ≅ φ^* blockComplex Bⱼ ≅ φ^* retained`. -/
def retainedBlockIso (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (φ : ℤ_[2] →+* S) :
    blockComplex ((centralDiskMatrix G hfinite 1).map φ) ((centralDiskMatrix G hfinite 2).map φ)
        ((centralDiskMatrix G hfinite 3).map φ) ≅
      scalarChangedComplex φ (retainedCentralComplex G hfinite) :=
  (blockScalarChangeIso φ _ _ _).symm ≪≫
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (retainedCentralNormalization G hfinite H)

/-- **A4.** Definition: the comparison map from the scalar Kummer model to the base-changed
retained integral model of the compact Kummer complex. -/
def retainedKMMap (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (φ : ℤ_[2] →+* S)
    (δ₁ δ₂ δ₃ : S) :
    GHom (kummerModel (0 : Matrix (Fin 1) (Fin 1) S) δ₁ δ₂ δ₃).toBased.toGCx
      (ofCC (scalarChangedComplex φ (retainedCentralComplex G hfinite))) :=
  ghomComp (kmBlockMap δ₁ δ₂ δ₃ _ _ _) (ofCCMap (retainedBlockIso G hfinite H φ).hom)

/-- PROVED: a unit determinant stays a unit after mapping the matrix. -/
theorem isUnit_det_map {m : ℕ} (φ : ℤ_[2] →+* S) (B : Matrix (Fin m) (Fin m) ℤ_[2])
    (h : IsUnit (φ B.det)) : IsUnit (B.map φ).det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact h

/-- **A4.** PROVED: the retained comparison map is a quasi-isomorphism when the disk scalars and
the base-changed disk determinants are units. -/
theorem retainedKMMap_quasiIso (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (φ : ℤ_[2] →+* S)
    {δ₁ δ₂ δ₃ : S} (hδ₁ : IsUnit δ₁) (hδ₂ : IsUnit δ₂) (hδ₃ : IsUnit δ₃)
    (hd₁ : IsUnit (φ (centralDiskMatrix G hfinite 1).det))
    (hd₂ : IsUnit (φ (centralDiskMatrix G hfinite 2).det))
    (hd₃ : IsUnit (φ (centralDiskMatrix G hfinite 3).det)) :
    QuasiIso (GHom.toCC (retainedKMMap G hfinite H φ δ₁ δ₂ δ₃)) := by
  unfold retainedKMMap
  rw [← GHom.toCC_comp]
  have := kmBlockMap_quasiIso hδ₁ hδ₂ hδ₃ (isUnit_det_map φ _ hd₁) (isUnit_det_map φ _ hd₂)
    (isUnit_det_map φ _ hd₃)
  have := isIso_toCC_ofCCMap (retainedBlockIso G hfinite H φ)
  have := quasiIso_of_isIso (GHom.toCC (ofCCMap (retainedBlockIso G hfinite H φ).hom))
  infer_instance

/-- **A4.** PROVED: the retained comparison map, followed by the identification
`(ofCC X).toCC ≅ X` and the base change of the retained comparison, is a quasi-isomorphism into
the base-changed compact Kummer complex. -/
theorem retainedKMMap_compact_quasiIso (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (φ : ℤ_[2] →+* S)
    {δ₁ δ₂ δ₃ : S} (hδ₁ : IsUnit δ₁) (hδ₂ : IsUnit δ₂) (hδ₃ : IsUnit δ₃)
    (hd₁ : IsUnit (φ (centralDiskMatrix G hfinite 1).det))
    (hd₂ : IsUnit (φ (centralDiskMatrix G hfinite 2).det))
    (hd₃ : IsUnit (φ (centralDiskMatrix G hfinite 3).det)) :
    QuasiIso (GHom.toCC (retainedKMMap G hfinite H φ δ₁ δ₂ δ₃) ≫
      (ofCCIso (scalarChangedComplex φ (retainedCentralComplex G hfinite))).hom ≫
        ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (retainedCentralComparison G hfinite)) := by
  have := retainedKMMap_quasiIso G hfinite H φ hδ₁ hδ₂ hδ₃ hd₁ hd₂ hd₃
  have := retainedCentralComparison_baseChange G hfinite φ
  have := quasiIso_of_isIso
    (ofCCIso (scalarChangedComplex φ (retainedCentralComplex G hfinite))).hom
  infer_instance

end Retained

/-! ### Base-change coordinates of the free lines -/

section LineCoordinates

open ZInQ.Manuscript.RC53Assist.CentralSelmer

variable {R S : Type} [CommRing R] [CommRing S] {m₁ m₂ m₃ : ℕ}

/-- PROVED: a basis vector of the reduced block model, pulled back to the base change of the
block model, is the pure tensor of its coefficient and the integral basis vector. -/
theorem extendedBlockCoordinates_symm_single (φ : R →+* S) (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) (n : ℤ)
    (i : blockIndex m₁ m₂ m₃ n) (c : S) :
    letI : Algebra R S := φ.toAlgebra
    (extendedBlockCoordinates φ B₁ B₂ B₃ n).symm
        ((blockCoordinates (B₁.map φ) (B₂.map φ) (B₃.map φ) n).symm (Pi.single i c)) =
      c ⊗ₜ[R] (blockCoordinates B₁ B₂ B₃ n).symm (Pi.single i 1) := by
  let _ : Algebra R S := φ.toAlgebra
  change (((LinearEquiv.baseChange R S _ _ (blockCoordinates B₁ B₂ B₃ n)).trans
    (TensorProduct.piScalarRight R S S _)).trans
      (blockCoordinates (B₁.map φ) (B₂.map φ) (B₃.map φ) n).symm).symm _ = _
  rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_trans_apply, TensorProduct.piScalarRight_symm_single,
    LinearEquiv.symm_apply_eq, LinearEquiv.baseChange_tmul, LinearEquiv.apply_symm_apply]

/-- PROVED: the free-line vector of degree one of the block model in coordinates. -/
theorem blockCoordinates_symm_one (B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (B₂ : Matrix (Fin m₂) (Fin m₂) S) (B₃ : Matrix (Fin m₃) (Fin m₃) S) (c : S) :
    (blockCoordinates B₁ B₂ B₃ 1).symm (Pi.single (Sum.inl () : Unit ⊕ (Fin m₁ ⊕ Fin m₂)) c) =
      ((c, 0, 0) : S × (Fin m₁ → S) × (Fin m₂ → S)) := by
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  funext k
  rcases k with u | i | j
  · rfl
  · exact Pi.single_eq_of_ne (M := fun _ : Unit ⊕ (Fin m₁ ⊕ Fin m₂) => S) (by simp) c
  · exact Pi.single_eq_of_ne (M := fun _ : Unit ⊕ (Fin m₁ ⊕ Fin m₂) => S) (by simp) c

/-- PROVED: the free-line vector of degree two of the block model in coordinates. -/
theorem blockCoordinates_symm_two (B₁ : Matrix (Fin m₁) (Fin m₁) S)
    (B₂ : Matrix (Fin m₂) (Fin m₂) S) (B₃ : Matrix (Fin m₃) (Fin m₃) S) (c : S) :
    (blockCoordinates B₁ B₂ B₃ 2).symm (Pi.single (Sum.inl () : Unit ⊕ (Fin m₂ ⊕ Fin m₃)) c) =
      ((c, 0, 0) : S × (Fin m₂ → S) × (Fin m₃ → S)) := by
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  funext k
  rcases k with u | i | j
  · rfl
  · exact Pi.single_eq_of_ne (M := fun _ : Unit ⊕ (Fin m₂ ⊕ Fin m₃) => S) (by simp) c
  · exact Pi.single_eq_of_ne (M := fun _ : Unit ⊕ (Fin m₂ ⊕ Fin m₃) => S) (by simp) c

end LineCoordinates

/-! ### The retained free generators and the functional (A5) -/

section RetainedLines

open ZInQ.Contrib.RC53Assist.CalibrationModel ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)

variable {S : Type} [CommRing S] {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ}

/-- Definition: the retained free generator of degree one. -/
def e₁R (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) :
    (retainedCentralComplex G hfinite).X 1 :=
  (retainedCentralCoordinates G hfinite H 1).symm
    (Pi.single (Sum.inl () : Unit ⊕ (Fin _ ⊕ Fin _)) 1)

/-- Definition: the retained free generator of degree two. -/
def e₂R (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) :
    (retainedCentralComplex G hfinite).X 2 :=
  (retainedCentralCoordinates G hfinite H 2).symm
    (Pi.single (Sum.inl () : Unit ⊕ (Fin _ ⊕ Fin _)) 1)

/-- Definition: the pure tensor `s ⊗ x` in the base change of an integral complex. -/
def bcTmul {R : Type} [CommRing R] (φ : R →+* S) (C : CochainComplex (ModuleCat.{0} R) ℤ)
    (n : ℤ) (s : S) (x : C.X n) : (ofCC (scalarChangedComplex φ C)).X n := by
  letI : Algebra R S := φ.toAlgebra
  exact s ⊗ₜ[R] x

/-- PROVED: `s ⊗ x = s • (1 ⊗ x)`. -/
theorem bcTmul_smul {R : Type} [CommRing R] (φ : R →+* S)
    (C : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℤ) (s : S) (x : C.X n) :
    bcTmul φ C n s x = s • bcTmul φ C n 1 x := by
  let _ : Algebra R S := φ.toAlgebra
  change s ⊗ₜ[R] x = s • ((1 : S) ⊗ₜ[R] x)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- **A5.** Definition: the base change `s ⊗ x ↦ s · φ (λ₀ x)` of an integral functional on the
degree-two term of the retained complex. -/
def retainedKMFunctional (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (φ : ℤ_[2] →+* S) (lam0 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2]) :
    (ofCC (scalarChangedComplex φ (retainedCentralComplex G hfinite))).X 2 →ₗ[S] S := by
  letI : Algebra ℤ_[2] S := φ.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid ℤ_[2] S S).toLinearMap ∘ₗ (lam0.baseChange S)

/-- PROVED: the base-changed functional on a pure tensor. -/
theorem retainedKMFunctional_tmul (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (φ : ℤ_[2] →+* S) (lam0 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2]) (s : S)
    (x : (retainedCentralComplex G hfinite).X 2) :
    retainedKMFunctional G hfinite φ lam0 (bcTmul φ _ 2 s x) = s * φ (lam0 x) := by
  let _ : Algebra ℤ_[2] S := φ.toAlgebra
  change (TensorProduct.AlgebraTensorModule.rid ℤ_[2] S S) ((lam0.baseChange S) (s ⊗ₜ[ℤ_[2]] x))
    = _
  rw [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def,
    mul_comm]
  rfl

/-- PROVED: the retained block isomorphism on a basis vector of the reduced block model. -/
theorem retainedBlockIso_single (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (φ : ℤ_[2] →+* S) (n : ℤ)
    (i : blockIndex (chosenPresentations (compactCentralComplex G) hfinite 1).relations
      (chosenPresentations (compactCentralComplex G) hfinite 2).relations
      (chosenPresentations (compactCentralComplex G) hfinite 3).relations n) (c : S) :
    ((retainedBlockIso G hfinite H φ).hom.f n).hom
        ((blockCoordinates ((centralDiskMatrix G hfinite 1).map φ)
          ((centralDiskMatrix G hfinite 2).map φ) ((centralDiskMatrix G hfinite 3).map φ) n).symm
            (Pi.single i c)) =
      bcTmul φ _ n c (((retainedCentralNormalization G hfinite H).hom.f n).hom
        ((blockCoordinates (centralDiskMatrix G hfinite 1) (centralDiskMatrix G hfinite 2)
          (centralDiskMatrix G hfinite 3) n).symm (Pi.single i 1))) := by
  let _ : Algebra ℤ_[2] S := φ.toAlgebra
  refine (congrArg (fun p => ((ModuleCat.extendScalars φ).map
    ((retainedCentralNormalization G hfinite H).hom.f n)).hom p)
      (extendedBlockCoordinates_symm_single φ _ _ _ n i c)).trans ?_
  exact ModuleCat.ExtendScalars.map_tmul φ _ c _

/-- **A5.** PROVED: the base-changed functional on the image of a degree-two model vector:
`λ (φ (vec2 y)) = φ (λ₀ e₂R) · y e₂'`. -/
theorem retainedKMFunctional_map (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (φ : ℤ_[2] →+* S)
    (δ₁ δ₂ δ₃ : S) (lam0 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2])
    (y : ((Fin 1 ⊕ Empty) ⊕ Unit) ⊕ Unit → S) :
    retainedKMFunctional G hfinite φ lam0
        ((retainedKMMap G hfinite H φ δ₁ δ₂ δ₃).f 2 2 rfl ⟨vec2 y, vec2_mem _ _⟩) =
      φ (lam0 (e₂R G hfinite H)) * y ke₂' := by
  have h1 : (retainedKMMap G hfinite H φ δ₁ δ₂ δ₃).f 2 2 rfl ⟨vec2 y, vec2_mem _ _⟩ =
      ((retainedBlockIso G hfinite H φ).hom.f 2).hom
        ((blockCoordinates ((centralDiskMatrix G hfinite 1).map φ)
          ((centralDiskMatrix G hfinite 2).map φ) ((centralDiskMatrix G hfinite 3).map φ) 2).symm
            (Pi.single (Sum.inl () : Unit ⊕ (Fin _ ⊕ Fin _)) (y ke₂'))) :=
    congrArg (fun p => ((retainedBlockIso G hfinite H φ).hom.f 2).hom p)
      (blockCoordinates_symm_two _ _ _ (y ke₂')).symm
  exact (congrArg (retainedKMFunctional G hfinite φ lam0) h1).trans
    ((congrArg (retainedKMFunctional G hfinite φ lam0)
      (retainedBlockIso_single G hfinite H φ 2 _ (y ke₂'))).trans
        ((retainedKMFunctional_tmul G hfinite φ lam0 _ _).trans (mul_comm _ _)))

/-- **A5.** PROVED: the image of the model class is `z 0 · (1 ⊗ e₁R)`. -/
theorem retainedKMMap_one (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (φ : ℤ_[2] →+* S)
    (δ₁ δ₂ δ₃ : S) (z : Fin 1 → S) :
    (retainedKMMap G hfinite H φ δ₁ δ₂ δ₃).f 1 1 rfl ⟨vec1 (kz z), vec1_mem _ _⟩ =
      z 0 • bcTmul φ _ 1 1 (e₁R G hfinite H) := by
  have h1 : (retainedKMMap G hfinite H φ δ₁ δ₂ δ₃).f 1 1 rfl ⟨vec1 (kz z), vec1_mem _ _⟩ =
      ((retainedBlockIso G hfinite H φ).hom.f 1).hom
        ((blockCoordinates ((centralDiskMatrix G hfinite 1).map φ)
          ((centralDiskMatrix G hfinite 2).map φ) ((centralDiskMatrix G hfinite 3).map φ) 1).symm
            (Pi.single (Sum.inl () : Unit ⊕ (Fin _ ⊕ Fin _)) (z 0))) :=
    congrArg (fun p => ((retainedBlockIso G hfinite H φ).hom.f 1).hom p)
      (blockCoordinates_symm_one _ _ _ (z 0)).symm
  exact h1.trans ((retainedBlockIso_single G hfinite H φ 1 _ (z 0)).trans
    (bcTmul_smul φ _ 1 (z 0) _))

end RetainedLines

/-! ### Cycles of the base-changed block model (A6) -/

section CycleCoboundary

open ZInQ.Manuscript.RC53Assist.CentralSelmer

variable {R S : Type} [CommRing R] [CommRing S] {m₁ m₂ m₃ : ℕ}

/-- Definition: the base change of an integral block normalization `N : blockComplex B ≅ P`. -/
def blockBaseIso (φ : R →+* S) {B₁ : Matrix (Fin m₁) (Fin m₁) R}
    {B₂ : Matrix (Fin m₂) (Fin m₂) R} {B₃ : Matrix (Fin m₃) (Fin m₃) R}
    {P : CochainComplex (ModuleCat.{0} R) ℤ} (N : blockComplex B₁ B₂ B₃ ≅ P) :
    blockComplex (B₁.map φ) (B₂.map φ) (B₃.map φ) ≅ scalarChangedComplex φ P :=
  (blockScalarChangeIso φ _ _ _).symm ≪≫
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso N

/-- Definition: a degree-one element of the block model as a triple. -/
def blockVec1 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) (x : (blockComplex B₁ B₂ B₃).X 1) :
    R × (Fin m₁ → R) × (Fin m₂ → R) := x

/-- PROVED: the base-change coordinates of a pure tensor. -/
theorem extendedBlockCoordinates_tmul (φ : R →+* S) (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) (n : ℤ) (s : S)
    (x : (blockComplex B₁ B₂ B₃).X n) :
    letI : Algebra R S := φ.toAlgebra
    extendedBlockCoordinates φ B₁ B₂ B₃ n (s ⊗ₜ[R] x) =
      (blockCoordinates (B₁.map φ) (B₂.map φ) (B₃.map φ) n).symm
        (fun k => φ (blockCoordinates B₁ B₂ B₃ n x k) * s) := by
  let _ : Algebra R S := φ.toAlgebra
  change (blockCoordinates (B₁.map φ) (B₂.map φ) (B₃.map φ) n).symm
    (TensorProduct.piScalarRight R S S _
      (LinearEquiv.baseChange R S _ _ (blockCoordinates B₁ B₂ B₃ n) (s ⊗ₜ[R] x))) = _
  rw [LinearEquiv.baseChange_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
  rfl

/-- **A6 (generic).** PROVED: for an integral block normalization `N : blockComplex B ≅ P` and a
degree-one cycle `z₀` of `P`, if the base-changed first two disk determinants are units then
`1 ⊗ z₀ − φ(a₀) · (1 ⊗ e₁)` is a coboundary of the base change of `P`, where `a₀` is the
free coordinate of `z₀` and `e₁` the free generator. -/
theorem block_cycle_coboundary (φ : R →+* S) (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R)
    {P : CochainComplex (ModuleCat.{0} R) ℤ} (N : blockComplex B₁ B₂ B₃ ≅ P)
    (hB₁ : IsUnit (B₁.map φ).det) (hB₂ : IsUnit (B₂.map φ).det) (z0 : P.X 1)
    (hz : (P.d 1 2).hom z0 = 0) :
    ∃ w : (scalarChangedComplex φ P).X 0,
      ((scalarChangedComplex φ P).d 0 1).hom w =
        bcTmul φ P 1 1 z0 - φ (blockCoordinates B₁ B₂ B₃ 1 ((N.inv.f 1).hom z0) (Sum.inl ())) •
          bcTmul φ P 1 1 ((N.hom.f 1).hom
            ((blockCoordinates B₁ B₂ B₃ 1).symm (Pi.single (Sum.inl ()) 1))) := by
  let pp := blockVec1 B₁ B₂ B₃ ((N.inv.f 1).hom z0)
  -- the disk component of the cycle
  have hc : blockD1 B₂ ((N.inv.f 1).hom z0) = 0 :=
    (LinearMap.congr_fun (blockComplex_d1 B₁ B₂ B₃) _).symm.trans
      ((congrArg (fun g => g.hom z0) (N.inv.comm 1 2)).trans
        ((congrArg (N.inv.f 2).hom hz).trans (map_zero _)))
  have hv : B₂ *ᵥ pp.2.2 = 0 := congrArg (fun q : R × (Fin m₂ → R) × (Fin m₃ → R) => q.2.1) hc
  have hφv : ∀ j, φ (pp.2.2 j) = 0 := by
    have h1 : (B₂.map φ) *ᵥ (φ ∘ pp.2.2) = 0 := by
      funext i
      rw [← RingHom.map_mulVec, hv]
      simp
    have h2 : φ ∘ pp.2.2 = 0 := by
      calc φ ∘ pp.2.2 = ((B₂.map φ)⁻¹ * B₂.map φ) *ᵥ (φ ∘ pp.2.2) := by
            rw [nonsing_inv_mul _ hB₂, one_mulVec]
        _ = 0 := by rw [← mulVec_mulVec, h1, mulVec_zero]
    exact fun j => congrFun h2 j
  -- the target in reduced block coordinates
  let I := blockBaseIso φ N
  let c : S := φ (blockCoordinates B₁ B₂ B₃ 1 ((N.inv.f 1).hom z0) (Sum.inl ()))
  let q := (blockCoordinates B₁ B₂ B₃ 1).symm
    (Pi.single (Sum.inl () : Unit ⊕ (Fin m₁ ⊕ Fin m₂)) 1)
  have k1 : (I.inv.f 1).hom (bcTmul φ P 1 1 z0) =
      (blockCoordinates (B₁.map φ) (B₂.map φ) (B₃.map φ) 1).symm
        (fun k => φ (blockCoordinates B₁ B₂ B₃ 1 ((N.inv.f 1).hom z0) k) * 1) := by
    let _ : Algebra R S := φ.toAlgebra
    exact (congrArg (extendedBlockCoordinates φ B₁ B₂ B₃ 1)
      (ModuleCat.ExtendScalars.map_tmul φ (N.inv.f 1) 1 z0)).trans
        (extendedBlockCoordinates_tmul φ B₁ B₂ B₃ 1 1 _)
  have hq : (N.inv.f 1).hom ((N.hom.f 1).hom q) = q := by
    change (N.hom.f 1 ≫ N.inv.f 1).hom q = q
    rw [← HomologicalComplex.comp_f, N.hom_inv_id, HomologicalComplex.id_f]
    rfl
  have k2 : (I.inv.f 1).hom (bcTmul φ P 1 1 ((N.hom.f 1).hom q)) =
      (blockCoordinates (B₁.map φ) (B₂.map φ) (B₃.map φ) 1).symm
        (Pi.single (Sum.inl () : Unit ⊕ (Fin m₁ ⊕ Fin m₂)) 1) := by
    let _ : Algebra R S := φ.toAlgebra
    refine (congrArg (extendedBlockCoordinates φ B₁ B₂ B₃ 1)
      ((ModuleCat.ExtendScalars.map_tmul φ (N.inv.f 1) 1 _).trans
        (congrArg (fun x => (1 : S) ⊗ₜ[R] x) hq))).trans ?_
    exact ((LinearEquiv.symm_apply_eq _).1
      (extendedBlockCoordinates_symm_single φ B₁ B₂ B₃ 1 _ 1)).symm
  have key : (I.inv.f 1).hom (bcTmul φ P 1 1 z0 - c • bcTmul φ P 1 1 ((N.hom.f 1).hom q)) =
      ((0, fun i => φ (pp.2.1 i), 0) : S × (Fin m₁ → S) × (Fin m₂ → S)) := by
    have hs : (I.inv.f 1).hom (bcTmul φ P 1 1 z0 - c • bcTmul φ P 1 1 ((N.hom.f 1).hom q)) =
        (I.inv.f 1).hom (bcTmul φ P 1 1 z0) -
          c • (I.inv.f 1).hom (bcTmul φ P 1 1 ((N.hom.f 1).hom q)) :=
      ((I.inv.f 1).hom.map_sub _ _).trans (congrArg _ ((I.inv.f 1).hom.map_smul _ _))
    rw [hs, k1, k2, ← map_smul, ← map_sub]
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    funext k
    rcases k with u | i | j
    · change φ pp.1 * 1 - φ pp.1 * Pi.single (M := fun _ : Unit ⊕ (Fin m₁ ⊕ Fin m₂) => S)
        (Sum.inl ()) 1 (Sum.inl u) = 0
      simp
    · change φ (pp.2.1 i) * 1 - φ pp.1 * Pi.single (M := fun _ : Unit ⊕ (Fin m₁ ⊕ Fin m₂) => S)
        (Sum.inl ()) 1 (Sum.inr (Sum.inl i)) = φ (pp.2.1 i)
      simp
    · change φ (pp.2.2 j) * 1 - φ pp.1 * Pi.single (M := fun _ : Unit ⊕ (Fin m₁ ⊕ Fin m₂) => S)
        (Sum.inl ()) 1 (Sum.inr (Sum.inr j)) = 0
      simp [hφv j]
  -- the primitive
  let w' : Fin m₁ → S := (B₁.map φ)⁻¹ *ᵥ (fun i => φ (pp.2.1 i))
  have hw' : blockD0 (B₁.map φ) w' =
      ((0, fun i => φ (pp.2.1 i), 0) : S × (Fin m₁ → S) × (Fin m₂ → S)) := by
    change ((0 : S), (B₁.map φ) *ᵥ ((B₁.map φ)⁻¹ *ᵥ (fun i => φ (pp.2.1 i))), (0 : Fin m₂ → S)) = _
    rw [mulVec_mulVec, mul_nonsing_inv _ hB₁, one_mulVec]
  refine ⟨(I.hom.f 0).hom w', ?_⟩
  have hd : ((blockComplex (B₁.map φ) (B₂.map φ) (B₃.map φ)).d 0 1).hom w' =
      (I.inv.f 1).hom (bcTmul φ P 1 1 z0 - c • bcTmul φ P 1 1 ((N.hom.f 1).hom q)) :=
    (LinearMap.congr_fun (blockComplex_d0 _ _ _) w').trans (hw'.trans key.symm)
  refine (congrArg (fun g => g.hom w') (I.hom.comm 0 1)).trans ?_
  refine (congrArg (I.hom.f 1).hom hd).trans ?_
  change (I.inv.f 1 ≫ I.hom.f 1).hom _ = _
  rw [← HomologicalComplex.comp_f, I.inv_hom_id, HomologicalComplex.id_f]
  rfl

end CycleCoboundary

section RetainedCycle

open ZInQ.Contrib.RC53Assist.CalibrationModel ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)

variable {S : Type} [CommRing S] {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ}

/-- **A6.** PROVED: for a degree-one cycle `z₀` of the retained complex with free coordinate
`a₀`, if the base-changed first two disk determinants are units then
`1 ⊗ z₀ − φ(a₀) · (1 ⊗ e₁R)` is a coboundary of the base-changed retained complex. -/
theorem retained_cycle_coboundary (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (φ : ℤ_[2] →+* S)
    (hd₁ : IsUnit (φ (centralDiskMatrix G hfinite 1).det))
    (hd₂ : IsUnit (φ (centralDiskMatrix G hfinite 2).det))
    (z0 : (retainedCentralComplex G hfinite).X 1)
    (hz : ((retainedCentralComplex G hfinite).d 1 2).hom z0 = 0) :
    ∃ w : (scalarChangedComplex φ (retainedCentralComplex G hfinite)).X 0,
      ((scalarChangedComplex φ (retainedCentralComplex G hfinite)).d 0 1).hom w =
        bcTmul φ _ 1 1 z0 - φ (retainedCentralCoordinates G hfinite H 1 z0 (Sum.inl ())) •
          bcTmul φ _ 1 1 (e₁R G hfinite H) :=
  block_cycle_coboundary φ _ _ _ (retainedCentralNormalization G hfinite H)
    (isUnit_det_map φ _ hd₁) (isUnit_det_map φ _ hd₂) z0 hz

end RetainedCycle

/-! ### Non-vacuity (A7) -/

section Example

/-- PROVED: `2` is a unit of `ℚ`. -/
theorem isUnit_two_rat : IsUnit (2 : ℚ) := isUnit_iff_ne_zero.2 two_ne_zero

/-- PROVED: the `1 × 1` matrix `(2)` over `ℚ` has unit determinant. -/
theorem isUnit_det_two_rat : IsUnit (!![2] : Matrix (Fin 1) (Fin 1) ℚ).det := by
  rw [det_fin_one_of]
  exact isUnit_two_rat

/-- **A7.** PROVED (non-vacuity of A2): over `ℚ` with `m₁ = m₂ = m₃ = 1`, `Bⱼ = (2)` and
`δⱼ = 2`, the hypotheses of `kmBlockMap_quasiIso` hold and the comparison map is a
quasi-isomorphism. -/
theorem kmBlockMap_quasiIso_example :
    QuasiIso (GHom.toCC (kmBlockMap (2 : ℚ) 2 2 !![2] !![2] !![2])) :=
  kmBlockMap_quasiIso isUnit_two_rat isUnit_two_rat isUnit_two_rat isUnit_det_two_rat
    isUnit_det_two_rat isUnit_det_two_rat

/-- **A7.** PROVED (non-vacuity of A3): in the example, the model class `vec1 (kz 1)` maps to
the free generator `(1, 0, 0)`, and `vec2 (kw 1)` to `(1, 0, 0)`; in particular the comparison map
is nonzero in degrees one and two. -/
theorem kmBlockMap_example_values :
    (kmBlockMap (2 : ℚ) 2 2 !![2] !![2] !![2]).f 1 1 rfl ⟨vec1 (kz 1), vec1_mem _ _⟩ =
        ((1, 0, 0) : ℚ × (Fin 1 → ℚ) × (Fin 1 → ℚ)) ∧
      (kmBlockMap (2 : ℚ) 2 2 !![2] !![2] !![2]).f 2 2 rfl ⟨vec2 (kw 1), vec2_mem _ _⟩ =
        ((1, 0, 0) : ℚ × (Fin 1 → ℚ) × (Fin 1 → ℚ)) :=
  ⟨kmBlockMap_one _ _ _ _ _ _ 1, kmBlockMap_two _ _ _ _ _ _ (kw 1)⟩

end Example

end ZInQ.Manuscript.RC.Wiring.KmIdent
