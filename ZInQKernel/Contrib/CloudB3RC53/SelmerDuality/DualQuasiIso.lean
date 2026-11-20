import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SupportChange

/-!
# Selmer duality, part 8: over a self-injective ring the termwise dual preserves
# quasi-isomorphisms

For the finite Selmer duality `C_U ≃ RHom_{R_i}(C_{U⊥}, R_i)[−3]` (tex L2806–2830) the termwise
dual `Hom_S(−, S)` (`dualCx`) is used as `RHom_S(−, S)`. Over a self-injective ring `S`
(`Module.Injective S S`; the coefficient rings `A_i` are, `acoef_selfInjective`) the functor
`Hom_S(−, S)` is exact, and this file proves the consequence that makes the termwise dual a model of
`RHom`: it carries quasi-isomorphisms to quasi-isomorphisms (`dualHom_quasiIso`).

Proof.
* `dualCx_acyclic`: the dual of an acyclic complex is acyclic (a linear form vanishing on the
  boundaries vanishes on the cycles, factors through the image of the differential and extends,
  by injectivity of `S`).
* `coneCx_acyclic_of_quasiIso`: `f` is a quasi-isomorphism ⇒ its cone `Cone(f)[−1]` (`coneCx f`)
  is acyclic: the degreewise split sequence `0 → B[−1] → Cone(f)[−1] → A → 0` maps to the one for
  `id_B`, whose cone is acyclic, and the middle five lemma `quasiIso_τ₂` applies.
* Dualizing these two sequences (degreewise split, so still short exact) gives a morphism of short
  exact sequences `0 → D(B) → D(Cone(id)) → D(B[−1]) → 0` to `0 → D(A) → D(Cone(f)) → D(B[−1]) → 0`
  with acyclic middle terms and identity third term, so its first component `D(f)` is a
  quasi-isomorphism by the five lemma for the first term (`quasiIso_τ₁`).

**Classification.** GLUE, PROVED.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.CloudB3RC53.SelmerDuality

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional HomologicalComplex

universe u

variable {S : Type u} [CommRing S]

/-! ### Acyclicity -/

/-- Acyclicity of a relation-indexed complex: every cycle is a boundary. -/
def GAcyclic (C : GCx S) : Prop :=
  ∀ i j k (hij : i + 1 = j) (hjk : j + 1 = k) (x : C.X j), C.d j k hjk x = 0 →
    ∃ y, C.d i j hij y = x

theorem acyclic_toCC_iff (C : GCx S) : C.toCC.Acyclic ↔ GAcyclic C := by
  constructor
  · intro h i j k hij hjk x hx
    subst hij hjk
    have hj := h (i + 1)
    rw [exactAt_iff' _ i (i + 1) (i + 1 + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at hj
    obtain ⟨y, hy⟩ := hj x ((GCx.toCC_d_hom C (i + 1) (i + 1 + 1) rfl x).trans hx)
    exact ⟨y, (GCx.toCC_d_hom C i (i + 1) rfl y).symm.trans hy⟩
  · intro h j
    rw [exactAt_iff' _ (j - 1) j (j + 1) (by simp) (by simp), ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' : C.d j (j + 1) rfl x = 0 := (GCx.toCC_d_hom C j (j + 1) rfl x).symm.trans hx
    obtain ⟨y, hy⟩ := h (j - 1) j (j + 1) (by omega) rfl x hx'
    exact ⟨y, (GCx.toCC_d_hom C (j - 1) j (by omega) y).trans hy⟩

/-- A quasi-isomorphism into an acyclic complex has acyclic source. -/
theorem acyclic_of_quasiIso_of_acyclic {K L : CochainComplex (ModuleCat.{u} S) ℤ} (φ : K ⟶ L)
    (hφ : QuasiIso φ) (hL : L.Acyclic) : K.Acyclic := fun i =>
  (quasiIsoAt_iff_exactAt' φ i (hL i)).1 inferInstance

/-- A map between acyclic complexes is a quasi-isomorphism. -/
theorem quasiIso_of_acyclic {K L : CochainComplex (ModuleCat.{u} S) ℤ} (φ : K ⟶ L)
    (hK : K.Acyclic) (hL : L.Acyclic) : QuasiIso φ := by
  rw [quasiIso_iff]
  intro i
  exact (quasiIsoAt_iff_exactAt φ i (hK i)).2 (hL i)

/-! ### The dual of an acyclic complex -/

/-- **Over a self-injective ring the dual of an acyclic complex is acyclic.** -/
theorem dualCx_acyclic [Module.Injective S S] (C : GCx S) (hC : GAcyclic C) (m : ℤ) :
    GAcyclic (dualCx C m) := by
  intro i j k hij hjk φ hφ
  -- `φ` kills the boundaries `d(C^{m−k}) ⊆ C^{m−j}`
  have hkill : ∀ x : C.X (m - k), asDual φ (C.d (m - k) (m - j) (by omega) x) = 0 := by
    intro x
    have := congrArg (fun χ => asDual χ x) hφ
    change (-(sgn j)) • asDual φ (C.d (m - k) (m - j) _ x) = 0 at this
    have h2 := congrArg (fun z : S => (-(sgn j)) • z) this
    simp only [smul_smul, neg_mul_neg, sgn_mul_self, one_smul, smul_zero] at h2
    exact h2
  -- hence `φ` kills the kernel of `d_out : C^{m−j} → C^{m−i}`
  set dout := C.d (m - j) (m - i) (by omega) with hdout
  have hker : LinearMap.ker dout ≤ LinearMap.ker (asDual φ) := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    obtain ⟨x, rfl⟩ := hC (m - k) (m - j) (m - i) (by omega) (by omega) z hz
    exact hkill x
  -- factor through the range and extend
  let g : LinearMap.range dout →ₗ[S] S :=
    ((LinearMap.ker dout).liftQ (asDual φ) hker).comp (dout.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨h, hh⟩ := Module.Injective.out (R := S) (Q := S) (LinearMap.range dout).subtype
    (Submodule.injective_subtype _) g
  refine ⟨(-(sgn i)) • h, dualCx_ext fun z => ?_⟩
  change (-(sgn i)) • (((-(sgn i)) • h) (dout z)) = asDual φ z
  rw [LinearMap.smul_apply, smul_smul, neg_mul_neg, sgn_mul_self, one_smul]
  have := hh ⟨dout z, LinearMap.mem_range_self dout z⟩
  rw [Submodule.subtype_apply] at this
  rw [this]
  change ((LinearMap.ker dout).liftQ (asDual φ) hker)
    (dout.quotKerEquivRange.symm ⟨dout z, _⟩) = asDual φ z
  rw [show (⟨dout z, LinearMap.mem_range_self dout z⟩ : LinearMap.range dout) =
    dout.quotKerEquivRange (Submodule.Quotient.mk z) from rfl, LinearEquiv.symm_apply_apply,
    Submodule.liftQ_apply]

/-! ### Transport along identities -/

theorem idGHom_f_f (B : GCx S) (i j k : ℤ) (h : i = j) (h' : j = k) (x : B.X i) :
    (idGHom B).f j k h' ((idGHom B).f i j h x) = (idGHom B).f i k (h.trans h') x := by
  subst h h'; rfl

theorem idGHom_f_self (B : GCx S) (i : ℤ) (h : i = i) (x : B.X i) : (idGHom B).f i i h x = x :=
  rfl

theorem idGHom_f_comp {A B : GCx S} (g : GHom A B) (i k : ℤ) (h : i = k) (a : A.X i) :
    (idGHom B).f i k h (g.f i i rfl a) = g.f i k h a := by
  subst h; rfl

theorem toCC_idGHom (X : GCx S) : GHom.toCC (idGHom X) = 𝟙 _ := by
  ext i x; rfl

theorem toCC_dualHom_idGHom (X : GCx S) (m : ℤ) : GHom.toCC (dualHom (idGHom X) m) = 𝟙 _ := by
  ext i φ
  exact dualCx_ext fun x => rfl

/-! ### Cones -/

/-- `B[−1]`: `X n = B^{n−1}`, `d = −d_B`. -/
def shiftDown (B : GCx S) : GCx S where
  X n := B.X (n - 1)
  d i j h := -(B.d (i - 1) (j - 1) (by omega))
  d_d i j k hij hjk x := by
    change -(B.d (j - 1) (k - 1) _ (-(B.d (i - 1) (j - 1) _ x))) = 0
    rw [map_neg, neg_neg, B.d_d]

variable {A B : GCx S} (f : GHom A B)

/-- `B[−1] → Cone(f)[−1]`, `b ↦ (0, b)`. -/
def coneIncl : GHom (shiftDown B) (coneCx f) where
  f i j h := h ▸ LinearMap.inr S (A.X i) (B.X (i - 1))
  comm i i₁ j j₁ hij h₁ h₂ hj b := by
    subst hij hj
    change ((0 : A.X i₁), -(B.d (i - 1) (i₁ - 1) _ b)) =
      (A.d i i₁ h₂ 0, f.f i (i₁ - 1) _ 0 - B.d (i - 1) (i₁ - 1) _ b)
    simp

/-- `Cone(f)[−1] → A`, `(a, b) ↦ a`. -/
def coneProj : GHom (coneCx f) A where
  f i j h := h ▸ LinearMap.fst S (A.X i) (B.X (i - 1))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    rfl

/-- `Cone(f)[−1] → Cone(id_B)[−1]`, `(a, b) ↦ (f a, b)`. -/
def coneToId : GHom (coneCx f) (coneCx (idGHom B)) where
  f i j h := h ▸ (f.f i i rfl).prodMap (LinearMap.id : B.X (i - 1) →ₗ[S] B.X (i - 1))
  comm i i₁ j j₁ hij h₁ h₂ hj c := by
    subst hij hj
    obtain ⟨a, b⟩ := c
    change (f.f i₁ i₁ rfl (A.d i i₁ h₁ a), f.f i (i₁ - 1) _ a - B.d (i - 1) (i₁ - 1) _ b) =
      (B.d i i₁ h₂ (f.f i i rfl a),
        (idGHom B).f i (i₁ - 1) _ (f.f i i rfl a) - B.d (i - 1) (i₁ - 1) _ b)
    rw [f.comm i i₁ i i₁ rfl h₁ h₂ rfl a, idGHom_f_comp]

omit f in
/-- The cone of the identity is acyclic. -/
theorem coneCx_id_acyclic (B : GCx S) : GAcyclic (coneCx (idGHom B)) := by
  intro i j k hij hjk c hc
  obtain ⟨b, b'⟩ := c
  have h2 : (idGHom B).f j (k - 1) (by omega) b = B.d (j - 1) (k - 1) (by omega) b' := by
    have := congrArg Prod.snd hc
    exact sub_eq_zero.mp this
  refine ⟨((idGHom B).f (j - 1) i (by omega) b', 0), ?_⟩
  change (B.d i j hij ((idGHom B).f (j - 1) i _ b'),
    (idGHom B).f i (j - 1) _ ((idGHom B).f (j - 1) i _ b') - B.d (i - 1) (j - 1) _ 0) = (b, b')
  rw [idGHom_f_f, idGHom_f_self, map_zero, sub_zero]
  refine Prod.ext ?_ rfl
  have hc' := (idGHom B).comm (j - 1) (k - 1) i j (by omega) (by omega) hij (by omega) b'
  change B.d i j hij ((idGHom B).f (j - 1) i _ b') = b
  rw [← hc', ← h2, idGHom_f_f, idGHom_f_self]

/-- The short complex `B[−1] → Cone(f)[−1] → A`. -/
def coneSES : ShortComplex (CochainComplex (ModuleCat.{u} S) ℤ) :=
  ShortComplex.mk (GHom.toCC (coneIncl f)) (GHom.toCC (coneProj f)) (by
    rw [GHom.toCC_comp]
    ext i c
    rfl)

theorem coneSES_shortExact : (coneSES f).ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro c hc
    obtain ⟨a, b⟩ := c
    change a = 0 at hc
    subst hc
    exact ⟨b, rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    intro b b' h
    change ((0 : A.X i), b) = (0, b') at h
    exact (Prod.mk.injEq _ _ _ _ ▸ h).2
  · rw [ModuleCat.epi_iff_surjective]
    intro a
    exact ⟨(a, 0), rfl⟩

/-- The morphism of sequences `(id, coneToId, f)`. -/
def coneSESHom : coneSES f ⟶ coneSES (idGHom B) where
  τ₁ := GHom.toCC (idGHom (shiftDown B))
  τ₂ := GHom.toCC (coneToId f)
  τ₃ := GHom.toCC f
  comm₁₂ := by
    change GHom.toCC (idGHom (shiftDown B)) ≫ GHom.toCC (coneIncl (idGHom B)) =
      GHom.toCC (coneIncl f) ≫ GHom.toCC (coneToId f)
    rw [GHom.toCC_comp, GHom.toCC_comp]
    refine GHom.toCC_ext fun i b => ?_
    change ((0 : B.X i), b) = (f.f i i rfl 0, b)
    rw [map_zero]
  comm₂₃ := by
    change GHom.toCC (coneToId f) ≫ GHom.toCC (coneProj (idGHom B)) =
      GHom.toCC (coneProj f) ≫ GHom.toCC f
    rw [GHom.toCC_comp, GHom.toCC_comp]
    exact GHom.toCC_ext fun i c => rfl

/-- **A quasi-isomorphism has acyclic cone.** -/
theorem coneCx_acyclic_of_quasiIso (hf : QuasiIso (GHom.toCC f)) : GAcyclic (coneCx f) := by
  have h1 : QuasiIso (coneSESHom f).τ₁ := by
    change QuasiIso (GHom.toCC (idGHom (shiftDown B)))
    rw [toCC_idGHom]
    infer_instance
  have h2 : QuasiIso (coneSESHom f).τ₂ :=
    quasiIso_τ₂ (coneSESHom f) (coneSES_shortExact f) (coneSES_shortExact _) h1 hf
  have hid : (coneCx (idGHom B)).toCC.Acyclic := (acyclic_toCC_iff _).2 (coneCx_id_acyclic B)
  exact (acyclic_toCC_iff _).1 (acyclic_of_quasiIso_of_acyclic (coneSESHom f).τ₂ h2 hid)

/-! ### Dualizing the cone sequences -/

/-- The dual short complex `D(A) → D(Cone(f)[−1]) → D(B[−1])`. -/
def dualConeSES (m : ℤ) : ShortComplex (CochainComplex (ModuleCat.{u} S) ℤ) :=
  ShortComplex.mk (GHom.toCC (dualHom (coneProj f) m)) (GHom.toCC (dualHom (coneIncl f) m)) (by
    rw [GHom.toCC_comp]
    ext i φ
    refine dualCx_ext fun b => ?_
    change asDual φ (0 : A.X (m - i)) = 0
    rw [map_zero])

theorem dualConeSES_shortExact (m : ℤ) : (dualConeSES f m).ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro φ hφ
    refine ⟨(LinearMap.inl S (A.X (m - i)) (B.X (m - i - 1))).dualMap (asDual φ),
      dualCx_ext fun c => ?_⟩
    obtain ⟨a, b⟩ := c
    have h0 := congrArg (fun χ => asDual χ b) hφ
    change asDual φ ((0 : A.X (m - i)), b) = 0 at h0
    change asDual φ (a, 0) = asDual φ (a, b)
    have : ((a, b) : (coneCx f).X (m - i)) = (a, 0) + (0, b) := by simp
    rw [this]
    erw [map_add]
    rw [h0, add_zero]
  · rw [ModuleCat.mono_iff_injective]
    intro φ ψ h
    refine dualCx_ext fun a => ?_
    have := congrArg (fun χ => asDual χ ((a, 0) : (coneCx f).X (m - i))) h
    exact this
  · rw [ModuleCat.epi_iff_surjective]
    intro ψ
    refine ⟨(LinearMap.snd S (A.X (m - i)) (B.X (m - i - 1))).dualMap (asDual ψ),
      dualCx_ext fun b => ?_⟩
    rfl

/-- The morphism of dual sequences `(D f, D coneToId, id)`. -/
def dualConeSESHom (m : ℤ) : dualConeSES (idGHom B) m ⟶ dualConeSES f m where
  τ₁ := GHom.toCC (dualHom f m)
  τ₂ := GHom.toCC (dualHom (coneToId f) m)
  τ₃ := GHom.toCC (dualHom (idGHom (shiftDown B)) m)
  comm₁₂ := by
    change GHom.toCC (dualHom f m) ≫ GHom.toCC (dualHom (coneProj f) m) =
      GHom.toCC (dualHom (coneProj (idGHom B)) m) ≫ GHom.toCC (dualHom (coneToId f) m)
    rw [GHom.toCC_comp, GHom.toCC_comp]
    exact GHom.toCC_ext fun i φ => dualCx_ext fun c => rfl
  comm₂₃ := by
    change GHom.toCC (dualHom (coneToId f) m) ≫ GHom.toCC (dualHom (coneIncl f) m) =
      GHom.toCC (dualHom (coneIncl (idGHom B)) m) ≫ GHom.toCC (dualHom (idGHom (shiftDown B)) m)
    rw [GHom.toCC_comp, GHom.toCC_comp]
    refine GHom.toCC_ext fun i φ => dualCx_ext fun b => ?_
    change asDual φ (f.f (m - i) (m - i) rfl 0, b) = asDual φ ((0 : B.X (m - i)), b)
    rw [map_zero]

/-! ### The five lemma for the first term -/

open HomologicalComplex HomologySequence ComposableArrows Abelian in
/-- **Two-out-of-three for the first term**: for a morphism `φ` of short exact sequences of
cochain complexes in an abelian category, if `φ.τ₂` and `φ.τ₃` are quasi-isomorphisms, so is
`φ.τ₁`. -/
theorem quasiIso_τ₁ {C : Type*} [Category C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₁ := by
  have i₂ : ∀ n, IsIso (homologyMap φ.τ₂ n) := fun n =>
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  have i₃ : ∀ n, IsIso (homologyMap φ.τ₃ n) := fun n =>
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hrel : ∀ k : ℤ, (ComplexShape.up ℤ).Rel (k - 1) k := fun k => by simp
  have hm : Mono (homologyMap φ.τ₁ n) := by
    have := i₂ (n - 1)
    have := i₃ (n - 1)
    have := i₂ n
    exact mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ (n - 1) n (hrel n)))
      (composableArrows₅_exact hS₁ (n - 1) n (hrel n)).δ₀.δlast
      (composableArrows₅_exact hS₂ (n - 1) n (hrel n)).δ₀.δlast
      (inferInstanceAs (Epi (homologyMap φ.τ₂ (n - 1))))
      (inferInstanceAs (Mono (homologyMap φ.τ₃ (n - 1))))
      (inferInstanceAs (Mono (homologyMap φ.τ₂ n)))
  have he : Epi (homologyMap φ.τ₁ n) := by
    have := i₃ (n - 1)
    have := i₂ n
    have := i₃ n
    exact epi_of_epi_of_epi_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ (n - 1) n (hrel n)))
      (composableArrows₅_exact hS₁ (n - 1) n (hrel n)).δ₀.δ₀
      (composableArrows₅_exact hS₂ (n - 1) n (hrel n)).δ₀.δ₀
      (inferInstanceAs (Epi (homologyMap φ.τ₃ (n - 1))))
      (inferInstanceAs (Epi (homologyMap φ.τ₂ n)))
      (inferInstanceAs (Mono (homologyMap φ.τ₃ n)))
  exact isIso_of_mono_of_epi _

/-! ### The theorem -/

/-- **Over a self-injective ring the termwise dual preserves quasi-isomorphisms**: for a chain map
`f : A → B` with `f` a quasi-isomorphism, `Hom_S(f, S) : Hom_S(B, S)[−m] → Hom_S(A, S)[−m]` is a
quasi-isomorphism. -/
theorem dualHom_quasiIso [Module.Injective S S] (m : ℤ) (hf : QuasiIso (GHom.toCC f)) :
    QuasiIso (GHom.toCC (dualHom f m)) := by
  have hcf : (dualCx (coneCx f) m).toCC.Acyclic :=
    (acyclic_toCC_iff _).2 (dualCx_acyclic _ (coneCx_acyclic_of_quasiIso f hf) m)
  have hcid : (dualCx (coneCx (idGHom B)) m).toCC.Acyclic :=
    (acyclic_toCC_iff _).2 (dualCx_acyclic _ (coneCx_id_acyclic B) m)
  have h2 : QuasiIso (dualConeSESHom f m).τ₂ := quasiIso_of_acyclic _ hcid hcf
  have h3 : QuasiIso (dualConeSESHom f m).τ₃ := by
    change QuasiIso (GHom.toCC (dualHom (idGHom (shiftDown B)) m))
    rw [toCC_dualHom_idGHom]
    infer_instance
  exact quasiIso_τ₁ (dualConeSESHom f m) (dualConeSES_shortExact (idGHom B) m)
    (dualConeSES_shortExact f m) h2 h3

end ZInQ.Contrib.CloudB3RC53.SelmerDuality
