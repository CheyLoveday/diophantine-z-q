import ZInQKernel.Contrib.OneProof.RC.Local.TameFreeModelCochains

/-!
# Lane RC31, round 5: the tame comparison is a quasi-isomorphism in degrees zero and one

Manuscript `diophantine_zq.tex`, tex 3470–3480 (Elliot's tame local free model (4.4)), with the
tame coordinates of tex 3298–3306 and 5026–5037.

* `quasiIso_iff_bijective_homologyMapLin` (PROVED): a morphism of short complexes of modules is
  a quasi-isomorphism iff the induced map `ker g ⧸ im f → ker g ⧸ im f` is bijective (via the
  explicit left homology data and `LeftHomologyMapData.quasiIso_iff`);
  `quasiIso_of_elementwise` and `quasiIsoAt_toCC_of_elementwise` (PROVED) are its elementwise
  forms, the second for `GHom.toCC` of a relation-indexed chain map.
* Degree `0` (PROVED, any `g`, any commutative ring): `quasiIsoAt_tameCochainMap_zero`, and
  `quasiIsoAt_tameCochainMap_zero_local` for the actual local Galois group.
* Negative degrees (PROVED): `quasiIsoAt_tameCochainMap_neg`.
* Degree `1` at `g = 1` over a field (PROVED): `quasiIsoAt_tameCochainMap_one_of_bijective`, and
  `quasiIsoAt_tameCochainMap_one` for the actual local Galois group (from
  `tameH1_bijective_local`).
* `quasiIso_tameCochainMap_of_two_le` (PROVED): at `g = 1`, for the actual local Galois group,
  `QuasiIso (GHom.toCC (tameCochainMap …))` follows from `QuasiIsoAt` in all degrees `≥ 2`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.TameBijective

/-! ### Quasi-isomorphisms of short complexes of modules, elementwise -/

section ShortComplexElementwise

variable {R : Type} [CommRing R] {S₁ S₂ : ShortComplex (ModuleCat.{0} R)}

/-- The induced map on the explicit cycles `ker g` of a morphism of short complexes of modules
(tex 3470–3480). Kind: definition. -/
def cyclesMapLin (φ : S₁ ⟶ S₂) :
    LinearMap.ker S₁.g.hom →ₗ[R] LinearMap.ker S₂.g.hom :=
  φ.τ₂.hom.restrict fun z hz => by
    have e := congrArg (fun t => t.hom z) φ.comm₂₃
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    rw [LinearMap.mem_ker] at hz ⊢
    rw [e, hz, map_zero]

/-- The induced map on the explicit homology `ker g ⧸ im f` (tex 3470–3480). Kind:
definition. -/
def homologyMapLin (φ : S₁ ⟶ S₂) :
    (LinearMap.ker S₁.g.hom ⧸ LinearMap.range S₁.moduleCatToCycles) →ₗ[R]
      (LinearMap.ker S₂.g.hom ⧸ LinearMap.range S₂.moduleCatToCycles) :=
  Submodule.mapQ _ _ (cyclesMapLin φ) (by
    rintro _ ⟨x, rfl⟩
    refine ⟨φ.τ₁.hom x, Subtype.ext ?_⟩
    have e := congrArg (fun t => t.hom x) φ.comm₁₂
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    change S₂.f.hom (φ.τ₁.hom x) = φ.τ₂.hom (S₁.f.hom x)
    exact e)

/-- The left homology map data of a morphism of short complexes of modules, for the explicit
left homology data (tex 3470–3480). Kind: definition. -/
def leftHomologyMapDataLin (φ : S₁ ⟶ S₂) :
    ShortComplex.LeftHomologyMapData φ S₁.moduleCatLeftHomologyData
      S₂.moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom (cyclesMapLin φ)
  φH := ModuleCat.ofHom (homologyMapLin φ)
  commi := by
    ext x
    rfl
  commf' := by
    ext x
    apply Subtype.ext
    have e := congrArg (fun t => t.hom x) φ.comm₁₂
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    change φ.τ₂.hom (S₁.f.hom x) = S₂.f.hom (φ.τ₁.hom x)
    exact e.symm
  commπ := by
    ext x
    rfl

/-- **Elementwise criterion for a quasi-isomorphism of short complexes of modules**
(tex 3470–3480): `φ` is a quasi-isomorphism iff the induced map `ker g ⧸ im f → ker g ⧸ im f`
is bijective. Kind: PROVED. -/
theorem quasiIso_iff_bijective_homologyMapLin (φ : S₁ ⟶ S₂) :
    ShortComplex.QuasiIso φ ↔ Function.Bijective (homologyMapLin φ) := by
  rw [(leftHomologyMapDataLin φ).quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  rfl

/-- **Elementwise sufficient condition** (tex 3470–3480): if every cycle whose image is a
boundary is a boundary, and every cycle of the target is a boundary away from the image of a
cycle, then `φ` is a quasi-isomorphism. Kind: PROVED. -/
theorem quasiIso_of_elementwise (φ : S₁ ⟶ S₂)
    (hinj : ∀ z : S₁.X₂, S₁.g.hom z = 0 → ∀ y : S₂.X₁, S₂.f.hom y = φ.τ₂.hom z →
      ∃ x : S₁.X₁, S₁.f.hom x = z)
    (hsurj : ∀ w : S₂.X₂, S₂.g.hom w = 0 → ∃ z : S₁.X₂, S₁.g.hom z = 0 ∧
      ∃ y : S₂.X₁, φ.τ₂.hom z - w = S₂.f.hom y) :
    ShortComplex.QuasiIso φ := by
  rw [quasiIso_iff_bijective_homologyMapLin]
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    induction c using Submodule.Quotient.induction_on with
    | H z =>
      have h0 : (Submodule.Quotient.mk (cyclesMapLin φ z) :
          LinearMap.ker S₂.g.hom ⧸ LinearMap.range S₂.moduleCatToCycles) = 0 := hc
      rw [Submodule.Quotient.mk_eq_zero] at h0
      obtain ⟨y, hy⟩ := h0
      obtain ⟨x, hx⟩ := hinj z.1 z.2 y (congrArg Subtype.val hy)
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨x, Subtype.ext hx⟩
  · intro c
    induction c using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨z, hz, y, hy⟩ := hsurj w.1 w.2
      refine ⟨Submodule.Quotient.mk ⟨z, hz⟩, ?_⟩
      change (Submodule.Quotient.mk (cyclesMapLin φ ⟨z, hz⟩) :
          LinearMap.ker S₂.g.hom ⧸ LinearMap.range S₂.moduleCatToCycles) =
        Submodule.Quotient.mk w
      rw [Submodule.Quotient.eq]
      exact ⟨y, Subtype.ext hy.symm⟩

end ShortComplexElementwise

/-! ### Quasi-isomorphisms of relation-indexed complexes, elementwise -/

section GCxElementwise

variable {R : Type} [CommRing R] {A B : GCx R}

/-- **Elementwise criterion for `QuasiIsoAt` of a relation-indexed chain map** (tex 3470–3480):
in degree `n` with `m + 1 = n` and `n + 1 = p`, injectivity and surjectivity on
`ker d ⧸ im d`, stated elementwise, give `QuasiIsoAt (GHom.toCC f) n`. Kind: PROVED. -/
theorem quasiIsoAt_toCC_of_elementwise (f : GHom A B) (m n p : ℤ) (hmn : m + 1 = n)
    (hnp : n + 1 = p)
    (hinj : ∀ z : A.X n, A.d n p hnp z = 0 → ∀ y : B.X m, B.d m n hmn y = f.f n n rfl z →
      ∃ x : A.X m, A.d m n hmn x = z)
    (hsurj : ∀ w : B.X n, B.d n p hnp w = 0 → ∃ z : A.X n, A.d n p hnp z = 0 ∧
      ∃ y : B.X m, f.f n n rfl z - w = B.d m n hmn y) :
    QuasiIsoAt (GHom.toCC f) n := by
  rw [quasiIsoAt_iff' _ m n p ((ComplexShape.up ℤ).prev_eq' hmn)
    ((ComplexShape.up ℤ).next_eq' hnp)]
  apply quasiIso_of_elementwise
  · intro z hz y hy
    have hz' : A.d n p hnp z = 0 := (GCx.toCC_d_hom A n p hnp z).symm.trans hz
    have hy' : B.d m n hmn y = f.f n n rfl z := (GCx.toCC_d_hom B m n hmn y).symm.trans hy
    obtain ⟨x, hx⟩ := hinj z hz' y hy'
    exact ⟨x, (GCx.toCC_d_hom A m n hmn x).trans hx⟩
  · intro w hw
    have hw' : B.d n p hnp w = 0 := (GCx.toCC_d_hom B n p hnp w).symm.trans hw
    obtain ⟨z, hz, y, hy⟩ := hsurj w hw'
    exact ⟨z, (GCx.toCC_d_hom A n p hnp z).trans hz, y,
      hy.trans (GCx.toCC_d_hom B m n hmn y).symm⟩

end GCxElementwise

/-! ### Degree zero, for any `g` -/

section DegreeZeroQI

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]

/-- **`tameCochainMap` is a quasi-isomorphism in degree `0`** (tex 3470–3480), for any `g`,
over any commutative ring, when `G` is topologically generated by `φ`, `σ` and a subgroup
acting trivially (separated coefficients). Kind: PROVED. -/
theorem quasiIsoAt_tameCochainMap_zero [T1Space M] (Φ g : M →ₗ[R] M) (φ σ : G) (q : ℕ)
    (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m) (hg : g ∘ₗ g = LinearMap.id)
    (hcomm : Φ ∘ₗ g = g ∘ₗ Φ) (hrel : φ * σ * φ⁻¹ = σ ^ q) (N : Subgroup G)
    (hN : ∀ x ∈ N, ∀ m : M, x • m = m)
    (hgen : (Subgroup.closure {φ, σ} ⊔ N).topologicalClosure = ⊤) :
    QuasiIsoAt (GHom.toCC (tameCochainMap Φ g φ σ q hq hΦ hgσ hg hcomm hrel)) 0 := by
  apply quasiIsoAt_toCC_of_elementwise _ (-1) 0 1 (by norm_num) rfl
  · intro z _ y hy
    have hy' : (0 : M) = evalZero R M z := hy
    have hz0 : (z : (contCochains R G M).X 0) = 0 :=
      evalZero_injective (hy'.symm.trans (map_zero _).symm)
    exact ⟨0, (map_zero _).trans hz0.symm⟩
  · intro w hw
    obtain ⟨a, ha⟩ := evalZero_surjective (R := R) (G := G) (M := M) w
    have hw' : freeD0 (Φ - LinearMap.id) (g - LinearMap.id) (evalZero R M a) = 0 := by
      rw [ha]
      exact hw
    refine ⟨a, (tame_H0_iff Φ g φ σ hΦ hgσ N hN hgen a).mpr hw', 0, ?_⟩
    change evalZero R M a - (show M from w) = 0
    exact sub_eq_zero.mpr ha

/-- **`tameCochainMap` is a quasi-isomorphism in negative degrees**, where both complexes vanish
(tex 3470–3480). Kind: PROVED. -/
theorem quasiIsoAt_tameCochainMap_neg (Φ g : M →ₗ[R] M) (φ σ : G) (q : ℕ)
    (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m) (hg : g ∘ₗ g = LinearMap.id)
    (hcomm : Φ ∘ₗ g = g ∘ₗ Φ) (hrel : φ * σ * φ⁻¹ = σ ^ q) (j : ℕ) :
    QuasiIsoAt (GHom.toCC (tameCochainMap Φ g φ σ q hq hΦ hgσ hg hcomm hrel))
      (Int.negSucc j) := by
  apply quasiIsoAt_toCC_of_elementwise _ (Int.negSucc j - 1) (Int.negSucc j)
    (Int.negSucc j + 1) (by omega) rfl
  · intro z _ y _
    exact ⟨0, rfl⟩
  · intro w _
    exact ⟨0, rfl, 0, rfl⟩

end DegreeZeroQI

/-! ### Degree one at `g = 1` -/

section DegreeOneQI

variable {k : Type} [Field k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- **`tameCochainMap` is a quasi-isomorphism in degree `1` at `g = 1`** (tex 3298–3306,
3470–3480), whenever the induced map `tameH1` on `Z¹ ⧸ d⁰C⁰` is bijective. Kind: PROVED. -/
theorem quasiIsoAt_tameCochainMap_one_of_bijective (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ)
    (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m) (hσ : ∀ m : M, σ • m = m)
    (hgσ : ∀ m, (LinearMap.id : M →ₗ[k] M) m = σ • m)
    (hg : (LinearMap.id : M →ₗ[k] M) ∘ₗ LinearMap.id = LinearMap.id)
    (hcomm : Φ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ Φ) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (hb : Function.Bijective (tameH1 Φ φ σ q hq hΦ hσ hrel)) :
    QuasiIsoAt (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ hgσ hg hcomm hrel)) 1 := by
  apply quasiIsoAt_toCC_of_elementwise _ 0 1 2 rfl rfl
  · intro z hz y hy
    let zc : Z1K k G M := ⟨z, hz⟩
    have h0 : tameH1 Φ φ σ q hq hΦ hσ hrel (Submodule.Quotient.mk zc) = 0 := by
      change (Submodule.Quotient.mk (tameZ1 Φ φ σ q hq hΦ hσ hrel zc) : ModelH1 Φ q) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨y, hy⟩
    have h1 := hb.1 (h0.trans (map_zero _).symm)
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨x, hx⟩ := h1
    exact ⟨x, congrArg Subtype.val hx⟩
  · intro w hw
    have hwz : w ∈ modelZ1 Φ q := hw
    obtain ⟨c, hc⟩ := hb.2 (Submodule.Quotient.mk ⟨w, hwz⟩)
    induction c using Submodule.Quotient.induction_on with
    | H zc =>
      have hc' : (Submodule.Quotient.mk (tameZ1 Φ φ σ q hq hΦ hσ hrel zc) : ModelH1 Φ q) =
          Submodule.Quotient.mk ⟨w, hwz⟩ := hc
      rw [Submodule.Quotient.eq] at hc'
      obtain ⟨y, hy⟩ := hc'
      exact ⟨zc.1, zc.2, y, hy.symm⟩

end DegreeOneQI

/-! ### The actual local Galois group -/

section ActualLocalQI

open TauCeti ValuativeRel
open ZInQ.Contrib.CloudB3RC53.TameQuotient

variable {K : Type} [Field K] [PerfectField K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup K) M]
  [SMulCommClass (Field.absoluteGaloisGroup K) k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup K) M]
  {n : ℕ} [NeZero n] [Fact (1 < n)] {a : K} {β : AlgebraicClosure K}
  {φ σ : Field.absoluteGaloisGroup K}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

omit [PerfectField K] in
/-- **Degree `0` for the actual local Galois group, any `g`** (tex 3470–3480): with `φ` an
arithmetic Frobenius lift and inertia topologically generated by `σ` and a subgroup `P` acting
trivially (NSW, Thm 7.5.3), `tameCochainMap` is a quasi-isomorphism in degree `0`. Kind:
PROVED. -/
theorem quasiIsoAt_tameCochainMap_zero_local (Φ g : M →ₗ[k] M) (q : ℕ) (hq : Odd q)
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, g m = σ • m) (hg : g ∘ₗ g = LinearMap.id)
    (hcomm : Φ ∘ₗ g = g ∘ₗ Φ) (hrel : φ * σ * φ⁻¹ = σ ^ q) (hφ : IsArithFrobeniusLift K φ)
    (P : Subgroup (Field.absoluteGaloisGroup K)) (hP : ∀ x ∈ P, ∀ m : M, x • m = m)
    (hIσ : (Subgroup.zpowers σ ⊔ P).topologicalClosure = inertiaSubgroup K) :
    QuasiIsoAt (GHom.toCC (tameCochainMap Φ g φ σ q hq hΦ hgσ hg hcomm hrel)) 0 :=
  quasiIsoAt_tameCochainMap_zero Φ g φ σ q hq hΦ hgσ hg hcomm hrel P hP
    (topologicalClosure_closure_pair_sup φ σ _ P
      hφ.topologicalClosure_zpowers_sup_inertiaSubgroup hIσ)

/-- **Degree `1` for the actual local Galois group at `g = 1`** (tex 3298–3306, 5026–5037,
3470–3480): with inertia acting trivially, Iwasawa generators with the exact relation
`φ σ φ⁻¹ = σ ^ q`, `q = |𝓀|` odd, and the hypotheses of `coordQLocal_bijective`,
`tameCochainMap` is a quasi-isomorphism in degree `1`. Kind: PROVED. -/
theorem quasiIsoAt_tameCochainMap_one [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (hq : Odd (Nat.card 𝓀[K])) (Φ : M →ₗ[k] M)
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, (LinearMap.id : M →ₗ[k] M) m = σ • m)
    (hg : (LinearMap.id : M →ₗ[k] M) ∘ₗ LinearMap.id = LinearMap.id)
    (hcomm : Φ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ Φ)
    (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K]) :
    QuasiIsoAt (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ (Nat.card 𝓀[K]) hq hΦ hgσ hg hcomm
      hrel)) 1 :=
  quasiIsoAt_tameCochainMap_one_of_bijective Φ φ σ _ hq hΦ (hItriv σ hσI) hgσ hg hcomm hrel
    (tameH1_bijective_local X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ hrel)

/-- **Reduction of the quasi-isomorphism to degrees `≥ 2`** at `g = 1` (tex 3470–3480): under
the hypotheses of `quasiIsoAt_tameCochainMap_one`, if `tameCochainMap` is a quasi-isomorphism
in every degree `≥ 2`, it is a quasi-isomorphism. Kind: PROVED. -/
theorem quasiIso_tameCochainMap_of_two_le [TopologicalSpace k]
    (X : TopRep.{0} k (UnramifiedGaloisGroup K))
    [ContinuousSMul (UnramifiedGaloisGroup K) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Field.absoluteGaloisGroup K) (x : X.V),
      f (localUnramifiedProjection K g • x) = g • f x)
    (hfs : Function.Surjective f)
    (hn : n.Coprime (ringChar 𝓀[K]))
    (hβ : β ^ n = algebraMap K (AlgebraicClosure K) a) (hβ0 : β ≠ 0)
    (hφ : IsArithFrobeniusLift K φ) (hσI : σ ∈ inertiaSubgroup K)
    (hζ : IsPrimitiveRoot (kummerVal β (algebraicGaloisEquiv K σ)) n)
    (hItriv : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hnM : ∀ m : M, n • m = 0) (hq : Odd (Nat.card 𝓀[K])) (Φ : M →ₗ[k] M)
    (hΦ : ∀ m, Φ m = φ • m) (hgσ : ∀ m, (LinearMap.id : M →ₗ[k] M) m = σ • m)
    (hg : (LinearMap.id : M →ₗ[k] M) ∘ₗ LinearMap.id = LinearMap.id)
    (hcomm : Φ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ Φ)
    (hrel : φ * σ * φ⁻¹ = σ ^ Nat.card 𝓀[K])
    (hhigh : ∀ i : ℤ, 2 ≤ i → QuasiIsoAt (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ
      (Nat.card 𝓀[K]) hq hΦ hgσ hg hcomm hrel)) i) :
    QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ (Nat.card 𝓀[K]) hq hΦ hgσ hg hcomm
      hrel)) := by
  rw [_root_.quasiIso_iff]
  intro i
  rcases i with (_ | _ | i) | j
  · exact quasiIsoAt_tameCochainMap_zero Φ LinearMap.id φ σ _ hq hΦ hgσ hg hcomm hrel
      (inertiaSubgroup K) hItriv (top_le_iff.mp
        (hφ.topologicalClosure_zpowers_sup_inertiaSubgroup.symm.le.trans
          (Subgroup.topologicalClosure_mono (sup_le_sup_right
            (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) _))))
  · exact quasiIsoAt_tameCochainMap_one X f hf hfs hn hβ hβ0 hφ hσI hζ hItriv hnM hq Φ hΦ
      hgσ hg hcomm hrel
  · exact hhigh _ (by rw [Int.ofNat_eq_natCast]; omega)
  · exact quasiIsoAt_tameCochainMap_neg Φ LinearMap.id φ σ _ hq hΦ hgσ hg hcomm hrel j

end ActualLocalQI

end ZInQ.Manuscript.RC.Local
