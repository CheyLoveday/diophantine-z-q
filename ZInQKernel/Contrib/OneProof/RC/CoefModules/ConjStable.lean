import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.SqrtMem

/-!
# Conjugation by an actual complex conjugation on `G_{K,S}`

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830): "Fix an
actual complex conjugation `τ ∈ G_Q`, so that `τ² = 1`", "Here `τ^*M_i` denotes pullback of the
Galois action", and "At a split place `v`, the dual local condition is transported from the
conjugate place `τv`".

The pullback `τ^*M` of a `G_{K,S}`-module needs the automorphism `g ↦ τ g τ⁻¹` of the genuine
group `G_{K,S} = Gal(K_S/K)` (`GKS K S`). It exists because `τ` carries `K_S`
(`unramifiedOutside K S`) into itself when `S` is stable under the automorphism `κ = τ|_K` of `K`.

* `ringEquiv_mem_unramifiedOutside`: a ring automorphism `τ` of `K̄` lying over `κ` maps `K_S`
  into itself when `S` is `κ`-stable. The image `τ(L)` of a finite normal subextension `L`
  unramified outside `S` is again one (`finiteDimensional_imageField`, `normal_imageField`,
  `isUnramifiedOutside_imageField`), by the semilinear transport of ramification indices
  `ramificationIdx_comap_ringEquiv`.
* `galConj`: for a field `L` over `K` and a ring automorphism `τ` of `L` lying over `κ`,
  `σ ↦ τ σ τ⁻¹` is a continuous (Krull topology) group automorphism of `Gal(L/K)`.
* `conjGKS`, `conjGKS_apply`, `continuous_conjGKS`, `conjGKS_conjGKS`, `conjGKSCont`: the
  induced automorphism of `G_{K,S}`; `resAbs_conjAbs`, `inflMap_conjGKS`: compatibility with the
  restrictions `Gal(K̄/K) → G_{K,S}` and `G_{K,S'} → G_{K,S}`.
* `conjPlace`, `mem_conjPlace_iff`: the conjugate place `κ(v)`; `isStable_comap_int`: a set of
  primes described through the rational primes below them is stable under every automorphism.
* `exists_complexConj_algClosure`: an actual complex conjugation of `K̄`;
  `exists_restrict_of_normal`: for `K/ℚ` normal it restricts to an automorphism `κ` of `K`;
  `complexConj_inv_of_pow_eq_one`: it inverts roots of unity; `complexConj_restrict_ne_refl`: for
  `K` totally complex, `κ ≠ id`; `exists_conjGKS_of_imagQuad`: the assembled statement for an
  imaginary quadratic field.

Kinds: every theorem is PROVED; the definitions are genuine constructions.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Manuscript.RC.SelmerComplex

/-! ### Semilinear transport of ramification indices -/

/-- **Ramification indices are invariant under semilinear ring isomorphisms.** Let `κ` be a ring
automorphism of `A` and `φ : B ≃+* B'` a ring isomorphism between `A`-algebras lying over `κ`
(`φ ∘ algebraMap = algebraMap ∘ κ`). Then for every ideal `Q'` of `B'`, the ideal `φ⁻¹(Q')` of `B`
has the same ramification index over `A` as `Q'` (both are lengths of the same local quotient,
identified through the induced isomorphism of localizations).

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem ramificationIdx_comap_ringEquiv {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A B'] (κ : A ≃+* A) (φ : B ≃+* B')
    (hφ : ∀ a, φ (algebraMap A B a) = algebraMap A B' (κ a)) (Q' : Ideal B') :
    (Q'.comap φ).ramificationIdx A = Q'.ramificationIdx A := by
  have hback : (Q'.comap φ).map φ = Q' :=
    Ideal.map_comap_of_surjective _ φ.surjective Q'
  by_cases hQ' : Q'.IsPrime; swap
  · have : ¬ (Q'.comap φ).IsPrime := fun h => hQ' (by
      rw [← hback]; exact Ideal.map_isPrime_of_equiv φ)
    rw [Ideal.ramificationIdx_of_not_isPrime _ _ hQ', Ideal.ramificationIdx_of_not_isPrime _ _ this]
  · have hQ : (Q'.comap φ).IsPrime := Ideal.comap_isPrime _ Q'
    have hp : (Q'.comap φ).under A = (Q'.under A).comap (κ : A →+* A) := by
      simp only [Ideal.under, Ideal.comap_comap]
      ext a
      simp [hφ]
    have : (Q'.comap φ).LiesOver ((Q'.comap φ).under A) := ⟨rfl⟩
    have : Q'.LiesOver (Q'.under A) := ⟨rfl⟩
    let Sq := Localization.AtPrime (Q'.comap φ)
    let Sq' := Localization.AtPrime Q'
    let f : Sq ≃+* Sq' := IsLocalization.ringEquivOfRingEquiv Sq Sq' φ
      (Ideal.map_primeCompl_comap_of_surjective φ φ.surjective Q')
    have hf : ∀ b : B, f (algebraMap B Sq b) = algebraMap B' Sq' (φ b) :=
      fun b => IsLocalization.ringEquivOfRingEquiv_eq _ b
    let : Algebra Sq Sq' := f.toRingHom.toAlgebra
    have hJ : Ideal.map (algebraMap A Sq') (Q'.under A) =
        Ideal.map (algebraMap Sq Sq') (Ideal.map (algebraMap A Sq) ((Q'.comap φ).under A)) := by
      rw [Ideal.map_map]
      have : (algebraMap Sq Sq').comp (algebraMap A Sq) =
          (algebraMap A Sq').comp (κ : A →+* A) := by
        ext a
        change f (algebraMap A Sq a) = algebraMap A Sq' (κ a)
        rw [IsScalarTower.algebraMap_apply A B Sq, hf, hφ, ← IsScalarTower.algebraMap_apply]
      rw [this, ← Ideal.map_map, hp, Ideal.map_comap_of_surjective (κ : A →+* A) κ.surjective]
    let g : (Sq ⧸ Ideal.map (algebraMap A Sq) ((Q'.comap φ).under A)) ≃ₐ[Sq]
        Sq' ⧸ Ideal.map (algebraMap A Sq') (Q'.under A) :=
      Ideal.quotientEquivAlg _ _ (AlgEquiv.ofBijective (Algebra.ofId Sq Sq') f.bijective) hJ
    rw [Ideal.ramificationIdx_eq ((Q'.comap φ).under A) (Q'.comap φ),
      Ideal.ramificationIdx_eq (Q'.under A) Q',
      g.toLinearEquiv.length_eq, Module.length_eq_of_surjective f.surjective]

/-! ### Images of intermediate fields under a semilinear automorphism -/

section Image

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (κ : K ≃+* K) (τ : L ≃+* L)
  (hτ : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (κ x))

/-- The image `τ(E)` of an intermediate field `E` of `L/K` under a ring automorphism `τ` of `L`
lying over the automorphism `κ` of `K`; it is again an intermediate field because `τ(K) = K`. -/
def imageField (E : IntermediateField K L) : IntermediateField K L :=
  (E.toSubfield.map (τ : L →+* L)).toIntermediateField fun a =>
    ⟨algebraMap K L (κ.symm a), E.algebraMap_mem _, by simp [hτ]⟩

/-- Membership in the image field: `y ∈ τ(E)` iff `y = τ x` for some `x ∈ E`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem mem_imageField {E : IntermediateField K L} {y : L} :
    y ∈ imageField κ τ hτ E ↔ ∃ x ∈ E, τ x = y := Iff.rfl

/-- `τ`, viewed as a `κ`-semilinear map of `K`-vector spaces `L → L`. -/
def semilinearOfRingEquiv : L →ₛₗ[(κ : K →+* K)] L where
  toFun := τ
  map_add' := map_add τ
  map_smul' a x := by simp [Algebra.smul_def, hτ]

/-- **`τ(E)` is finite-dimensional when `E` is**: it is the image of `E` under the semilinear map
`τ`, and images of finitely generated submodules under semilinear maps are finitely generated.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem finiteDimensional_imageField (E : IntermediateField K L) [FiniteDimensional K E] :
    FiniteDimensional K (imageField κ τ hτ E) := by
  have h1 : (E.toSubalgebra.toSubmodule).FG := Module.Finite.iff_fg.mp ‹_›
  have h2 := h1.map (semilinearOfRingEquiv κ τ hτ)
  have h3 : (imageField κ τ hτ E).toSubalgebra.toSubmodule =
      (E.toSubalgebra.toSubmodule).map (semilinearOfRingEquiv κ τ hτ) := by
    ext y
    simp only [Submodule.mem_map]
    exact Iff.rfl
  rw [← h3] at h2
  exact Module.Finite.iff_fg.mpr h2

/-- **`τ(E)` is normal over `K` when `E` is** (for `L/K` normal): for every `K`-embedding
`σ : L → L`, `τ⁻¹ σ τ` is again a `K`-embedding, so it maps `E` into `E`, hence `σ` maps `τ(E)`
into `τ(E)`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem normal_imageField [Normal K L] (E : IntermediateField K L) [Normal K E] :
    Normal K (imageField κ τ hτ E) := by
  rw [IntermediateField.normal_iff_forall_map_le]
  intro σ y hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨x, hx, rfl⟩ := hz
  let ρ : L →ₐ[K] L :=
    { toRingHom := (τ.symm : L →+* L).comp ((σ : L →+* L).comp (τ : L →+* L))
      commutes' := fun a => by
        change τ.symm (σ (τ (algebraMap K L a))) = algebraMap K L a
        rw [hτ, AlgHom.commutes]
        apply τ.injective
        rw [RingEquiv.apply_symm_apply, hτ] }
  have hmap := (IntermediateField.normal_iff_forall_map_le.mp ‹Normal K E›) ρ
  refine ⟨ρ x, hmap ⟨x, hx, rfl⟩, ?_⟩
  change τ (τ.symm (σ (τ x))) = σ (τ x)
  exact τ.apply_symm_apply _

end Image

/-! ### Unramifiedness of the image -/

section Unramified

variable {K : Type} [Field K] [NumberField K] (κ : K ≃+* K)
  (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
  (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x))

/-- The restriction `E ≃+* τ(E)` of `τ`. -/
def imageEquiv (E : IntermediateField K (AlgebraicClosure K)) : E ≃+* imageField κ τ hτ E where
  toFun x := ⟨τ x, x, x.2, rfl⟩
  invFun y := ⟨τ.symm y, by
    obtain ⟨x, hx, hxy⟩ := (mem_imageField κ τ hτ).mp y.2
    rw [← hxy, τ.symm_apply_apply]
    exact hx⟩
  left_inv x := Subtype.ext (τ.symm_apply_apply (x : AlgebraicClosure K))
  right_inv y := Subtype.ext (τ.apply_symm_apply (y : AlgebraicClosure K))
  map_mul' x y := Subtype.ext (map_mul τ (x : AlgebraicClosure K) y)
  map_add' x y := Subtype.ext (map_add τ (x : AlgebraicClosure K) y)

/-- The restriction `E ≃+* τ(E)` is `τ` on underlying elements.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem imageEquiv_apply (E : IntermediateField K (AlgebraicClosure K)) (x : E) :
    ((imageEquiv κ τ hτ E x : imageField κ τ hτ E) : AlgebraicClosure K) = τ x := rfl

/-- The restriction `E ≃+* τ(E)` lies over the automorphism `κ` of `𝒪_K`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem imageEquiv_algebraMap (E : IntermediateField K (AlgebraicClosure K)) (a : 𝓞 K) :
    imageEquiv κ τ hτ E (algebraMap (𝓞 K) E a) =
      algebraMap (𝓞 K) (imageField κ τ hτ E) (RingOfIntegers.mapRingEquiv κ a) := by
  apply Subtype.ext
  rw [imageEquiv_apply]
  change τ (algebraMap K (AlgebraicClosure K) (a : K)) =
    algebraMap K (AlgebraicClosure K) ((RingOfIntegers.mapRingEquiv κ a : 𝓞 K) : K)
  rw [hτ, RingOfIntegers.mapRingEquiv_apply]

/-- The inverse `τ(E) ≃+* E` lies over `κ⁻¹` on `𝒪_K`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem imageEquiv_symm_algebraMap (E : IntermediateField K (AlgebraicClosure K)) (a : 𝓞 K) :
    (imageEquiv κ τ hτ E).symm (algebraMap (𝓞 K) (imageField κ τ hτ E) a) =
      algebraMap (𝓞 K) E ((RingOfIntegers.mapRingEquiv κ).symm a) := by
  apply (imageEquiv κ τ hτ E).injective
  rw [RingEquiv.apply_symm_apply, imageEquiv_algebraMap, RingEquiv.apply_symm_apply]

/-- The ring isomorphism between the integral closures of `𝒪_K` in `E` and in `τ(E)` induced by
`τ` (integrality is transported along `κ`). -/
def integralClosureImageEquiv (E : IntermediateField K (AlgebraicClosure K)) :
    integralClosure (𝓞 K) E ≃+* integralClosure (𝓞 K) (imageField κ τ hτ E) where
  toFun b := ⟨imageEquiv κ τ hτ E b,
    IsIntegral.map_of_comp_eq (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)
      (imageEquiv κ τ hτ E : E →+* imageField κ τ hτ E) (by
        ext a
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
        rw [imageEquiv_algebraMap]) b.2⟩
  invFun b := ⟨(imageEquiv κ τ hτ E).symm b,
    IsIntegral.map_of_comp_eq ((RingOfIntegers.mapRingEquiv κ).symm : 𝓞 K →+* 𝓞 K)
      ((imageEquiv κ τ hτ E).symm : imageField κ τ hτ E →+* E) (by
        ext a
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
        rw [imageEquiv_symm_algebraMap]) b.2⟩
  left_inv b := Subtype.ext ((imageEquiv κ τ hτ E).symm_apply_apply (b : E))
  right_inv b := Subtype.ext ((imageEquiv κ τ hτ E).apply_symm_apply (b : imageField κ τ hτ E))
  map_mul' x y := Subtype.ext (map_mul (imageEquiv κ τ hτ E) (x : E) y)
  map_add' x y := Subtype.ext (map_add (imageEquiv κ τ hτ E) (x : E) y)

/-- The isomorphism of integral closures lies over the automorphism `κ` of `𝒪_K`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem integralClosureImageEquiv_algebraMap (E : IntermediateField K (AlgebraicClosure K))
    (a : 𝓞 K) :
    integralClosureImageEquiv κ τ hτ E (algebraMap (𝓞 K) (integralClosure (𝓞 K) E) a) =
      algebraMap (𝓞 K) (integralClosure (𝓞 K) (imageField κ τ hτ E))
        (RingOfIntegers.mapRingEquiv κ a) :=
  Subtype.ext (imageEquiv_algebraMap κ τ hτ E a)

/-- **`τ(E)` is unramified outside a `κ`-stable `S` when `E` is.** A prime `Q'` of the integral
closure for `τ(E)` above `v ∉ S` corresponds under `τ` to a prime above `w = κ⁻¹(v)`, which is not
in `S` by stability, and the ramification indices agree (`ramificationIdx_comap_ringEquiv`).

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem isUnramifiedOutside_imageField (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v w : HeightOneSpectrum (𝓞 K),
        w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S ↔ w ∈ S))
    (E : IntermediateField K (AlgebraicClosure K)) (hE : IsUnramifiedOutside K S E) :
    IsUnramifiedOutside K S (imageField κ τ hτ E) := by
  intro v hv Q' hQ' hlo
  set κO := RingOfIntegers.mapRingEquiv κ with hκO
  have hne : v.asIdeal.comap (κO : 𝓞 K →+* 𝓞 K) ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [← Ideal.map_comap_of_surjective (κO : 𝓞 K →+* 𝓞 K) κO.surjective v.asIdeal, h,
      Ideal.map_bot]
  let w : HeightOneSpectrum (𝓞 K) :=
    ⟨v.asIdeal.comap (κO : 𝓞 K →+* 𝓞 K), Ideal.comap_isPrime _ _, hne⟩
  have hw : w ∉ S := fun hwS => hv ((hS w v
    (Ideal.map_comap_of_surjective (κO : 𝓞 K →+* 𝓞 K) κO.surjective v.asIdeal).symm).mp hwS)
  rw [← ramificationIdx_comap_ringEquiv κO (integralClosureImageEquiv κ τ hτ E)
    (integralClosureImageEquiv_algebraMap κ τ hτ E) Q']
  refine hE w hw _ (Ideal.comap_isPrime _ _) ⟨?_⟩
  ext a
  change κO a ∈ v.asIdeal ↔ integralClosureImageEquiv κ τ hτ E (algebraMap (𝓞 K) _ a) ∈ Q'
  rw [integralClosureImageEquiv_algebraMap, hlo.over]
  rfl

end Unramified

/-! ### `τ` preserves `K_S` -/

/-- **A ring automorphism of `K̄` over `κ` preserves `K_S` for `κ`-stable `S`.** Let `τ` be a ring
automorphism of `K̄ = AlgebraicClosure K` with `τ(a) = κ(a)` for `a ∈ K`, and let `S` be stable
under `κ` (`v ∈ S ↔ κ(v) ∈ S`). Then `τ(K_S) ⊆ K_S`, where `K_S = unramifiedOutside K S`. Proof: the
preimage `τ⁻¹(K_S)` is an intermediate field; it contains every finite normal subextension `L`
unramified outside `S`, because `τ(L)` is again finite, normal and unramified outside `S`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem ringEquiv_mem_unramifiedOutside (K : Type) [Field K] [NumberField K] (κ : K ≃+* K)
    (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x))
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v w : HeightOneSpectrum (𝓞 K),
        w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S ↔ w ∈ S))
    (x : AlgebraicClosure K) (hx : x ∈ ZInQ.Contrib.CloudB3RC53.RankCounts.unramifiedOutside K S) :
    τ x ∈ ZInQ.Contrib.CloudB3RC53.RankCounts.unramifiedOutside K S := by
  let U' : IntermediateField K (AlgebraicClosure K) :=
    ((unramifiedOutside K S).toSubfield.comap
      (τ : AlgebraicClosure K →+* AlgebraicClosure K)).toIntermediateField fun a => by
        change τ (algebraMap K _ a) ∈ unramifiedOutside K S
        rw [hτ]
        exact (unramifiedOutside K S).algebraMap_mem _
  have hle : unramifiedOutside K S ≤ U' := by
    refine iSup₂_le fun L hL => ?_
    obtain ⟨hfin, hnorm, hunr⟩ := hL
    intro y hy
    change τ y ∈ unramifiedOutside K S
    have : imageField κ τ hτ L ≤ unramifiedOutside K S :=
      le_iSup₂_of_le (f := fun (L : IntermediateField K (AlgebraicClosure K))
        (_ : FiniteDimensional K L ∧ Normal K L ∧ IsUnramifiedOutside K S L) => L)
        (imageField κ τ hτ L)
        ⟨finiteDimensional_imageField κ τ hτ L, normal_imageField κ τ hτ L,
          isUnramifiedOutside_imageField κ τ hτ S hS L hunr⟩ le_rfl
    exact this ⟨y, hy, rfl⟩
  exact hle hx

/-! ### Conjugation of Galois groups by a semilinear automorphism -/

section GaloisConj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (κ : K ≃+* K) (τ : L ≃+* L)
  (hτ : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (κ x))

include hτ in
/-- The inverse `τ⁻¹` lies over `κ⁻¹`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem symm_algebraMap (x : K) : τ.symm (algebraMap K L x) = algebraMap K L (κ.symm x) := by
  apply τ.injective
  rw [RingEquiv.apply_symm_apply, hτ, RingEquiv.apply_symm_apply]

/-- The conjugate `τ σ τ⁻¹` of a `K`-automorphism `σ` of `L`; it is again `K`-linear because `τ`
lies over `κ` and `τ⁻¹` over `κ⁻¹`. -/
def galConjFun (σ : L ≃ₐ[K] L) : L ≃ₐ[K] L :=
  AlgEquiv.ofRingEquiv (f := τ.symm.trans (σ.toRingEquiv.trans τ)) fun a => by
    simp only [RingEquiv.trans_apply, symm_algebraMap κ τ hτ, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.commutes, hτ, RingEquiv.apply_symm_apply]

/-- **Conjugation by `τ` on `Gal(L/K)`**: the group automorphism `σ ↦ τ σ τ⁻¹`, with inverse
`σ ↦ τ⁻¹ σ τ`. -/
def galConj : (L ≃ₐ[K] L) ≃* (L ≃ₐ[K] L) where
  toFun σ := galConjFun κ τ hτ σ
  invFun σ := galConjFun κ.symm τ.symm (symm_algebraMap κ τ hτ) σ
  left_inv σ := by
    apply AlgEquiv.ext
    intro x
    change τ.symm (τ (σ (τ.symm (τ.symm.symm x)))) = σ x
    rw [RingEquiv.symm_symm, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  right_inv σ := by
    apply AlgEquiv.ext
    intro x
    change τ (τ.symm (σ (τ.symm.symm (τ.symm x)))) = σ x
    rw [RingEquiv.symm_symm, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  map_mul' σ₁ σ₂ := by
    apply AlgEquiv.ext
    intro x
    change τ (σ₁ (σ₂ (τ.symm x))) = τ (σ₁ (τ.symm (τ (σ₂ (τ.symm x)))))
    rw [RingEquiv.symm_apply_apply]

/-- **The formula for conjugation**: `(τ σ τ⁻¹)(x) = τ(σ(τ⁻¹ x))`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem galConj_apply (σ : L ≃ₐ[K] L) (x : L) : galConj κ τ hτ σ x = τ (σ (τ.symm x)) := rfl

/-- The inverse of conjugation by `τ` is conjugation by `τ⁻¹`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem galConj_symm :
    (galConj κ τ hτ).symm = galConj κ.symm τ.symm (symm_algebraMap κ τ hτ) :=
  MulEquiv.ext fun _ => rfl

/-- **Conjugation is continuous for the Krull topology.** For a finite-dimensional intermediate
field `E`, the preimage of the fixing subgroup of `E` contains the fixing subgroup of the
finite-dimensional intermediate field `τ⁻¹(E)` (`finiteDimensional_imageField`), which is open.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem continuous_galConj : Continuous (galConj κ τ hτ) := by
  refine continuous_of_continuousAt_one (galConj κ τ hτ) ?_
  rw [ContinuousAt, map_one]
  refine Filter.tendsto_def.mpr fun s hs => ?_
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K L s).mp hs
  let E' : IntermediateField K L := imageField κ.symm τ.symm (symm_algebraMap κ τ hτ) E
  have hE' : FiniteDimensional K E' := finiteDimensional_imageField _ _ _ E
  have hsub : (E'.fixingSubgroup : Set (L ≃ₐ[K] L)) ⊆ galConj κ τ hτ ⁻¹' s := by
    intro σ hσ
    apply hEs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro e he
    rw [galConj_apply, hσ (τ.symm e) ⟨e, he, rfl⟩, RingEquiv.apply_symm_apply]
  exact Filter.mem_of_superset ((E'.fixingSubgroup_isOpen).mem_nhds E'.fixingSubgroup.one_mem) hsub

/-- **Conjugation by an involution is an involution**: if `τ (τ x) = x` for all `x`, then
`τ (τ σ τ⁻¹) τ⁻¹ = σ`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem galConj_galConj (hinv : ∀ x, τ (τ x) = x) (σ : L ≃ₐ[K] L) :
    galConj κ τ hτ (galConj κ τ hτ σ) = σ := by
  have h : ∀ y, τ.symm y = τ y := fun y => by
    apply τ.injective
    rw [RingEquiv.apply_symm_apply, hinv]
  apply AlgEquiv.ext
  intro x
  rw [galConj_apply, galConj_apply, h, h, hinv, hinv]

/-- Conjugation by `τ` as an isomorphism of topological groups `Gal(L/K) ≃ₜ* Gal(L/K)`. -/
def galConjCont : (L ≃ₐ[K] L) ≃ₜ* (L ≃ₐ[K] L) :=
  { galConj κ τ hτ with
    continuous_toFun := continuous_galConj κ τ hτ
    continuous_invFun := continuous_galConj κ.symm τ.symm (symm_algebraMap κ τ hτ) }

end GaloisConj

/-! ### The induced automorphism of `G_{K,S}` -/

section ConjGKS

variable (K : Type) [Field K] [NumberField K] (κ : K ≃+* K)
  (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
  (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x))
  (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S ↔ w ∈ S))

omit [NumberField K] in
include hS in
/-- A `κ`-stable set of primes is `κ⁻¹`-stable.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem stable_symm : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ.symm : 𝓞 K →+* 𝓞 K) →
      (v ∈ S ↔ w ∈ S) := fun v w h => by
  have hid : (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K).comp
      (RingOfIntegers.mapRingEquiv κ.symm : 𝓞 K →+* 𝓞 K) = RingHom.id _ := by
    ext a
    simp [RingOfIntegers.mapRingEquiv_apply]
  have hv : v.asIdeal = w.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) := by
    rw [h, Ideal.map_map, hid, Ideal.map_id]
  exact (hS w v hv).symm

/-- The restriction of `τ` to a ring automorphism of `K_S` (`ringEquiv_mem_unramifiedOutside`
for `τ` and for `τ⁻¹`). -/
def tauS : unramifiedOutside K S ≃+* unramifiedOutside K S where
  toFun x := ⟨τ x, ringEquiv_mem_unramifiedOutside K κ τ hτ S hS x x.2⟩
  invFun x := ⟨τ.symm x, ringEquiv_mem_unramifiedOutside K κ.symm τ.symm (symm_algebraMap κ τ hτ)
    S (stable_symm K κ S hS) x x.2⟩
  left_inv x := Subtype.ext (τ.symm_apply_apply (x : AlgebraicClosure K))
  right_inv x := Subtype.ext (τ.apply_symm_apply (x : AlgebraicClosure K))
  map_mul' x y := Subtype.ext (map_mul τ (x : AlgebraicClosure K) y)
  map_add' x y := Subtype.ext (map_add τ (x : AlgebraicClosure K) y)

/-- The restriction of `τ` to `K_S` is `τ` on underlying elements.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem tauS_apply (x : unramifiedOutside K S) :
    ((tauS K κ τ hτ S hS x : unramifiedOutside K S) : AlgebraicClosure K) = τ x := rfl

/-- The restriction of `τ` to `K_S` lies over `κ`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem tauS_algebraMap (a : K) :
    tauS K κ τ hτ S hS (algebraMap K (unramifiedOutside K S) a) =
      algebraMap K (unramifiedOutside K S) (κ a) :=
  Subtype.ext (hτ a)

/-- **The conjugation `g ↦ τ g τ⁻¹` of `G_{K,S} = Gal(K_S/K)`** (the tree's `GKS K S`), for a
ring automorphism `τ` of `K̄` lying over `κ` and a `κ`-stable set `S`: the group automorphism used
to pull back the Galois action, `τ^*M`. -/
def conjGKS : GKS K S ≃* GKS K S :=
  galConj κ (tauS K κ τ hτ S hS) (tauS_algebraMap K κ τ hτ S hS)

/-- **The formula for `conjGKS`**: for `σ ∈ G_{K,S}` and `x ∈ K_S`,
`(τ σ τ⁻¹)(x) = τ(σ(τ⁻¹ x))` (`GKS K S` is a type synonym of `Gal(K_S/K)` without a function
coercion, so automorphisms are applied through `@id (GaloisGroupS K S)`).

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem conjGKS_apply (σ : GKS K S) (x : unramifiedOutside K S) :
    (((@id (GaloisGroupS K S) (conjGKS K κ τ hτ S hS σ)) x : unramifiedOutside K S) :
      AlgebraicClosure K) =
      τ ((@id (GaloisGroupS K S) σ) ⟨τ.symm x, ringEquiv_mem_unramifiedOutside K κ.symm τ.symm
        (symm_algebraMap κ τ hτ) S (stable_symm K κ S hS) x x.2⟩) := rfl

/-- **`conjGKS` is continuous** for the Krull topology of `G_{K,S}` (`continuous_galConj`).

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem continuous_conjGKS : Continuous (conjGKS K κ τ hτ S hS) :=
  continuous_galConj κ (tauS K κ τ hτ S hS) (tauS_algebraMap K κ τ hτ S hS)

/-- **`conjGKS` is an involution when `τ² = 1`.**

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem conjGKS_conjGKS (hinv : ∀ x, τ (τ x) = x) (σ : GKS K S) :
    conjGKS K κ τ hτ S hS (conjGKS K κ τ hτ S hS σ) = σ :=
  galConj_galConj κ (tauS K κ τ hτ S hS) (tauS_algebraMap K κ τ hτ S hS)
    (fun y => Subtype.ext (hinv (y : AlgebraicClosure K))) σ

/-- The inverse of `conjGKS` for `τ` is `conjGKS` for `τ⁻¹`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem conjGKS_symm :
    (conjGKS K κ τ hτ S hS).symm =
      conjGKS K κ.symm τ.symm (symm_algebraMap κ τ hτ) S (stable_symm K κ S hS) :=
  MulEquiv.ext fun _ => rfl

/-- `conjGKS` as an isomorphism of topological groups `G_{K,S} ≃ₜ* G_{K,S}`. -/
def conjGKSCont : GKS K S ≃ₜ* GKS K S :=
  galConjCont κ (tauS K κ τ hτ S hS) (tauS_algebraMap K κ τ hτ S hS)

/-- Conjugation by `τ` on the absolute Galois group `Gal(K̄/K)`. -/
def conjAbs : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≃*
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
  galConj κ τ hτ

/-- **Compatibility with restriction**: restricting `τ σ τ⁻¹` from `K̄` to `K_S` gives
`conjGKS` of the restriction of `σ`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem resAbs_conjAbs (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    resAbs K S (conjAbs K κ τ hτ σ) = conjGKS K κ τ hτ S hS (resAbs K S σ) := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [resAbs_apply_coe]
  change τ (σ (τ.symm x)) = τ (((resAbs K S σ) ((tauS K κ τ hτ S hS).symm x) :
    unramifiedOutside K S) : AlgebraicClosure K)
  rw [resAbs_apply_coe]
  rfl

end ConjGKS

/-- **Compatibility with inflation**: for `κ`-stable `S ⊆ S'`, the restriction
`G_{K,S'} → G_{K,S}` (`inflMap`) intertwines the two conjugations.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem inflMap_conjGKS (K : Type) [Field K] [NumberField K] (κ : K ≃+* K)
    (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x))
    {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S')
    (hS : ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S ↔ w ∈ S))
    (hS' : ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S' ↔ w ∈ S'))
    (σ : GKS K S') :
    inflMap K h (conjGKS K κ τ hτ S' hS' σ) = conjGKS K κ τ hτ S hS (inflMap K h σ) := by
  obtain ⟨g, rfl⟩ := resAbs_surjective K S' σ
  rw [← resAbs_conjAbs K κ τ hτ S' hS']
  change resUnr K h (resAbs K S' (conjAbs K κ τ hτ g)) =
    conjGKS K κ τ hτ S hS (resUnr K h (resAbs K S' g))
  rw [resUnr_comp, resUnr_comp, resAbs_conjAbs]

/-! ### Conjugate places and stable sets of primes -/

section Places

variable {K : Type} [Field K]

/-- **The conjugate place** `κ(v)` of a finite place `v` of `K`, for a ring automorphism `κ` of
`K`: the image of the prime `v` under the induced automorphism of `𝒪_K`. -/
def conjPlace (κ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)
  isPrime := Ideal.map_isPrime_of_equiv (RingOfIntegers.mapRingEquiv κ)
  ne_bot := (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv κ).injective).not.mpr
    v.ne_bot

/-- **A `κ`-stable set contains `v` iff it contains the conjugate place `κ(v)`** (the stability
hypothesis of `ringEquiv_mem_unramifiedOutside` and `conjGKS`, read on places).

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem mem_conjPlace_iff (κ : K ≃+* K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S ↔ w ∈ S))
    (v : HeightOneSpectrum (𝓞 K)) : v ∈ S ↔ conjPlace κ v ∈ S :=
  hS v (conjPlace κ v) rfl

/-- **Conjugating a place twice gives it back** when `κ² = 1`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem conjPlace_conjPlace (κ : K ≃+* K) (hκ : ∀ x, κ (κ x) = x) (v : HeightOneSpectrum (𝓞 K)) :
    conjPlace κ (conjPlace κ v) = v := by
  apply HeightOneSpectrum.ext
  change Ideal.map _ (Ideal.map _ v.asIdeal) = v.asIdeal
  rw [Ideal.map_map]
  have : ((RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K).comp
      (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) = RingHom.id _ := by
    ext a
    simp [RingOfIntegers.mapRingEquiv_apply, hκ]
  rw [this, Ideal.map_id]

/-- A place and its conjugate lie over the same rational prime: the contractions of `v` and of
`w = κ(v)` to `ℤ` coincide.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem comap_int_eq_of_eq_map (κ : K ≃+* K) (v w : HeightOneSpectrum (𝓞 K))
    (h : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) :
    w.asIdeal.comap (algebraMap ℤ (𝓞 K)) = v.asIdeal.comap (algebraMap ℤ (𝓞 K)) := by
  rw [h, Ideal.map_comap_of_equiv]
  ext n
  simp only [Ideal.mem_comap, eq_intCast, map_intCast]

/-- **Sets of primes described through the rational primes below them are stable under every
automorphism of `K`**: for any set `T` of ideals of `ℤ`, the set of places `v` with `v ∩ ℤ ∈ T`
(for instance the places above `2N` together with chosen rational primes) satisfies the
stability hypothesis of `conjGKS` for every `κ`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem isStable_comap_int (T : Set (Ideal ℤ)) (κ : K ≃+* K) :
    ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) →
      (v ∈ {u : HeightOneSpectrum (𝓞 K) | u.asIdeal.comap (algebraMap ℤ (𝓞 K)) ∈ T} ↔
        w ∈ {u : HeightOneSpectrum (𝓞 K) | u.asIdeal.comap (algebraMap ℤ (𝓞 K)) ∈ T}) := by
  intro v w h
  simp only [Set.mem_ofPred_eq, comap_int_eq_of_eq_map κ v w h]

/-- **The places above an integer `n` form a stable set** for every automorphism `κ` of `K`
(e.g. `n = 2N`).

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem isStable_primesAbove (n : ℤ) (κ : K ≃+* K) :
    ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) →
      (v ∈ {u : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ u.asIdeal} ↔
        w ∈ {u : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ u.asIdeal}) := by
  intro v w h
  have hc := congrArg (fun I : Ideal ℤ => n ∈ I) (comap_int_eq_of_eq_map κ v w h)
  simp only [Ideal.mem_comap, eq_intCast] at hc
  simp only [Set.mem_ofPred_eq]
  exact Iff.of_eq hc.symm

end Places

/-! ### An actual complex conjugation of `K̄` -/

section ComplexConj

variable (K : Type) [Field K] [NumberField K]

/-- `K̄ = AlgebraicClosure K` is algebraic over `ℚ` (tower `ℚ ⊆ K ⊆ K̄`).

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem isAlgebraic_rat_algClosure : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) :=
  Algebra.IsAlgebraic.trans ℚ K (AlgebraicClosure K)

/-- **An actual complex conjugation of `K̄`**: there are an embedding `ι : K̄ → ℂ` and a ring
automorphism `τ` of `K̄` with `ι ∘ τ = conj ∘ ι` and `τ² = 1` (complex conjugation restricted to
the normal extension `K̄/ℚ`, embedded in `ℂ`).

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem exists_complexConj_algClosure :
    ∃ (ι : AlgebraicClosure K →+* ℂ) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K),
      (∀ x, ι (τ x) = starRingEnd ℂ (ι x)) ∧ ∀ x, τ (τ x) = x := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) := isAlgebraic_rat_algClosure K
  have : IsAlgClosure ℚ (AlgebraicClosure K) := ⟨inferInstance, this⟩
  have : Normal ℚ (AlgebraicClosure K) := IsAlgClosure.normal ℚ (AlgebraicClosure K)
  let ι : AlgebraicClosure K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let _ : Algebra (AlgebraicClosure K) ℂ := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ (AlgebraicClosure K) ℂ :=
    IsScalarTower.of_algebraMap_eq fun r => (ι.commutes r).symm
  let conjQ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  let τ := conjQ.restrictNormal (AlgebraicClosure K)
  have hτ : ∀ x, ι (τ x) = starRingEnd ℂ (ι x) := fun x =>
    AlgEquiv.restrictNormal_commutes conjQ (AlgebraicClosure K) x
  refine ⟨ι.toRingHom, τ.toRingEquiv, hτ, fun x => ?_⟩
  apply ι.toRingHom.injective
  change ι (τ (τ x)) = ι x
  rw [hτ, hτ, Complex.conj_conj]

/-- **For `K/ℚ` normal, every ring automorphism `τ` of `K̄` restricts to a ring automorphism `κ`
of `K`** (`τ(a) = κ(a)` for `a ∈ K`); in particular an actual complex conjugation does (e.g. for
`K` quadratic).

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem exists_restrict_of_normal [Normal ℚ K] (τ : AlgebraicClosure K ≃+* AlgebraicClosure K) :
    ∃ κ : K ≃+* K, ∀ x : K,
      τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x) := by
  let τQ : AlgebraicClosure K ≃ₐ[ℚ] AlgebraicClosure K :=
    AlgEquiv.ofRingEquiv (f := τ) fun q => by rw [eq_ratCast]; exact map_ratCast τ q
  refine ⟨(τQ.restrictNormal K).toRingEquiv, fun x => ?_⟩
  exact (AlgEquiv.restrictNormal_commutes τQ K x).symm

omit [NumberField K] in
/-- **An actual complex conjugation inverts roots of unity**: if `ι ∘ τ = conj ∘ ι` and
`ζⁿ = 1` with `n > 0`, then `τ ζ = ζ⁻¹` (`|ι ζ| = 1`, so `conj (ι ζ) = (ι ζ)⁻¹`).

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem complexConj_inv_of_pow_eq_one (ι : AlgebraicClosure K →+* ℂ)
    (τ : AlgebraicClosure K ≃+* AlgebraicClosure K) (hι : ∀ x, ι (τ x) = starRingEnd ℂ (ι x))
    {n : ℕ} (hn : 0 < n) (ζ : AlgebraicClosure K) (hζ : ζ ^ n = 1) : τ ζ = ζ⁻¹ := by
  apply ι.injective
  have hnorm : ‖ι ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) hn.ne'
  rw [hι, map_inv₀, Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
  simp

omit [NumberField K] in
/-- **For `K` totally complex, an actual complex conjugation does not fix `K`**: if `τ` lies over
`κ`, then `κ ≠ id` (otherwise `ι|_K` would be a real embedding of `K`).

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem complexConj_restrict_ne_refl [IsTotallyComplex K] (ι : AlgebraicClosure K →+* ℂ)
    (τ : AlgebraicClosure K ≃+* AlgebraicClosure K) (hι : ∀ x, ι (τ x) = starRingEnd ℂ (ι x))
    (κ : K ≃+* K)
    (hκ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x)) :
    κ ≠ RingEquiv.refl K := by
  intro hrefl
  let φ : K →+* ℂ := ι.comp (algebraMap K (AlgebraicClosure K))
  have hreal : ComplexEmbedding.IsReal φ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    change starRingEnd ℂ (ι (algebraMap K _ x)) = ι (algebraMap K _ x)
    rw [← hι, hκ, hrefl, RingEquiv.refl_apply]
  have hv : (InfinitePlace.mk φ).IsReal := InfinitePlace.isReal_mk_iff.mpr hreal
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _)) hv

/-- **Imaginary quadratic fields**: for `[K : ℚ] = 2` and `K` totally complex, an actual complex
conjugation `τ` restricts to a non-trivial automorphism `κ` of `K`.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem exists_complexConj_restrict_ne_refl_of_imagQuad (h2 : Module.finrank ℚ K = 2)
    [IsTotallyComplex K] (ι : AlgebraicClosure K →+* ℂ)
    (τ : AlgebraicClosure K ≃+* AlgebraicClosure K) (hι : ∀ x, ι (τ x) = starRingEnd ℂ (ι x)) :
    ∃ κ : K ≃+* K, (∀ x : K,
      τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x)) ∧
      κ ≠ RingEquiv.refl K := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  obtain ⟨κ, hκ⟩ := exists_restrict_of_normal K τ
  exact ⟨κ, hκ, complexConj_restrict_ne_refl K ι τ hι κ hκ⟩

/-- **The assembled statement for an imaginary quadratic field.** For `[K : ℚ] = 2`, `K` totally
complex, and a set `S` of finite places stable under every automorphism of `K` (e.g.
`isStable_comap_int`, `isStable_primesAbove`), there are an actual complex conjugation
`(ι, τ)` of `K̄`, `τ² = 1`, restricting to a non-trivial automorphism `κ` of `K`, whose
conjugation `conjGKS` of `G_{K,S}` is a continuous involutive group automorphism.

Kind: PROVED. Manuscript reference: `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`,
tex 2761–2830: "Fix an actual complex conjugation τ ∈ G_Q, so that τ² = 1" and "At a split place
v, the dual local condition is transported from the conjugate place τv". -/
theorem exists_conjGKS_of_imagQuad (h2 : Module.finrank ℚ K = 2) [IsTotallyComplex K]
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ κ : K ≃+* K, ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) → (v ∈ S ↔ w ∈ S)) :
    ∃ (ι : AlgebraicClosure K →+* ℂ) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
      (κ : K ≃+* K) (hτ : ∀ x : K,
        τ (algebraMap K (AlgebraicClosure K) x) = algebraMap K (AlgebraicClosure K) (κ x)),
      (∀ x, ι (τ x) = starRingEnd ℂ (ι x)) ∧ (∀ x, τ (τ x) = x) ∧ κ ≠ RingEquiv.refl K ∧
      Continuous (conjGKS K κ τ hτ S (hS κ)) ∧
      ∀ σ : GKS K S, conjGKS K κ τ hτ S (hS κ) (conjGKS K κ τ hτ S (hS κ) σ) = σ := by
  obtain ⟨ι, τ, hι, hinv⟩ := exists_complexConj_algClosure K
  obtain ⟨κ, hκ, hne⟩ := exists_complexConj_restrict_ne_refl_of_imagQuad K h2 ι τ hι
  exact ⟨ι, τ, κ, hκ, hι, hinv, hne, continuous_conjGKS K κ τ hκ S (hS κ),
    conjGKS_conjGKS K κ τ hκ S (hS κ) hinv⟩

end ComplexConj

end ZInQ.Manuscript.RC.CoefModules
