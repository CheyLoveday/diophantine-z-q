import ZInQKernel.Contrib.CloudB3RC53.Finiteness.TwoInSupport
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Inflation

/-!
# The ramification step proved: `h2` from full `2`-power torsion, unconditionally

`TwoInSupport.lean` reduces the hypothesis `h2` (every place above `2` lies in `S`) to the
statement `FiniteUnramifiedSupport` (b2). This file proves (b2), and with it
`TwoPowerRootsRamified` and `h2` from full `2`-power torsion alone:
* `UnramifiedOutsideSup` (definition) and `finiteUnramifiedSupport_of_sup`: (b2) from the
  statement that a compositum of two fields unramified outside `S` is unramified outside `S`;
* `unramifiedOutsideSup_proof` (PROVED): the inertia group of a compositum restricts to the
  trivial inertia groups of its two factors;
* `finiteUnramifiedSupport_proof`, `twoPowerRootsRamified_proof`, `h2_of_hasFullTwoTorsion_proof`
  (PROVED).
The declarations keep their names in `ZInQ.Contrib.CloudB3RC53.Finiteness`. Kinds: definitions and
PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Finiteness
open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.CoefModules (FullTorsion HasRootsOfUnity hasRootsOfUnity_of_fullTorsion
  curveEll curveEll_coeffs)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)

/-! ### (b2) from the compositum statement -/

section Compositum

open ZInQ.Contrib.CloudB3RC53.RankCounts (IsUnramifiedOutside unramifiedOutside UnrGal
  unramifiedOutside_eq_iSup_subtype)

/-- **`K` itself is unramified outside every `S`** (`PROVED`): `𝓞_K → 𝓞_⊥` is surjective, hence
formally unramified. -/
theorem isUnramifiedOutside_bot (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    IsUnramifiedOutside K S (⊥ : IntermediateField K (AlgebraicClosure K)) := by
  rw [RankCounts.KummerS.isUnramifiedOutside_iff]
  intro v _
  have hsurj : Function.Surjective
      (Algebra.ofId (𝓞 K) (𝓞 (⊥ : IntermediateField K (AlgebraicClosure K)))) := by
    intro x
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 (x : (⊥ : IntermediateField K
      (AlgebraicClosure K))).2
    have hk' : algebraMap K (⊥ : IntermediateField K (AlgebraicClosure K)) k = x := by
      apply Subtype.ext
      exact hk
    have hint : IsIntegral ℤ k := by
      have hx : IsIntegral ℤ (x : (⊥ : IntermediateField K (AlgebraicClosure K))) := x.2
      rw [← hk'] at hx
      exact (isIntegral_algHom_iff ((Algebra.ofId K _).restrictScalars ℤ)
        (algebraMap K _).injective).1 hx
    refine ⟨⟨k, hint⟩, ?_⟩
    apply RingOfIntegers.ext
    exact hk'
  have : Algebra.FormallyUnramified (𝓞 K) (𝓞 (⊥ : IntermediateField K (AlgebraicClosure K))) :=
    Algebra.FormallyUnramified.of_surjective _ hsurj
  intro P _ _
  infer_instance

/-- **(ii) The compositum of two finite normal subextensions unramified outside `S` is unramified
outside `S`** (classical: the inertia group of a prime of `L₁ L₂` restricts into the trivial
inertia groups of `L₁` and `L₂`, and `Gal(L₁ L₂/K) → Gal(L₁/K) × Gal(L₂/K)` is injective; Tau Ceti
has `Ideal.isUnramifiedAt_iff_inertia_eq_bot`). Proved in `unramifiedOutsideSup_proof`. -/
def UnramifiedOutsideSup : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (L₁ L₂ : IntermediateField K (AlgebraicClosure K)),
    UnrGal K S L₁ → UnrGal K S L₂ → IsUnramifiedOutside K S (L₁ ⊔ L₂)

/-- **(b2) from (ii)** (`PROVED` from `UnramifiedOutsideSup`): the finite normal subextensions
unramified outside `S` form a directed family (by (ii)), containing `⊥`
(`isUnramifiedOutside_bot`), so every element of their supremum `K_S` lies in one of them. -/
theorem finiteUnramifiedSupport_of_sup (h : UnramifiedOutsideSup) : FiniteUnramifiedSupport := by
  intro K _ _ S x
  have hne : Nonempty {L : IntermediateField K (AlgebraicClosure K) // UnrGal K S L} :=
    ⟨⟨⊥, inferInstance, inferInstance, isUnramifiedOutside_bot K S⟩⟩
  have hdir : Directed (· ≤ ·) (fun L : {L : IntermediateField K (AlgebraicClosure K) //
      UnrGal K S L} => (L : IntermediateField K (AlgebraicClosure K))) := by
    intro L₁ L₂
    have h₁ := L₁.2
    have h₂ := L₂.2
    have : FiniteDimensional K (L₁ : IntermediateField K (AlgebraicClosure K)) := h₁.1
    have : FiniteDimensional K (L₂ : IntermediateField K (AlgebraicClosure K)) := h₂.1
    have : Normal K (L₁ : IntermediateField K (AlgebraicClosure K)) := h₁.2.1
    have : Normal K (L₂ : IntermediateField K (AlgebraicClosure K)) := h₂.2.1
    refine ⟨⟨L₁.1 ⊔ L₂.1, inferInstance, inferInstance, h K S L₁.1 L₂.1 h₁ h₂⟩, le_sup_left,
      le_sup_right⟩
  have key : ∀ y : AlgebraicClosure K, y ∈ unramifiedOutside K S →
      ∃ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L ∧
        IsUnramifiedOutside K S L ∧ y ∈ L := by
    intro y hy
    rw [unramifiedOutside_eq_iSup_subtype, ← SetLike.mem_coe,
      IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion] at hy
    obtain ⟨L, hL⟩ := hy
    exact ⟨L.1, L.2.1, L.2.2.2, hL⟩
  exact key _ x.2

/-- **`h2` from full `2`-power torsion and (ii)** (`PROVED` from `UnramifiedOutsideSup`). -/
theorem h2_of_hasFullTwoTorsion_of_sup (h : UnramifiedOutsideSup)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (W : WeierstrassCurve K) [W.IsElliptic]
    [ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S W] :
    ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
  h2_of_hasFullTwoTorsion_of_finiteUnramifiedSupport (finiteUnramifiedSupport_of_sup h) W

end Compositum

/-! ### Fragments of (ii) -/

/-- **An automorphism of a compositum trivial on both factors is the identity** (`PROVED`). For
intermediate fields `L₁, L₂` of `E/F` and an `F`-automorphism `σ` of `L₁ ⊔ L₂` fixing every element
of `L₁` and of `L₂`, `σ = 1`: the fixed field of `σ` contains `L₁` and `L₂`, hence `L₁ ⊔ L₂`. -/
theorem algEquiv_sup_eq_one {F E : Type*} [Field F] [Field E] [Algebra F E]
    (L₁ L₂ : IntermediateField F E) (σ : ↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂))
    (h₁ : ∀ (x : E) (hx : x ∈ L₁), σ ⟨x, le_sup_left (b := L₂) hx⟩ = ⟨x, le_sup_left (b := L₂) hx⟩)
    (h₂ : ∀ (x : E) (hx : x ∈ L₂), σ ⟨x, le_sup_right (a := L₁) hx⟩ =
      ⟨x, le_sup_right (a := L₁) hx⟩) :
    σ = 1 := by
  set T := IntermediateField.fixedField (Subgroup.zpowers σ)
  have hfix : ∀ y : ↥(L₁ ⊔ L₂), σ y = y → y ∈ T := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hst : σ ∈ MulAction.stabilizer (↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂)) y := hy
    exact (Subgroup.zpowers_le.2 hst) hf
  have hle : L₁ ⊔ L₂ ≤ T.map (L₁ ⊔ L₂).val := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact ⟨⟨x, le_sup_left (b := L₂) hx⟩, hfix _ (h₁ x hx), rfl⟩
    · exact ⟨⟨x, le_sup_right (a := L₁) hx⟩, hfix _ (h₂ x hx), rfl⟩
  refine AlgEquiv.ext fun y => ?_
  obtain ⟨z, hz, hzy⟩ := hle y.2
  have hzy' : z = y := Subtype.ext hzy
  subst hzy'
  exact (IntermediateField.mem_fixedField_iff _ _).1 hz σ (Subgroup.mem_zpowers σ)

/-- **Inertia restricts into inertia** (`PROVED`). Let `f : A → B` be a ring map, `G` act on `B`
and `H` on `A`, and `φ : G → H` compatible with `f` (`f (φ g • a) = g • f a`). If `g` lies in the
inertia group of an ideal `Q` of `B`, then `φ g` lies in the inertia group of `f⁻¹(Q)`. -/
theorem map_mem_inertia_comap {A B G H : Type*} [CommRing A] [CommRing B] [Group G] [Group H]
    [MulAction G B] [MulAction H A] (f : A →+* B) (φ : G →* H)
    (hcompat : ∀ (g : G) (a : A), f (φ g • a) = g • f a) (Q : Ideal B) {g : G}
    (hg : g ∈ Q.inertia G) : φ g ∈ (Q.comap f).inertia H := by
  rw [Ideal.mem_inertia] at hg ⊢
  intro a
  rw [Ideal.mem_comap, map_sub, hcompat]
  exact hg (f a)

/-! ### (ii) proved -/

section CompositumProof

open ZInQ.Contrib.CloudB3RC53.RankCounts (IsUnramifiedOutside UnrGal)

/-- **Trivial inertia** (`PROVED`): at a prime `P` of `𝓞_L` over `v ∉ S`, for `L` finite Galois and
unramified outside `S`, the inertia group is trivial (`Ideal.isUnramifiedAt_iff_inertia_eq_bot`). -/
theorem inertia_eq_bot_of_isUnramifiedOutside {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [Normal K L] (hL : IsUnramifiedOutside K S L)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P.LiesOver v.asIdeal) : P.inertia (L ≃ₐ[K] L) = ⊥ := by
  have hU := (RankCounts.KummerS.isUnramifiedOutside_iff K S L).1 hL v hv
  have : IsGalois K L := IsGalois.mk
  have : Algebra.IsUnramifiedAt (𝓞 K) P := hU P inferInstance hP
  exact (Ideal.isUnramifiedAt_iff_inertia_eq_bot P).1 this

/-- **An inertia element of a compositum is trivial on an unramified factor** (`PROVED`). For
`L_i ≤ M` finite normal, `L_i` unramified outside `S`, and `σ` in the inertia group of a prime `P`
of `𝓞_M` above `v ∉ S`: the restriction of `σ` to `L_i` lies in the inertia group of `P ∩ 𝓞_{L_i}`
(the argument of `map_mem_inertia_comap`), which is trivial, so `σ` fixes `L_i`. -/
theorem fix_of_mem_inertia {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (Li M : IntermediateField K (AlgebraicClosure K))
    (hle : Li ≤ M) [FiniteDimensional K Li] [Normal K Li] [FiniteDimensional K M] [Normal K M]
    (hLi : IsUnramifiedOutside K S Li) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (P : Ideal (𝓞 M)) [P.IsPrime] (hP : P.LiesOver v.asIdeal) (σ : M ≃ₐ[K] M)
    (hσ : σ ∈ P.inertia (M ≃ₐ[K] M)) (x : AlgebraicClosure K) (hx : x ∈ Li) :
    σ ⟨x, hle hx⟩ = ⟨x, hle hx⟩ := by
  set χ := σ.liftNormal (AlgebraicClosure K)
  set τ : Li ≃ₐ[K] Li := χ.restrictNormal Li
  have hcompat : ∀ y : Li, ((τ y : Li) : AlgebraicClosure K) =
      ((σ ⟨y, hle y.2⟩ : M) : AlgebraicClosure K) := by
    intro y
    calc ((τ y : Li) : AlgebraicClosure K) = algebraMap Li (AlgebraicClosure K) (τ y) := rfl
      _ = χ (algebraMap Li (AlgebraicClosure K) y) := AlgEquiv.restrictNormal_commutes χ Li y
      _ = χ (algebraMap M (AlgebraicClosure K) ⟨y, hle y.2⟩) := rfl
      _ = algebraMap M (AlgebraicClosure K) (σ ⟨y, hle y.2⟩) :=
        AlgEquiv.liftNormal_commutes σ (AlgebraicClosure K) _
  set f : 𝓞 Li →+* 𝓞 M := RingOfIntegers.mapRingHom (IntermediateField.inclusion hle).toRingHom
  have hfalg : f.comp (algebraMap (𝓞 K) (𝓞 Li)) = algebraMap (𝓞 K) (𝓞 M) := by
    ext a
    rfl
  have hQprime : (P.comap f).IsPrime := Ideal.comap_isPrime f P
  have hQlo : (P.comap f).LiesOver v.asIdeal := by
    constructor
    rw [Ideal.under, Ideal.comap_comap, hfalg]
    exact hP.over
  have hτ : τ ∈ (P.comap f).inertia (Li ≃ₐ[K] Li) := by
    rw [Ideal.mem_inertia] at hσ ⊢
    intro a
    rw [Ideal.mem_comap, map_sub]
    have : f (τ • a) = σ • f a := by
      apply RingOfIntegers.ext
      apply Subtype.ext
      exact hcompat (a : Li)
    rw [this]
    exact hσ (f a)
  have hτ1 : τ = 1 := by
    have h := inertia_eq_bot_of_isUnramifiedOutside Li hLi hv (P.comap f) hQlo
    rw [h] at hτ
    exact hτ
  apply Subtype.ext
  have := hcompat ⟨x, hx⟩
  rw [hτ1] at this
  exact this.symm

/-- **(ii) `UnramifiedOutsideSup`** (`PROVED`): an inertia element `σ` at a prime of `𝓞_{L₁ ⊔ L₂}`
above `v ∉ S` is trivial on `L₁` and on `L₂` (`fix_of_mem_inertia`), hence `σ = 1`
(`algEquiv_sup_eq_one`); so the inertia group is trivial and `L₁ ⊔ L₂` is unramified there. -/
theorem unramifiedOutsideSup_proof : UnramifiedOutsideSup := by
  intro K _ _ S L₁ L₂ h₁ h₂
  obtain ⟨hf₁, hn₁, hu₁⟩ := h₁
  obtain ⟨hf₂, hn₂, hu₂⟩ := h₂
  rw [RankCounts.KummerS.isUnramifiedOutside_iff]
  intro v hv P _ hP
  have : IsGalois K ↥(L₁ ⊔ L₂) := IsGalois.mk
  rw [Ideal.isUnramifiedAt_iff_inertia_eq_bot, Subgroup.eq_bot_iff_forall]
  intro σ hσ
  exact algEquiv_sup_eq_one L₁ L₂ σ
    (fun x hx => fix_of_mem_inertia L₁ (L₁ ⊔ L₂) le_sup_left hu₁ hv P hP σ hσ x hx)
    (fun x hx => fix_of_mem_inertia L₂ (L₁ ⊔ L₂) le_sup_right hu₂ hv P hP σ hσ x hx)

end CompositumProof

/-! ### `h2` from full `2`-power torsion, unconditionally -/

/-- **(b2) `FiniteUnramifiedSupport`** (`PROVED`). -/
theorem finiteUnramifiedSupport_proof : FiniteUnramifiedSupport :=
  finiteUnramifiedSupport_of_sup unramifiedOutsideSup_proof

/-- **The ramification step `TwoPowerRootsRamified`** (`PROVED`). -/
theorem twoPowerRootsRamified_proof : TwoPowerRootsRamified :=
  twoPowerRootsRamified_of_finiteUnramifiedSupport finiteUnramifiedSupport_proof

/-- **`h2` from full `2`-power torsion** (`PROVED`): if `E[2^n] ⊆ E(K_S)` for every `n`, then `S`
contains every place above `2`. The consumers `*_of_ramified` take
`twoPowerRootsRamified_proof`. -/
theorem h2_of_hasFullTwoTorsion_proof {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]
    [HasFullTwoTorsion K S W] :
    ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
  h2_of_hasFullTwoTorsion twoPowerRootsRamified_proof W

end ZInQ.Contrib.CloudB3RC53.Finiteness
