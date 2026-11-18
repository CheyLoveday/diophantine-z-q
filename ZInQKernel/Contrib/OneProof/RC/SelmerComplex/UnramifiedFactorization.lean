import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.SqrtMem
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.PrimesAbove
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.BaseChange
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Maximal
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField

/-!
# `K_S/K` is unramified at every prime outside `S`: the localization factors through `G_q/I_q`

For a number field `K`, a set `S` of finite primes and a finite prime `q ∉ S`, the localization
`p_q : G_{K_q} → G_{K,S} = Gal(K_S/K)` factors through the unramified quotient
`Gal(K_q^{ur}/K_q)` of `G_{K_q}`. This is the statement `UnramifiedAtFactorization K S`.

Proof.
* Every finite Galois subextension `L ⊆ K̄` unramified outside `S` is unramified at `q`: every
  prime `w` of `𝒪_L` above `q` has ramification index one, so the completed extension `L_w/K_q`
  is an unramified extension of local fields (the local ramification index of a completion is the
  global one). Hence the image of `L_w` under any `K_q`-embedding into `K̄_q` lies in `K_q^{ur}`.
* `L/K` is normal, so all `K`-embeddings of `L` into `K̄_q` have the same image; in particular the
  embedding of algebraic closures `K̄ → K̄_q` defining the decomposition map carries `L` into
  `K_q^{ur}`.
* An element of `G_{K_q}` acting trivially on `K_q^{ur}` therefore fixes every such `L`, hence
  their compositum `K_S`: the kernel of `G_{K_q} → Gal(K_q^{ur}/K_q)` lies in the kernel of `p_q`.
* `G_{K_q}` is compact and `Gal(K_q^{ur}/K_q)` is Hausdorff, so the continuous surjection
  `G_{K_q} → Gal(K_q^{ur}/K_q)` is a quotient map, and `p_q` descends to a continuous
  homomorphism `ψ_q` with `p_q = ψ_q ∘ res`.

Main results (all PROVED):
* `exists_continuousMonoidHom_factor`: a continuous homomorphism out of a compact group factors
  continuously through a continuous surjection onto a Hausdorff group whose kernel it kills.
* `decompLift_mem_maximalUnramifiedExtension`: the local–global link above.
* `locMap_eq_one_of_urRes_eq_one`: the kernel containment `ker(res) ⊆ ker(p_q)`.
* `unramifiedAtFactorization_of_kernel`: the factorization from the kernel containment.
* `unramifiedAtFactorization`: `UnramifiedAtFactorization K S` for every `S`.
* `urFactor`, `galoisSupportDataUr`: the genuine support change of Nekovář 7.8.8(ii) with the
  canonical factorizations at the new places (no factorization input left), and
  `supportChange_of_print_ur`: its quasi-isomorphy from the PRINT `NekovarProp788ii`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.RankCounts

/-! ### Factorization through a quotient of a compact group -/

section Factor

variable {G Q H : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [Group Q]
  [TopologicalSpace Q] [T2Space Q] [Group H] [TopologicalSpace H]

/-- **Factorization through a quotient.** Let `π : G → Q` be a continuous surjective homomorphism
from a compact group onto a Hausdorff group, and `φ : G → H` a continuous homomorphism with
`ker π ⊆ ker φ`. Then `φ = ψ ∘ π` for a continuous homomorphism `ψ : Q → H` (`π` is closed, hence
a quotient map). -/
theorem exists_continuousMonoidHom_factor (π : G →ₜ* Q) (hπ : Function.Surjective π)
    (φ : G →ₜ* H) (hker : ∀ g, π g = 1 → φ g = 1) :
    ∃ ψ : Q →ₜ* H, ∀ g, φ g = ψ (π g) := by
  let π₀ : G →* Q := π
  let φ₀ : G →* H := φ
  have hk : π₀.ker ≤ φ₀.ker := fun g hg => hker g hg
  let ψ₀ : Q →* H := π₀.liftOfSurjective hπ ⟨φ₀, hk⟩
  have hcomp : ∀ g, ψ₀ (π g) = φ g := fun g =>
    π₀.liftOfRightInverse_comp_apply _ _ ⟨φ₀, hk⟩ g
  have hq : Topology.IsQuotientMap π :=
    (π.continuous.isClosedMap).isQuotientMap π.continuous hπ
  have hcont : Continuous ψ₀ := by
    rw [hq.continuous_iff]
    have : (ψ₀ ∘ π) = φ := funext hcomp
    rw [this]
    exact φ.continuous
  exact ⟨⟨ψ₀, hcont⟩, fun g => (hcomp g).symm⟩

end Factor

variable (K : Type) [Field K] [NumberField K]

/-! ### The embedding of algebraic closures behind the decomposition map -/

/-- The embedding `K̄ → K̄_q` of algebraic closures over `K → K_q` used by the decomposition map
`decompMap K q`. -/
def decompLift (q : HeightOneSpectrum (𝓞 K)) :
    AlgebraicClosure K →+* AlgebraicClosure (q.adicCompletion K) :=
  letI : Algebra K (q.adicCompletion K) := (algebraMap K (q.adicCompletion K)).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure (q.adicCompletion K)).toRingHom

/-- The decomposition map is characterized by `ι (decompMap g x) = g (ι x)` for the embedding
`ι : K̄ → K̄_q`. -/
theorem decompLift_decompMap (q : HeightOneSpectrum (𝓞 K))
    (σ : Field.absoluteGaloisGroup (q.adicCompletion K)) (x : AlgebraicClosure K) :
    decompLift K q (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K q σ) x) =
      @id (AlgebraicClosure (q.adicCompletion K) ≃ₐ[q.adicCompletion K]
        AlgebraicClosure (q.adicCompletion K)) σ (decompLift K q x) := by
  let _ : Algebra K (q.adicCompletion K) := (algebraMap K (q.adicCompletion K)).toAlgebra
  let g : AlgebraicClosure K →ₐ[K] AlgebraicClosure (q.adicCompletion K) := IsAlgClosed.lift
  let _ : Algebra (AlgebraicClosure K) (AlgebraicClosure (q.adicCompletion K)) := g.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalarsHom K
    (@id (AlgebraicClosure (q.adicCompletion K) ≃ₐ[q.adicCompletion K]
      AlgebraicClosure (q.adicCompletion K)) σ)) (AlgebraicClosure K) x

/-- The embedding `K̄ → K̄_q` is a `K`-algebra map. -/
theorem decompLift_algebraMap (q : HeightOneSpectrum (𝓞 K)) (c : K) :
    decompLift K q (algebraMap K (AlgebraicClosure K) c) =
      algebraMap K (AlgebraicClosure (q.adicCompletion K)) c := by
  let _ : Algebra K (q.adicCompletion K) := (algebraMap K (q.adicCompletion K)).toAlgebra
  exact (IsAlgClosed.lift :
    AlgebraicClosure K →ₐ[K] AlgebraicClosure (q.adicCompletion K)).commutes c

/-- An element of `G_{K_q}` in the kernel of the restriction to `K_q^{ur}` fixes `K_q^{ur}`
pointwise. -/
theorem fix_of_urRes_eq_one (q : HeightOneSpectrum (𝓞 K)) (g : Gloc K q)
    (hg : urRes K q g = 1) (y : AlgebraicClosure (q.adicCompletion K))
    (hy : y ∈ TauCeti.maximalUnramifiedExtension (q.adicCompletion K)
      (AlgebraicClosure (q.adicCompletion K))) :
    @id (AlgebraicClosure (q.adicCompletion K) ≃ₐ[q.adicCompletion K]
      AlgebraicClosure (q.adicCompletion K)) g y = y := by
  have h := AlgEquiv.restrictNormal_commutes
    (@id (AlgebraicClosure (q.adicCompletion K) ≃ₐ[q.adicCompletion K]
      AlgebraicClosure (q.adicCompletion K)) g)
    (TauCeti.maximalUnramifiedExtension (q.adicCompletion K)
      (AlgebraicClosure (q.adicCompletion K))) ⟨y, hy⟩
  have h1 : AlgEquiv.restrictNormal (@id (AlgebraicClosure (q.adicCompletion K) ≃ₐ[q.adicCompletion K]
      AlgebraicClosure (q.adicCompletion K)) g) (TauCeti.maximalUnramifiedExtension
        (q.adicCompletion K) (AlgebraicClosure (q.adicCompletion K))) = 1 := hg
  rw [h1] at h
  exact h.symm

/-! ### The local–global link -/

open scoped AdicCompletionExtension in
/-- **A finite Galois subextension unramified at `q` lands in `K_q^{ur}`.** Let `L ⊆ K̄` be a
finite normal extension of `K` unramified outside `S`, and `q ∉ S`. Then the embedding
`K̄ → K̄_q` carries `L` into the maximal unramified extension `K_q^{ur}` of `K_q`. -/
theorem decompLift_mem_maximalUnramifiedExtension (S : Set (HeightOneSpectrum (𝓞 K)))
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S) (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [Normal K L] (hL : IsUnramifiedOutside K S L)
    (x : AlgebraicClosure K) (hx : x ∈ L) :
    decompLift K q x ∈ TauCeti.maximalUnramifiedExtension (q.adicCompletion K)
      (AlgebraicClosure (q.adicCompletion K)) := by
  -- a prime `w` of `𝒪_L` above `q`; it is unramified, so `L_w/K_q` is unramified
  obtain ⟨w, hw⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) q
  have hlo : w.asIdeal.LiesOver q.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hw.symm⟩
  have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    (KummerS.isUnramifiedOutside_iff K S L).1 hL q hq w.asIdeal w.isPrime hlo
  have : TauCeti.IsUnramified (q.adicCompletion K) (w.adicCompletion L) :=
    HeightOneSpectrum.isUnramified_adicCompletion_of_isUnramifiedAt q w
  have : Algebra.IsAlgebraic (q.adicCompletion K) (w.adicCompletion L) :=
    Algebra.IsAlgebraic.of_finite _ _
  -- a `K_q`-embedding `j : L_w → K̄_q`; its image `E` is unramified, hence inside `K_q^{ur}`
  let j : w.adicCompletion L →ₐ[q.adicCompletion K] AlgebraicClosure (q.adicCompletion K) :=
    IsAlgClosed.lift
  let E : IntermediateField (q.adicCompletion K) (AlgebraicClosure (q.adicCompletion K)) :=
    j.fieldRange
  let e : w.adicCompletion L ≃ₐ[q.adicCompletion K] E := AlgEquiv.ofInjectiveField j
  have : Module.Finite (q.adicCompletion K) E := Module.Finite.equiv e.toLinearEquiv
  let _ := TauCeti.finiteIntermediateFieldValuativeRel (q.adicCompletion K)
    (AlgebraicClosure (q.adicCompletion K)) E
  let _ := TauCeti.finiteIntermediateFieldTopology (q.adicCompletion K)
    (AlgebraicClosure (q.adicCompletion K)) E
  have := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField (q.adicCompletion K)
    (AlgebraicClosure (q.adicCompletion K)) E
  have := TauCeti.finiteIntermediateField_valuativeExtension (q.adicCompletion K)
    (AlgebraicClosure (q.adicCompletion K)) E
  have : TauCeti.IsUnramified (q.adicCompletion K) E := TauCeti.IsUnramified.of_algEquiv e
  have hE : E ≤ TauCeti.maximalUnramifiedExtension (q.adicCompletion K)
      (AlgebraicClosure (q.adicCompletion K)) := E.le_maximalUnramifiedExtension
  -- the `K`-embedding `ψ : L → L_w → K̄_q` lands in `K_q^{ur}`
  let ψ : L →ₐ[K] AlgebraicClosure (q.adicCompletion K) :=
    { toRingHom := j.toRingHom.comp (algebraMap L (w.adicCompletion L))
      commutes' := fun c => by
        change j (algebraMap L (w.adicCompletion L) (algebraMap K L c)) = _
        have h1 : algebraMap L (w.adicCompletion L) (algebraMap K L c) =
            algebraMap (q.adicCompletion K) (w.adicCompletion L)
              (algebraMap K (q.adicCompletion K) c) :=
          (q.adicCompletionExtension_coe K L w c).symm
        rw [h1, AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }
  have hψ : ∀ y, ψ y ∈ TauCeti.maximalUnramifiedExtension (q.adicCompletion K)
      (AlgebraicClosure (q.adicCompletion K)) := fun y => hE ⟨_, rfl⟩
  -- the `K`-embedding `φ : L → K̄ → K̄_q`; by normality it has the same image as `ψ`
  let φ : L →ₐ[K] AlgebraicClosure (q.adicCompletion K) :=
    { toRingHom := (decompLift K q).comp L.val.toRingHom
      commutes' := fun c => decompLift_algebraMap K q c }
  let F : IntermediateField K (AlgebraicClosure (q.adicCompletion K)) := ψ.fieldRange
  let eψ : L ≃ₐ[K] F := AlgEquiv.ofInjectiveField ψ
  have : Normal K F := Normal.of_algEquiv eψ
  have hF := AlgHom.fieldRange_of_normal (φ.comp eψ.symm.toAlgHom)
  have hmem : φ ⟨x, hx⟩ ∈ F := by
    rw [← hF]
    exact AlgHom.mem_fieldRange.2 ⟨eψ ⟨x, hx⟩, by simp⟩
  obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.1 hmem
  change φ ⟨x, hx⟩ ∈ _
  rw [← hy]
  exact hψ y

/-! ### The kernel containment and the factorization -/

/-- **Inertia acts trivially on `K_S`.** For `q ∉ S`, an element of `G_{K_q}` acting trivially on
`K_q^{ur}` fixes `K_S` pointwise through the decomposition map. -/
theorem decompMap_fix_of_urRes_eq_one (S : Set (HeightOneSpectrum (𝓞 K)))
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S) (g : Gloc K q) (hg : urRes K q g = 1)
    (x : AlgebraicClosure K) (hx : x ∈ unramifiedOutside K S) :
    @id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K q g) x = x := by
  set τ := @id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K q g) with hτ
  have hL : ∀ L : IntermediateField K (AlgebraicClosure K),
      (FiniteDimensional K L ∧ Normal K L ∧ IsUnramifiedOutside K S L) → ∀ y ∈ L, τ y = y := by
    rintro L ⟨h1, h2, h3⟩ y hy
    apply (decompLift K q).injective
    rw [hτ, decompLift_decompMap]
    exact fix_of_urRes_eq_one K q g hg _
      (decompLift_mem_maximalUnramifiedExtension K S q hq L h3 y hy)
  have hle : unramifiedOutside K S ≤ IntermediateField.fixedField (Subgroup.zpowers τ) := by
    refine iSup₂_le fun L hLp => ?_
    rw [IntermediateField.le_iff_le, Subgroup.zpowers_le,
      IntermediateField.mem_fixingSubgroup_iff]
    exact hL L hLp
  rw [IntermediateField.le_iff_le, Subgroup.zpowers_le,
    IntermediateField.mem_fixingSubgroup_iff] at hle
  exact hle x hx

/-- **The kernel containment** `ker(G_{K_q} → Gal(K_q^{ur}/K_q)) ⊆ ker(p_q)` for `q ∉ S`. -/
theorem locMap_eq_one_of_urRes_eq_one (S : Set (HeightOneSpectrum (𝓞 K)))
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S) (g : Gloc K q) (hg : urRes K q g = 1) :
    locMap K S q g = 1 := by
  change resAbs K S (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K q g)) =
    (1 : GaloisGroupS K S)
  refine AlgEquiv.ext fun y => Subtype.ext ?_
  rw [resAbs_apply_coe]
  exact decompMap_fix_of_urRes_eq_one K S q hq g hg y.1 y.2

/-- The restriction `G_{K_q} → Gal(K_q^{ur}/K_q)` is surjective. -/
theorem urRes_surjective (q : HeightOneSpectrum (𝓞 K)) : Function.Surjective (urRes K q) :=
  AlgEquiv.restrictNormalHom_surjective _

/-- **The factorization from the kernel containment.** If for every `q ∉ S` the kernel of
`G_{K_q} → Gal(K_q^{ur}/K_q)` is contained in the kernel of the localization `p_q`, then `p_q`
factors continuously through `Gal(K_q^{ur}/K_q)`. -/
theorem unramifiedAtFactorization_of_kernel (S : Set (HeightOneSpectrum (𝓞 K)))
    (h : ∀ q : HeightOneSpectrum (𝓞 K), q ∉ S →
      ∀ g : Gloc K q, urRes K q g = 1 → locMap K S q g = 1) :
    UnramifiedAtFactorization K S := by
  intro q hq
  have : CompactSpace (Gloc K q) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure (q.adicCompletion K) ≃ₐ[q.adicCompletion K]
      AlgebraicClosure (q.adicCompletion K)))
  have : T2Space (GUr K q) := krullTopology_t2
  exact exists_continuousMonoidHom_factor (urRes K q) (urRes_surjective K q) (locMap K S q)
    (h q hq)

/-- **`K_S/K` is unramified at every `q ∉ S`** (the statement `UnramifiedAtFactorization`): the
localization `p_q : G_{K_q} → G_{K,S}` factors through `Gal(K_q^{ur}/K_q)` by a continuous
homomorphism. -/
theorem unramifiedAtFactorization (S : Set (HeightOneSpectrum (𝓞 K))) :
    UnramifiedAtFactorization K S :=
  unramifiedAtFactorization_of_kernel K S fun q hq g hg =>
    locMap_eq_one_of_urRes_eq_one K S q hq g hg

/-! ### The genuine support change without factorization inputs -/

section SupportChange

open ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {S S' : Set (HeightOneSpectrum (𝓞 K))}

/-- The factorization `ψ_q : Gal(K_q^{ur}/K_q) → G_{K,S}` of the localization at a new place
`q ∈ S' − S` (chosen by `unramifiedAtFactorization`). -/
def urFactor (q : NewPlaces K S S') : GUr K q.1 →ₜ* GKS K S :=
  Classical.choose (unramifiedAtFactorization K S q.1 q.2.2)

theorem urFactor_spec (q : NewPlaces K S S') (g : Gloc K q.1) :
    locMap K S q.1 g = urFactor K q (urRes K q.1 g) :=
  Classical.choose_spec (unramifiedAtFactorization K S q.1 q.2.2) g

/-- **The genuine support change `S ⊆ S'`** (Nekovář 7.8.8(ii), tex 3483–3498) with the unramified
conditions `C(G_q/I_q, M)` at the new places and the canonical factorizations `urFactor`: an
instance of the abstract `SupportChangeData` with no remaining input. -/
abbrev galoisSupportDataUr (hS : S ⊆ S') (k : Type) [CommRing k] (M : Type) [AddCommGroup M]
    [Module k M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]
    (Δ : GaloisLocalConditions K S k M) : SupportChangeData k :=
  galoisSupportData K hS k M (urFactor K) (urFactor_spec K) Δ

/-- **The genuine support comparison is a quasi-isomorphism** (from the PRINT `NekovarProp788ii`,
with the canonical factorizations). -/
theorem supportChange_of_print_ur (h : NekovarProp788ii K) (hS : S ⊆ S') (p : ℕ) {R : Type}
    [CommRing R] [IsLocalRing R] (hset : NekovarFiniteSetting K S p R) (hS' : S'.Finite)
    {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M]
    [SMulCommClass (GKS K S) R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul (GKS K S) M] [Finite M] (Δ : GaloisLocalConditions K S R M) :
    QuasiIso (GHom.toCC (supportMap (galoisSupportDataUr K hS R M Δ))) :=
  h S S' hS p R hset hS' M (urFactor K) (urFactor_spec K) Δ

end SupportChange

end ZInQ.Manuscript.RC.SelmerComplex
