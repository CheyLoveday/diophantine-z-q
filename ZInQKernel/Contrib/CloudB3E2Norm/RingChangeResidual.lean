import ZInQKernel.Contrib.CloudB3E2Norm.GenCxResidual

/-!
# Residual cohomology along a ring isomorphism

Toward the last piece of `GenCxResidualIso` (the stage rings `StageRing s ≃ Acoef s`): for local
rings `R ≃+* R'` and complexes over them related by degreewise additive isomorphisms that are
semilinear along the ring isomorphism and commute with the differentials, the residual
cohomologies have the same rank, and one is finite iff the other is.

* `subquotientSEquiv` (definition): a semilinear equivalence of subquotients `ker g / im f` from
  commuting semilinear equivalences;
* `residueTensorSEquiv` (definition): `k ⊗_R X ≃ k' ⊗_{R'} X'` semilinear along the residue-field
  isomorphism, for a semilinear additive isomorphism `X ≃ X'`;
* `residualSEquivOfRingEquiv` (definition), **`residualFinrank_eq_of_ringEquiv`**,
  **`residualFinite_iff_of_ringEquiv`** (PROVED);
* **`genCxResidualIso_of_ringChange`** (PROVED): `GenCxResidualIso` from the place-by-place
  condition isomorphisms and reference complexes over rings isomorphic to the stage rings (for the
  contributor's standard-old family, over `Acoef s`), related to the Galois Selmer complexes over
  `StageRing s` by degreewise semilinear additive isomorphisms commuting with the differentials.

What remains of `GenCxResidualIso` for the actual presentation: the place-by-place condition
isomorphisms (old places: `Δ s` against the standard old conditions; new places: `frobCx` against
`urAt`) and the degreewise semilinear identification of the Galois Selmer complex over
`StageRing s` with the standard-old Selmer complex over `Acoef s`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.St0Shape

open IsLocalRing TensorProduct
open ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

section Subquotient

variable {k k' : Type*} [CommRing k] [CommRing k'] {σ : k →+* k'} {σ' : k' →+* k}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {V W Z V' W' Z' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup Z] [Module k Z] [AddCommGroup V'] [Module k' V'] [AddCommGroup W'] [Module k' W']
  [AddCommGroup Z'] [Module k' Z']

/-- **A semilinear equivalence of subquotients** `ker g / im f ≃ ker g' / im f'` from commuting
semilinear equivalences. Kind: definition. -/
def subquotientSEquiv (f : V →ₗ[k] W) (g : W →ₗ[k] Z) (f' : V' →ₗ[k'] W') (g' : W' →ₗ[k'] Z')
    (eV : V ≃ₛₗ[σ] V') (eW : W ≃ₛₗ[σ] W') (eZ : Z ≃ₛₗ[σ] Z')
    (hf : ∀ x, eW (f x) = f' (eV x)) (hg : ∀ y, eZ (g y) = g' (eW y)) :
    subquotientOf f g ≃ₛₗ[σ] subquotientOf f' g' :=
  have hker : (LinearMap.ker g).map (eW : W →ₛₗ[σ] W') = LinearMap.ker g' := by
    ext y'
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hy
      rw [LinearMap.mem_ker]
      change g' (eW y) = 0
      rw [← hg, hy, map_zero]
    · intro hy'
      refine ⟨eW.symm y', ?_, eW.apply_symm_apply y'⟩
      rw [LinearMap.mem_ker] at hy'
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      apply eZ.injective
      rw [hg, LinearEquiv.apply_symm_apply, hy', map_zero]
  let eK : LinearMap.ker g ≃ₛₗ[σ] LinearMap.ker g' :=
    (eW.submoduleMap (LinearMap.ker g)).trans (LinearEquiv.ofEq _ _ hker)
  Submodule.Quotient.equiv _ _ eK (by
    ext ⟨y', hy'⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.mem_range]
    constructor
    · rintro ⟨⟨y, hy⟩, ⟨x, hx⟩, he⟩
      refine ⟨eV x, ?_⟩
      have := congrArg Subtype.val he
      simp only [LinearEquiv.coe_coe] at this
      rw [← hf, hx]
      exact this
    · rintro ⟨x', hx'⟩
      refine ⟨⟨eW.symm y', ?_⟩, ⟨eV.symm x', ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker] at hy' ⊢
        apply eZ.injective
        rw [hg, LinearEquiv.apply_symm_apply, hy', map_zero]
      · apply eW.injective
        rw [hf, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hx']
      · apply Subtype.ext
        exact eW.apply_symm_apply y')

end Subquotient

section Tensor

variable {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (e : R ≃+* R')
  {X X' : Type} [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R' X'] (f : X ≃+ X')
  (hf : ∀ (r : R) (x : X), f (r • x) = e r • f x)

/-- The residue-field isomorphism of a ring isomorphism of local rings. Kind: definition. -/
abbrev resEquiv : ResidueField R ≃+* ResidueField R' := ResidueField.mapEquiv e

theorem resEquiv_smul (r : R) (a : ResidueField R) :
    resEquiv e (r • a) = e r • resEquiv e a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1

/-- `a ⊗ x ↦ ē a ⊗ f x`, additively. Kind: definition. -/
def residueTensorHom : ResidueField R ⊗[R] X →+ ResidueField R' ⊗[R'] X' :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun x => resEquiv e a ⊗ₜ[R'] f x
          map_zero' := by rw [map_zero, tmul_zero]
          map_add' := fun x y => by rw [map_add, tmul_add] }
      map_zero' := by ext x; simp
      map_add' := fun a b => by ext x; simp [add_tmul] }
    (fun r a x => by
      change resEquiv e (r • a) ⊗ₜ[R'] f x = resEquiv e a ⊗ₜ[R'] f (r • x)
      rw [resEquiv_smul, hf, smul_tmul])

theorem residueTensorHom_tmul (a : ResidueField R) (x : X) :
    residueTensorHom e f hf (a ⊗ₜ x) = resEquiv e a ⊗ₜ f x := rfl

/-- The inverse pair of the residue-field isomorphism. Kind: PROVED (instance). -/
theorem resInvPair : RingHomInvPair (resEquiv e : ResidueField R →+* ResidueField R')
    ((resEquiv e).symm : ResidueField R' →+* ResidueField R) :=
  RingHomInvPair.of_ringEquiv _

theorem resInvPair' : RingHomInvPair ((resEquiv e).symm : ResidueField R' →+* ResidueField R)
    (resEquiv e : ResidueField R →+* ResidueField R') :=
  RingHomInvPair.of_ringEquiv_symm _

attribute [local instance] resInvPair resInvPair'

omit [IsLocalRing R] [IsLocalRing R'] in
include hf in
theorem hf_symm : ∀ (r : R') (x : X'), f.symm (r • x) = e.symm r • f.symm x := by
  intro r x
  apply f.injective
  rw [AddEquiv.apply_symm_apply, hf, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- **`k ⊗_R X ≃ k' ⊗_{R'} X'`, semilinear along the residue-field isomorphism**.
Kind: definition. -/
def residueTensorSEquiv :
    ResidueField R ⊗[R] X ≃ₛₗ[(resEquiv e : ResidueField R →+* ResidueField R')]
      ResidueField R' ⊗[R'] X' where
  toFun := residueTensorHom e f hf
  invFun := residueTensorHom e.symm f.symm (hf_symm e f hf)
  map_add' := map_add _
  map_smul' c z := by
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      rw [smul_tmul', residueTensorHom_tmul, residueTensorHom_tmul, smul_tmul', smul_eq_mul,
        smul_eq_mul, map_mul]
      rfl
    | add z w hz hw => rw [smul_add, map_add, map_add, hz, hw, smul_add]
  left_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      rw [residueTensorHom_tmul, residueTensorHom_tmul, AddEquiv.symm_apply_apply]
      congr 1
      exact (resEquiv e).symm_apply_apply a
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  right_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      rw [residueTensorHom_tmul, residueTensorHom_tmul, AddEquiv.apply_symm_apply]
      congr 1
      exact (resEquiv e).apply_symm_apply a
    | add z w hz hw => rw [map_add, map_add, hz, hw]

end Tensor

section Complexes

variable {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (e : R ≃+* R')
  {C : GCx R} {C' : GCx R'} (f : ∀ n, C.X n ≃+ C'.X n)
  (hf : ∀ n (r : R) (x : C.X n), f n (r • x) = e r • f n x)
  (hd : ∀ i j (h : i + 1 = j) (x : C.X i), f j (C.d i j h x) = C'.d i j h (f i x))

attribute [local instance] resInvPair resInvPair'

include hd in
theorem residueTensor_comm (a b : ℤ) (h : a + 1 = b) (z : ResidueField R ⊗[R] C.X a) :
    residueTensorSEquiv e (f b) (hf b) (residualDiff C a b h z) =
      residualDiff C' a b h (residueTensorSEquiv e (f a) (hf a) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c x =>
    change residueTensorHom e (f b) (hf b) (c ⊗ₜ C.d a b h x) =
      (C'.d a b h).baseChange (ResidueField R') (residueTensorHom e (f a) (hf a) (c ⊗ₜ x))
    rw [residueTensorHom_tmul, residueTensorHom_tmul, LinearMap.baseChange_tmul, hd]
  | add z w hz hw => rw [map_add, map_add, hz, hw, ← map_add, ← map_add]

/-- **The residual cohomologies along a ring isomorphism** (semilinear along the residue-field
isomorphism). Kind: definition. -/
def residualSEquivOfRingEquiv (n : ℤ) :
    residualCohomologyAt C n ≃ₛₗ[(resEquiv e : ResidueField R →+* ResidueField R')]
      residualCohomologyAt C' n :=
  subquotientSEquiv _ _ _ _ (residueTensorSEquiv e (f (n - 1)) (hf (n - 1)))
    (residueTensorSEquiv e (f n) (hf n)) (residueTensorSEquiv e (f (n + 1)) (hf (n + 1)))
    (residueTensor_comm e f hf hd (n - 1) n (by omega))
    (residueTensor_comm e f hf hd n (n + 1) rfl)

include hf hd in
theorem residualRank_eq_of_ringEquiv (n : ℤ) :
    Module.rank (ResidueField R) (residualCohomologyAt C n) =
      Module.rank (ResidueField R') (residualCohomologyAt C' n) :=
  rank_eq_of_equiv_equiv (resEquiv e) (residualSEquivOfRingEquiv e f hf hd n).toAddEquiv
    (resEquiv e).bijective (fun c m => (residualSEquivOfRingEquiv e f hf hd n).map_smulₛₗ c m)

include hf hd in
/-- **Residual ranks are invariant under a ring isomorphism** (PROVED). -/
theorem residualFinrank_eq_of_ringEquiv (n : ℤ) :
    Module.finrank (ResidueField R) (residualCohomologyAt C n) =
      Module.finrank (ResidueField R') (residualCohomologyAt C' n) := by
  unfold Module.finrank
  rw [residualRank_eq_of_ringEquiv e f hf hd n]

include hf hd in
/-- **Residual finiteness is invariant under a ring isomorphism** (PROVED). -/
theorem residualFinite_iff_of_ringEquiv (n : ℤ) :
    Module.Finite (ResidueField R) (residualCohomologyAt C n) ↔
      Module.Finite (ResidueField R') (residualCohomologyAt C' n) := by
  rw [← Module.rank_lt_aleph0_iff, ← Module.rank_lt_aleph0_iff,
    residualRank_eq_of_ringEquiv e f hf hd n]

end Complexes

/-! ### `GenCxResidualIso` through a ring change -/

section Genuine

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  [∀ s, TopologicalSpace (StageRing s)]
  {M : ℕ → Type} [∀ s, AddCommGroup (M s)] [∀ s, Module (StageRing s) (M s)]
  [∀ s, DistribMulAction (GKS K S) (M s)] [∀ s, SMulCommClass (GKS K S) (StageRing s) (M s)]
  [∀ s, TopologicalSpace (M s)] [∀ s, DiscreteTopology (M s)]
  [∀ s, ContinuousSMul (GKS K S) (M s)]
  {Δ : ∀ s, LocalConditions (StageRing s) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (M s)}
  {ι : Type} [DecidableEq ι] {place : ι × Bool → Places K S}
  {X : ∀ s, (j : ι × Bool) → TopRep.{0} (StageRing s) (GUr K (place j).1)}
  {EU : ∀ s j, SplitInclusion (genuineUq K S (StageRing s) (place j) (X s j))
    (genuineLq K S (StageRing s) (M s) (place j))}

/-- **`GenCxResidualIso` through reference complexes over isomorphic rings** (PROVED): with the
place-by-place condition isomorphisms of `genCxResidualIso_of_conditions`, and at every stage
`s ≠ 0` a complex `Cref s` over a local ring `Rref s ≃+* StageRing s` (for the contributor's
standard-old family, `Acoef s`, with `Rk` its residual ranks), related to
`selCx (galoisSelData K S (StageRing s) (M s) (Δref s))` by degreewise additive isomorphisms that
are semilinear and commute with the differentials, the named input holds with the reference
ranks. -/
theorem genCxResidualIso_of_ringChange {Rk : ℕ → ℤ → ℕ} (hS : S₀ ⊆ S)
    (hinj : Function.Injective place) (hw : ∀ j, (place j).1 ∉ S₀)
    (hcov : ∀ v ∈ S, v ∈ S₀ ∨ ∃ j, (place j).1 = v)
    (Δref : ∀ s, GaloisLocalConditions K S (StageRing s) (M s))
    (ψ : ∀ s i, GHom ((presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) ∅).U i)
      ((Δref s).U (presPlaceEquiv hS hinj hw hcov i)))
    (hψ : ∀ s i n, Function.Bijective ((ψ s i).f n n rfl))
    (hψι : ∀ s i n x, ((Δref s).i (presPlaceEquiv hS hinj hw hcov i)).f n n rfl
        ((ψ s i).f n n rfl x) =
      ((presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) ∅).i i).f n n rfl x)
    (Rref : ℕ → Type) [∀ s, CommRing (Rref s)] [∀ s, IsLocalRing (Rref s)]
    (eR : ∀ s, StageRing s ≃+* Rref s) (Cref : ∀ s, GCx (Rref s))
    (fR : ∀ s n, (selCx (galoisSelData K S (StageRing s) (M s) (Δref s))).X n ≃+ (Cref s).X n)
    (hfR : ∀ s n (r : StageRing s) x, fR s n (r • x) = eR s r • fR s n x)
    (hdR : ∀ s i j (h : i + 1 = j) x,
      fR s j ((selCx (galoisSelData K S (StageRing s) (M s) (Δref s))).d i j h x) =
        (Cref s).d i j h (fR s i x))
    (hfin : ∀ s [NeZero s] n, Module.Finite (ResidueField (Rref s))
      (residualCohomologyAt (Cref s) n))
    (hrank : ∀ s [NeZero s] n,
      Module.finrank (ResidueField (Rref s)) (residualCohomologyAt (Cref s) n) = Rk s n) :
    GenCxResidualIso K S₀ S M Δ place X EU Rk :=
  genCxResidualIso_of_conditions hS hinj hw hcov Δref ψ hψ hψι
    (fun s _ n => (residualFinite_iff_of_ringEquiv (eR s) (fR s) (hfR s) (hdR s) n).2 (hfin s n))
    (fun s _ n => (residualFinrank_eq_of_ringEquiv (eR s) (fR s) (hfR s) (hdR s) n).trans
      (hrank s n))

end Genuine

end ZInQ.Contrib.CloudB3E2.St0Shape
