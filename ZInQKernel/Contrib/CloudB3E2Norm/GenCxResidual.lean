import ZInQKernel.Contrib.CloudB3E2Norm.St0Shape
import ZInQKernel.Contrib.RC53Assist.ResidualFiniteness.StageResidual
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageArith

/-!
# Residual cohomology along isomorphisms of Selmer data

Manuscript `diophantine_zq.tex`, tex 4385–4414.

Toward discharging the named input `GenCxResidualIso` of `St0Shape`:

* `homologySubEquiv` (definition): the cohomology of a complex in degree `n` is its cocycles
  modulo coboundaries;
* **`residualEquivOfBijective`** (definition): a chain map with bijective components induces a
  linear equivalence of the residual cohomologies `Hⁿ(k ⊗ C) ≃ Hⁿ(k ⊗ C')`;
  `residualFinite_iff_of_bijective`, `residualFinrank_eq_of_bijective` (PROVED);
* **`residualEquivOfSelIso`** (definition) and its corollaries (PROVED): the same for the Selmer
  complexes of Selmer data related by componentwise bijective chain maps compatible with
  restriction and the condition maps;
* **`genCxResidualIso_of_selIso`** (PROVED): `GenCxResidualIso Rk` from, at every stage `s ≠ 0`,
  a componentwise isomorphism of Selmer data from the genuine `C_∅` to Selmer data with finite
  residual cohomology and residual ranks `Rk s`;
* `piCongrLin`, `piReindex` (definitions), **`selIsoReindex`** (definition): reindexing the places
  of Selmer data along an equivalence, with place-by-place isomorphisms of the conditions;
* `presPlace`, **`presPlaceEquiv`** (definitions): the places `Places K S₀ ⊕ (ι × Bool)` of the
  presentation are the places of `S` (for `place` injective, outside `S₀`, `S = S₀ ∪ range place`),
  with the same underlying primes;
* **`genCxResidualIso_of_conditions`** (PROVED): `GenCxResidualIso Rk` from place-by-place
  isomorphisms of the presentation's conditions with Galois local conditions `Δref s` at the
  places of `S`, and finite residual cohomology with ranks `Rk s` for
  `selCx (galoisSelData K S (StageRing s) (M s) (Δref s))`.

What remains of the named input: the place-by-place condition isomorphisms with the reference
family's conditions (old places: `Δ s` against the standard old conditions; new places: the
unramified Frobenius complex `frobCx` against `urAt`), and the reference finiteness and ranks over
`StageRing s` — the contributor's `stageSelmer_residualCohomologyFinite` and
`standardOld_producerBounds` are stated over `Acoef s`, so a transport along the ring isomorphism
`StageRing s ≃ Acoef s` is the last missing piece.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.St0Shape

open IsLocalRing
open ZInQ.Manuscript.RC.Limits ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.RC53Assist.InnerLimitArith (gcxBaseChange)

section Generic

variable {R : Type} [CommRing R]

/-- **The cohomology of a complex in degree `n` is its cocycles modulo coboundaries**.
Kind: definition. -/
def homologySubEquiv (C : GCx R) (n : ℤ) :
    C.toCC.homology n ≃ₗ[R] subquotientOf (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl) := by
  have e := C.toCC.homologyIsoSc' (n - 1) n (n + 1) (CochainComplex.prev ℤ n)
    (CochainComplex.next ℤ n)
  have hr : LinearMap.range (C.toCC.sc' (n - 1) n (n + 1)).moduleCatToCycles =
      (LinearMap.range (C.toCC.sc' (n - 1) n (n + 1)).f.hom).comap
        (LinearMap.ker (C.toCC.sc' (n - 1) n (n + 1)).g.hom).subtype :=
    LinearMap.range_codRestrict _ _ _
  have e2 : C.toCC.homology n ≃ₗ[R] subquotientOf (C.toCC.sc' (n - 1) n (n + 1)).f.hom
      (C.toCC.sc' (n - 1) n (n + 1)).g.hom :=
    (e.toLinearEquiv.trans (C.toCC.sc' (n - 1) n (n + 1)).moduleCatHomologyIso.toLinearEquiv).trans
      (Submodule.quotEquivOfEq _ _ hr)
  have hf : (C.toCC.sc' (n - 1) n (n + 1)).f.hom = C.d (n - 1) n (by omega) :=
    LinearMap.ext fun x => GCx.toCC_d_hom C (n - 1) n (by omega) x
  have hg : (C.toCC.sc' (n - 1) n (n + 1)).g.hom = C.d n (n + 1) rfl :=
    LinearMap.ext fun x => GCx.toCC_d_hom C n (n + 1) rfl x
  rw [hf, hg] at e2
  exact e2

variable [IsLocalRing R]

/-- **A chain map with bijective components induces an equivalence of residual cohomologies**.
Kind: definition. -/
def residualEquivOfBijective {C C' : GCx R} (f : GHom C C')
    (hf : ∀ n, Function.Bijective (f.f n n rfl)) (n : ℤ) :
    residualCohomologyAt C n ≃ₗ[ResidueField R] residualCohomologyAt C' n :=
  have hb : ∀ m, Function.Bijective
      ((ZInQ.Contrib.RC53Assist.ResidualFiniteness.ghomBaseChange (ResidueField R) f).f m m rfl) :=
    fun m => ((LinearEquiv.ofBijective (f.f m m rfl) (hf m)).baseChange R (ResidueField R)
      _ _).bijective
  ((homologySubEquiv (gcxBaseChange (ResidueField R) C) n).symm.trans
    (ZInQ.Contrib.RC53Assist.ResidualFiniteness.homologyIsoOfBijective _ hb n).toLinearEquiv).trans
    (homologySubEquiv (gcxBaseChange (ResidueField R) C') n)

/-- Residual finiteness transfers along a chain map with bijective components (PROVED). -/
theorem residualFinite_iff_of_bijective {C C' : GCx R} (f : GHom C C')
    (hf : ∀ n, Function.Bijective (f.f n n rfl)) (n : ℤ) :
    Module.Finite (ResidueField R) (residualCohomologyAt C n) ↔
      Module.Finite (ResidueField R) (residualCohomologyAt C' n) :=
  Module.Finite.equiv_iff (residualEquivOfBijective f hf n)

/-- Residual ranks agree along a chain map with bijective components (PROVED). -/
theorem residualFinrank_eq_of_bijective {C C' : GCx R} (f : GHom C C')
    (hf : ∀ n, Function.Bijective (f.f n n rfl)) (n : ℤ) :
    Module.finrank (ResidueField R) (residualCohomologyAt C n) =
      Module.finrank (ResidueField R) (residualCohomologyAt C' n) :=
  (residualEquivOfBijective f hf n).finrank_eq

/-- **An isomorphism of Selmer data induces an equivalence of the residual cohomologies of the
Selmer complexes** (componentwise bijective chain maps `φ_G`, `φ_U`, `φ_L` with
`φ_L ∘ res = res ∘ φ_G` and `φ_L ∘ ι = ι ∘ φ_U`). Kind: definition. -/
def residualEquivOfSelIso {D₁ D₂ : SelData R} (φG : GHom D₁.G D₂.G) (φU : GHom D₁.U D₂.U)
    (φL : GHom D₁.L D₂.L)
    (hres : ∀ i j (h : i = j) (a : D₁.G.X i),
      φL.f j j rfl (D₁.res.f i j h a) = D₂.res.f i j h (φG.f i i rfl a))
    (hι : ∀ i j (h : i = j) (u : D₁.U.X i),
      φL.f j j rfl (D₁.ι.f i j h u) = D₂.ι.f i j h (φU.f i i rfl u))
    (hG : ∀ n, Function.Bijective (φG.f n n rfl)) (hU : ∀ n, Function.Bijective (φU.f n n rfl))
    (hL : ∀ n, Function.Bijective (φL.f n n rfl)) (n : ℤ) :
    residualCohomologyAt (selCx D₁) n ≃ₗ[ResidueField R] residualCohomologyAt (selCx D₂) n :=
  residualEquivOfBijective
    (ZInQ.Contrib.RC53Assist.ResidualFiniteness.selCxMap φG φU φL hres hι)
    (ZInQ.Contrib.RC53Assist.ResidualFiniteness.selCxMap_bijective φG φU φL hres hι hG hU hL) n

/-- **A componentwise isomorphism of Selmer data** `D₁ → D₂`. Kind: definition (data with its
hypotheses). -/
structure SelIso (D₁ D₂ : SelData R) where
  /-- the global component -/
  φG : GHom D₁.G D₂.G
  /-- the condition component -/
  φU : GHom D₁.U D₂.U
  /-- the local component -/
  φL : GHom D₁.L D₂.L
  /-- compatibility with restriction -/
  hres : ∀ i j (h : i = j) (a : D₁.G.X i),
    φL.f j j rfl (D₁.res.f i j h a) = D₂.res.f i j h (φG.f i i rfl a)
  /-- compatibility with the condition maps -/
  hι : ∀ i j (h : i = j) (u : D₁.U.X i),
    φL.f j j rfl (D₁.ι.f i j h u) = D₂.ι.f i j h (φU.f i i rfl u)
  /-- bijectivity -/
  hG : ∀ n, Function.Bijective (φG.f n n rfl)
  hU : ∀ n, Function.Bijective (φU.f n n rfl)
  hL : ∀ n, Function.Bijective (φL.f n n rfl)

/-- The residual equivalence of a `SelIso`. Kind: definition. -/
def SelIso.residualEquiv {D₁ D₂ : SelData R} (e : SelIso D₁ D₂) (n : ℤ) :
    residualCohomologyAt (selCx D₁) n ≃ₗ[ResidueField R] residualCohomologyAt (selCx D₂) n :=
  residualEquivOfSelIso e.φG e.φU e.φL e.hres e.hι e.hG e.hU e.hL n

end Generic

/-! ### Reindexing the places of Selmer data -/

section Reindex

open ZInQ.Manuscript.RC.SelmerComplex

variable {k : Type} [CommRing k] {GS : Type} [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS]
  {ι₂ : Type} {Gv : ι₂ → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  {ι₁ : Type} (σ : ι₁ ≃ ι₂)

/-- The reindexing `∏_i P(σ i) → ∏_v P v` along `σ : ι₁ ≃ ι₂`, as a linear map.
Kind: definition. -/
def piCongrLin (P : ι₂ → Type) [∀ v, AddCommGroup (P v)] [∀ v, Module k (P v)] :
    (∀ i, P (σ i)) →ₗ[k] (∀ v, P v) where
  toFun := Equiv.piCongrLeft P σ
  map_add' x y := by
    funext v
    obtain ⟨a, rfl⟩ := σ.surjective v
    simp only [Equiv.piCongrLeft_apply_apply, Pi.add_apply]
  map_smul' c x := by
    funext v
    obtain ⟨a, rfl⟩ := σ.surjective v
    simp only [Equiv.piCongrLeft_apply_apply, Pi.smul_apply, RingHom.id_apply]

theorem piCongrLin_apply (P : ι₂ → Type) [∀ v, AddCommGroup (P v)] [∀ v, Module k (P v)]
    (x : ∀ i, P (σ i)) (a : ι₁) : piCongrLin (k := k) σ P x (σ a) = x a :=
  Equiv.piCongrLeft_apply_apply P σ x a

theorem piCongrLin_bijective (P : ι₂ → Type) [∀ v, AddCommGroup (P v)] [∀ v, Module k (P v)] :
    Function.Bijective (piCongrLin (k := k) σ P) :=
  (Equiv.piCongrLeft P σ).bijective

/-- The reindexing of a product of complexes along `σ : ι₁ ≃ ι₂`, from `∏_{i} A(σ i)` to
`∏_{v} A v`. Kind: definition. -/
def piReindex (A : ι₂ → GCx k) : GHom (piCx fun i => A (σ i)) (piCx A) where
  f i j h := by
    subst h
    exact piCongrLin (k := k) σ (fun v => (A v).X i)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    funext v
    obtain ⟨a, rfl⟩ := σ.surjective v
    change piCongrLin (k := k) σ (fun v => (A v).X i₁) (fun b => (A (σ b)).d i i₁ h₁ (x b))
        (σ a) = (A (σ a)).d i i₁ h₂ (piCongrLin (k := k) σ (fun v => (A v).X i) x (σ a))
    rw [piCongrLin_apply, piCongrLin_apply (k := k) σ (fun v => (A v).X i)
      (show ∀ b, (A (σ b)).X i from x) a]

theorem piReindex_apply (A : ι₂ → GCx k) (n : ℤ) (x : ∀ i, (A (σ i)).X n) (a : ι₁) :
    (piReindex σ A).f n n rfl x (σ a) = x a :=
  piCongrLin_apply (k := k) σ (fun v => (A v).X n) x a

theorem piReindex_bijective (A : ι₂ → GCx k) (n : ℤ) :
    Function.Bijective ((piReindex σ A).f n n rfl) :=
  piCongrLin_bijective σ _

/-- **Reindexing the places of Selmer data** (PROVED): for `σ : ι₁ ≃ ι₂`, conditions `Δ₁` at the
places `ι₁` (with the local groups `G_{σ i}`) and `Δ₂` at `ι₂`, and componentwise bijective chain
maps `ψ_i : U₁(i) → U₂(σ i)` compatible with the condition maps, the Selmer data are isomorphic.
Kind: definition. -/
def selIsoReindex (Δ₁ : LocalConditions k GS (fun i => Gv (σ i)) (fun i => loc (σ i)) M)
    (Δ₂ : LocalConditions k GS Gv loc M) (ψ : ∀ i, GHom (Δ₁.U i) (Δ₂.U (σ i)))
    (hψ : ∀ i n, Function.Bijective ((ψ i).f n n rfl))
    (hψι : ∀ i n (x : (Δ₁.U i).X n),
      (Δ₂.i (σ i)).f n n rfl ((ψ i).f n n rfl x) = (Δ₁.i i).f n n rfl x) :
    SelIso (selData k GS (fun i => Gv (σ i)) (fun i => loc (σ i)) M Δ₁)
      (selData k GS Gv loc M Δ₂) where
  φG := ⟨fun i j h => by subst h; exact LinearMap.id, fun i i₁ j j₁ hij h₁ h₂ hj x => by
    subst hij hj; rfl⟩
  φU := ZInQ.Contrib.CloudB3RC53.SelmerDuality.ghomComp (piMap ψ) (piReindex σ Δ₂.U)
  φL := piReindex σ (localCx k GS Gv loc M)
  hres i j h a := by
    subst h
    funext v
    obtain ⟨b, rfl⟩ := σ.surjective v
    exact piReindex_apply σ _ i _ b
  hι i j h u := by
    subst h
    funext v
    obtain ⟨b, rfl⟩ := σ.surjective v
    change (piReindex σ (localCx k GS Gv loc M)).f i i rfl (fun c => (Δ₁.i c).f i i rfl (u c))
        (σ b) = (Δ₂.i (σ b)).f i i rfl
          ((piReindex σ Δ₂.U).f i i rfl (fun c => (ψ c).f i i rfl (u c)) (σ b))
    rw [piReindex_apply, piReindex_apply]
    exact (hψι b i (u b)).symm
  hG n := Function.bijective_id
  hU n := ZInQ.Contrib.RC53Assist.ResidualFiniteness.ghomComp_bijective _ _
    (ZInQ.Contrib.RC53Assist.ResidualFiniteness.piMap_bijective ψ hψ) (piReindex_bijective σ _) n
  hL n := piReindex_bijective σ _ n

end Reindex

/-! ### The genuine `C_∅` -/

section Genuine

open NumberField IsDedekindDomain
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

/-- **`GenCxResidualIso` from isomorphisms of Selmer data** (PROVED): if at every stage `s ≠ 0`
the Selmer data of the genuine `C_∅` are componentwise isomorphic to Selmer data `D s` with
finite residual cohomology and residual ranks `Rk s`, the named input holds. -/
theorem genCxResidualIso_of_selIso {Rk : ℕ → ℤ → ℕ}
    (D : ∀ s, SelData (StageRing s))
    (e : ∀ s [NeZero s], SelIso (suppDataS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) ∅)
      (D s))
    (hfin : ∀ s [NeZero s] n, Module.Finite (ResidueField (StageRing s))
      (residualCohomologyAt (selCx (D s)) n))
    (hrank : ∀ s [NeZero s] n, Module.finrank (ResidueField (StageRing s))
      (residualCohomologyAt (selCx (D s)) n) = Rk s n) :
    GenCxResidualIso K S₀ S M Δ place X EU Rk where
  finite s _ n := (Module.Finite.equiv_iff ((e s).residualEquiv n)).2 (hfin s n)
  rank_eq s _ n := ((e s).residualEquiv n).finrank_eq.trans (hrank s n)

/-- **The places of the presentation as places of `S`** (tex 3455–3463): `v ∈ S₀` and the places
of the chain, the identity on the underlying primes. Kind: definition. -/
def presPlace (hS : S₀ ⊆ S) (i : Places K S₀ ⊕ (ι × Bool)) : Places K S :=
  ⟨presPrime K S₀ S place i, by
    rcases i with v | j
    · exact hS v.2
    · exact (place j).2⟩

/-- **The places of the presentation are the places of `S`** (PROVED): bijective when `place`
is injective, its places lie outside `S₀`, and `S = S₀ ∪ range place`. Kind: definition. -/
def presPlaceEquiv (hS : S₀ ⊆ S) (hinj : Function.Injective place)
    (hw : ∀ j, (place j).1 ∉ S₀) (hcov : ∀ v ∈ S, v ∈ S₀ ∨ ∃ j, (place j).1 = v) :
    Places K S₀ ⊕ (ι × Bool) ≃ Places K S :=
  Equiv.ofBijective (presPlace (place := place) hS) (by
    constructor
    · rintro (v | j) (v' | j') h
      · have h' : v.1 = v'.1 := congrArg (fun x : Places K S => x.1) h
        exact congrArg Sum.inl (Subtype.ext h')
      · exact absurd (congrArg Subtype.val h ▸ v.2) (hw j')
      · exact absurd ((congrArg Subtype.val h).symm ▸ v'.2) (hw j)
      · have h' : (place j).1 = (place j').1 := congrArg (fun x : Places K S => x.1) h
        exact congrArg Sum.inr (hinj (Subtype.ext h'))
    · rintro ⟨v, hv⟩
      rcases hcov v hv with h0 | ⟨j, hj⟩
      · exact ⟨Sum.inl ⟨v, h0⟩, rfl⟩
      · exact ⟨Sum.inr j, Subtype.ext hj⟩)

/-- **`GenCxResidualIso` from reference conditions at the places of `S`** (PROVED): if at every
stage `s ≠ 0` the conditions of the genuine `C_∅` are, place by place, isomorphic to Galois local
conditions `Δref s` at the places of `S` (compatibly with the condition maps), and the Selmer
complexes `selCx (galoisSelData K S (StageRing s) (M s) (Δref s))` have finite residual
cohomology with ranks `Rk s`, the named input `GenCxResidualIso Rk` holds. -/
theorem genCxResidualIso_of_conditions {Rk : ℕ → ℤ → ℕ} (hS : S₀ ⊆ S)
    (hinj : Function.Injective place) (hw : ∀ j, (place j).1 ∉ S₀)
    (hcov : ∀ v ∈ S, v ∈ S₀ ∨ ∃ j, (place j).1 = v)
    (Δref : ∀ s, GaloisLocalConditions K S (StageRing s) (M s))
    (ψ : ∀ s i, GHom ((presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) ∅).U i)
      ((Δref s).U (presPlaceEquiv hS hinj hw hcov i)))
    (hψ : ∀ s i n, Function.Bijective ((ψ s i).f n n rfl))
    (hψι : ∀ s i n x, ((Δref s).i (presPlaceEquiv hS hinj hw hcov i)).f n n rfl
        ((ψ s i).f n n rfl x) =
      ((presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) ∅).i i).f n n rfl x)
    (hfin : ∀ s [NeZero s] n, Module.Finite (ResidueField (StageRing s))
      (residualCohomologyAt (selCx (galoisSelData K S (StageRing s) (M s) (Δref s))) n))
    (hrank : ∀ s [NeZero s] n, Module.finrank (ResidueField (StageRing s))
      (residualCohomologyAt (selCx (galoisSelData K S (StageRing s) (M s) (Δref s))) n) =
        Rk s n) :
    GenCxResidualIso K S₀ S M Δ place X EU Rk :=
  genCxResidualIso_of_selIso (fun s => galoisSelData K S (StageRing s) (M s) (Δref s))
    (fun s _ => by
      change SelIso (selData (StageRing s) (GKS K S)
        (fun i => Gloc K ((presPlaceEquiv hS hinj hw hcov) i).1)
        (fun i => locMap K S ((presPlaceEquiv hS hinj hw hcov) i).1) (M s)
        (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) ∅))
        (selData (StageRing s) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (M s) (Δref s))
      exact selIsoReindex (Gv := fun v : Places K S => Gloc K v.1) (loc := fun v => locMap K S v.1)
        (presPlaceEquiv hS hinj hw hcov)
        (presCondS K S₀ S (StageRing s) (M s) (Δ s) place (X s) (EU s) ∅) (Δref s) (ψ s)
        (hψ s) (hψι s)) hfin hrank

end Genuine

end ZInQ.Contrib.CloudB3E2.St0Shape
