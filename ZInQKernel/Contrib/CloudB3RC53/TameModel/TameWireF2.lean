import ZInQKernel.Contrib.CloudB3RC53.TameModel.TrivialF2QIso

/-!
# Wiring: the `tame` field of `Identification2G` for trivial `𝔽₂` coefficients

`Identification2G` (`ClearingComplex/GenuineIdentification.lean`) carries, at every new place
`q ∈ S' − S`, the named input `tame q : TameModelQIso M₀ (Φ_q) (q_q) L_q U_q ι_q` with `L_q` the
genuine continuous cochains of `G_{K_q}` on `M₀`, `U_q` those of `Gal(K_q^{ur}/K_q)` and `ι_q`
inflation (`urCond`). For the trivial coefficients `R₀ = M₀ = 𝔽₂`, `Φ_q = 1` and odd `q_q`,
`tame_trivialF2` discharges it from `tameModelQIsoF2` (`TrivialF2QIso.lean`) at `K = K_q`,
`π = urRes`, modulo the print `LocalCohomologyF2 K_q` and the odd residue characteristic of `K_q`.

The coefficient modules of `L_q`, `U_q` are type synonyms of `𝔽₂` with actions restricted along
the localization and unramified-factorization maps (`ResMod`); every action on `𝔽₂` is trivial.
The comparison is made by **explicit identity isomorphisms of complexes** (componentwise the
identity on cochains, `isoTrivL`, `isoTrivU`, commuting with inflation), along
which `TameModelQIso` is transported (`TameModelQIso.transport`). All PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.TameModel

open CategoryTheory NumberField IsDedekindDomain TauCeti ValuativeRel
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.ClearingComplex (TameModelQIso tL tU tιH)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom)
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)

/-! ### Transport of `TameModelQIso` along isomorphisms -/

/-- `TameModelQIso` is transported along isomorphisms of the full local complexes and of the
unramified conditions that commute with the inclusions. -/
def TameModelQIso.transport {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    {Φ : M →ₗ[R] M} {q : ℕ} {L U L' U' : GCx R} {ι : GHom U L} {ι' : GHom U' L'}
    (T : TameModelQIso M Φ q L U ι) (eL : L.toCC ≅ L'.toCC) (eU : U.toCC ≅ U'.toCC)
    (hcomm : eU.hom ≫ SelmerDuality.GHom.toCC ι' = SelmerDuality.GHom.toCC ι ≫ eL.hom) :
    TameModelQIso M Φ q L' U' ι' where
  fL := T.fL ≫ eL.hom
  fU := T.fU ≫ eU.hom
  qisL := by
    have := T.qisL
    infer_instance
  qisU := by
    have := T.qisU
    infer_instance
  comm := by
    rw [← Category.assoc, T.comm, Category.assoc, ← hcomm, ← Category.assoc]

/-! ### The trivial action -/

/-- The trivial action of a group on `𝔽₂`. -/
abbrev trivActF2 (G : Type) [Group G] : DistribMulAction G (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

theorem trivActF2_comm (G : Type) [Group G] :
    @SMulCommClass G (ZMod 2) (ZMod 2) (trivActF2 G).toSMul _ :=
  @SMulCommClass.mk G (ZMod 2) (ZMod 2) (trivActF2 G).toSMul _ fun _ _ _ => rfl

theorem trivActF2_cont (G : Type) [Group G] [TopologicalSpace G] :
    @ContinuousSMul G (ZMod 2) (trivActF2 G).toSMul _ _ :=
  @ContinuousSMul.mk G (ZMod 2) (trivActF2 G).toSMul _ _ continuous_snd

/-- The differential of `natCx` out of a negative degree vanishes. -/
theorem natCx_toCC_d_negSucc {k : Type} [CommRing k] (C : CochainComplex (ModuleCat.{0} k) ℕ)
    (m : ℕ) (j : ℤ) (y : ((natCx C).toCC).X (Int.negSucc m)) :
    (((natCx C).toCC).d (Int.negSucc m) j).hom y = 0 := by
  by_cases h : Int.negSucc m + 1 = j
  · refine (PairedFunctional.GCx.toCC_d_hom (natCx C) _ _ h y).trans ?_
    subst h
    rfl
  · rw [HomologicalComplex.shape _ _ _ h]
    rfl

/-! ### The identity isomorphisms -/

section Wire

variable (K : Type) [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S ⊆ S')
  [DistribMulAction (GKS K S) (ZMod 2)] [SMulCommClass (GKS K S) (ZMod 2) (ZMod 2)]
  [ContinuousSMul (GKS K S) (ZMod 2)]

/-- The trivial action of `Gal(F^{alg}/F)` on `𝔽₂`. -/
abbrev trivGal (F : Type) [Field F] : DistribMulAction (Gal(AlgebraicClosure F/F)) (ZMod 2) :=
  trivActF2 _

attribute [local instance] trivGal

theorem trivGal_comm (F : Type) [Field F] :
    SMulCommClass (Gal(AlgebraicClosure F/F)) (ZMod 2) (ZMod 2) :=
  trivActF2_comm _

theorem trivGal_cont (F : Type) [Field F] :
    ContinuousSMul (Gal(AlgebraicClosure F/F)) (ZMod 2) :=
  trivActF2_cont _

attribute [local instance] trivGal_comm trivGal_cont

/-- The identity on cochains, `C^n(G_{K_q}, 𝔽₂) ≃ C^n(G_{K_q}, ResMod (locMap ∘ infl) 𝔽₂)`. -/
def linTrivL (q : NewPlaces K S S') (n : ℕ) :
    (contCochains (ZMod 2) (Gal(AlgebraicClosure (q.1.adicCompletion K)/q.1.adicCompletion K))
      (ZMod 2)).X n ≃ₗ[ZMod 2]
    (contCochains (ZMod 2) (Gloc K q.1)
      (ResMod (locMap K S' q.1) (ResMod (inflMap K hS) (ZMod 2)))).X n where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl


theorem linTrivL_d (q : NewPlaces K S S') (n : ℕ) (x : (contCochains (ZMod 2) (Gal(AlgebraicClosure (q.1.adicCompletion K)/q.1.adicCompletion K)) (ZMod 2)).X n) :
    linTrivL K hS q (n + 1) (((contCochains (ZMod 2) (Gal(AlgebraicClosure (q.1.adicCompletion K)/q.1.adicCompletion K)) (ZMod 2)).d n (n + 1)).hom x) = ((contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S' q.1) (ResMod (inflMap K hS) (ZMod 2)))).d n (n + 1)).hom (linTrivL K hS q n x) := by
  refine contCochains_ext fun v => ?_
  have h1 := contCochains_d_apply (k := ZMod 2) (G := (Gal(AlgebraicClosure (q.1.adicCompletion K)/q.1.adicCompletion K))) (M := ZMod 2) n x v
  have h2 := contCochains_d_apply (k := ZMod 2) (G := Gloc K q.1)
    (M := ResMod (locMap K S' q.1) (ResMod (inflMap K hS) (ZMod 2))) n (linTrivL K hS q n x) v
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1
  exact (smul_zmod_two (G := GKS K S) _ _).symm

/-- Components of the identity isomorphism of the full local complexes. -/
def compIsoL (q : NewPlaces K S S') : (i : ℤ) → (natCx (contCochains (ZMod 2) (Gal(AlgebraicClosure (q.1.adicCompletion K)/q.1.adicCompletion K)) (ZMod 2))).toCC.X i ≅ (natCx (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S' q.1) (ResMod (inflMap K hS) (ZMod 2))))).toCC.X i
  | Int.ofNat n => (linTrivL K hS q n).toModuleIso
  | Int.negSucc _ => Iso.refl (ModuleCat.of (ZMod 2) PUnit)

/-- **The identity isomorphism of the full local complexes.** -/
def isoTrivL (q : NewPlaces K S S') : (natCx (contCochains (ZMod 2) (Gal(AlgebraicClosure (q.1.adicCompletion K)/q.1.adicCompletion K)) (ZMod 2))).toCC ≅ (natCx (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S' q.1) (ResMod (inflMap K hS) (ZMod 2))))).toCC :=
  HomologicalComplex.Hom.isoOfComponents (compIsoL K hS q) (by
    rintro i j (rfl : i + 1 = j)
    ext x
    rcases i with n | m
    · have e1 := PairedFunctional.GCx.toCC_d_hom (natCx (contCochains (ZMod 2) (Gal(AlgebraicClosure (q.1.adicCompletion K)/q.1.adicCompletion K)) (ZMod 2))) (Int.ofNat n) (Int.ofNat n + 1) rfl x
      have e2 := PairedFunctional.GCx.toCC_d_hom (natCx (contCochains (ZMod 2) (Gloc K q.1) (ResMod (locMap K S' q.1) (ResMod (inflMap K hS) (ZMod 2))))) (Int.ofNat n) (Int.ofNat n + 1) rfl
        (linTrivL K hS q n x)
      exact e2.trans ((linTrivL_d K hS q n x).symm.trans (congrArg (linTrivL K hS q (n + 1)) e1.symm))
    · rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        natCx_toCC_d_negSucc, natCx_toCC_d_negSucc, map_zero])

end Wire

section WireU

variable (K : Type) [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))}
  [DistribMulAction (GKS K S) (ZMod 2)] [SMulCommClass (GKS K S) (ZMod 2) (ZMod 2)]
  [ContinuousSMul (GKS K S) (ZMod 2)]
  (ψur : ∀ q : NewPlaces K S S', GUr K q.1 →ₜ* GKS K S)

/-- The action of `Gal(K_q^{ur}/K_q)` on `𝔽₂` through `ψ_q` (it is trivial), on the bare `𝔽₂`. -/
abbrev actU (q : NewPlaces K S S') : DistribMulAction (GUr K q.1) (ZMod 2) :=
  inferInstanceAs (DistribMulAction (GUr K q.1) (ResMod (ψur q) (ZMod 2)))

omit [ContinuousSMul (GKS K S) (ZMod 2)] in
theorem actU_comm (q : NewPlaces K S S') :
    @SMulCommClass (GUr K q.1) (ZMod 2) (ZMod 2) (actU K ψur q).toSMul _ :=
  inferInstanceAs (SMulCommClass (GUr K q.1) (ZMod 2) (ResMod (ψur q) (ZMod 2)))

omit [SMulCommClass (GKS K S) (ZMod 2) (ZMod 2)] in
theorem actU_cont (q : NewPlaces K S S') :
    @ContinuousSMul (GUr K q.1) (ZMod 2) (actU K ψur q).toSMul _ _ :=
  inferInstanceAs (ContinuousSMul (GUr K q.1) (ResMod (ψur q) (ZMod 2)))

/-- **The unramified conditions agree** (definitionally; the coefficient module of `U_q` is a type
synonym of `𝔽₂`). -/
def isoTrivU (q : NewPlaces K S S') :
    (letI := actU K ψur q; letI := actU_comm K ψur q; letI := actU_cont K ψur q
      (natCx (contCochains (ZMod 2) (GUr K q.1) (ZMod 2))).toCC) ≅
      (natCx (contCochains (ZMod 2) (GUr K q.1) (ResMod (ψur q) (ZMod 2)))).toCC :=
  Iso.refl _

end WireU

/-! ### The wiring -/

section Final

variable (K : Type) [Field K] [NumberField K] {S S' : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S ⊆ S')
  [DistribMulAction (GKS K S) (ZMod 2)] [SMulCommClass (GKS K S) (ZMod 2) (ZMod 2)]
  [ContinuousSMul (GKS K S) (ZMod 2)]

/-- **The `tame` field of `Identification2G` for trivial `𝔽₂` coefficients** (`R₀ = M₀ = 𝔽₂`,
`Φ_q = 1`, `q_q` odd), from the print `LocalCohomologyF2 K_q` (for every, necessarily trivial,
action of `G_{K_q}` on `𝔽₂`) and odd residue characteristic. PROVED. -/
def tame_trivialF2 (ψur : ∀ q : NewPlaces K S S', GUr K q.1 →ₜ* GKS K S)
    (hψur : ∀ (q : NewPlaces K S S') g, locMap K S q.1 g = ψur q (urRes K q.1 g))
    (q : NewPlaces K S S') {qq : ℕ} (hq : Odd qq)
    (hp : ringChar 𝓀[q.1.adicCompletion K] ≠ 2)
    (hL : ∀ [DistribMulAction (Gal(AlgebraicClosure (q.1.adicCompletion K)/q.1.adicCompletion K))
        (ZMod 2)]
      [SMulCommClass (Gal(AlgebraicClosure (q.1.adicCompletion K)/q.1.adicCompletion K)) (ZMod 2)
        (ZMod 2)]
      [ContinuousSMul (Gal(AlgebraicClosure (q.1.adicCompletion K)/q.1.adicCompletion K)) (ZMod 2)],
      LocalCohomologyF2 (q.1.adicCompletion K)) :
    TameModelQIso (ZMod 2) (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) qq
      (natCx (contCochains (ZMod 2) (Gloc K q.1)
        (ResMod (locMap K S' q.1) (ResMod (inflMap K hS) (ZMod 2)))))
      (natCx (contCochains (ZMod 2) (GUr K q.1) (ResMod (ψur q) (ZMod 2))))
      (natHom (urCond (k := ZMod 2) (GS := GKS K S) (GS' := GKS K S') (M := ZMod 2)
        (infl := inflMap K hS)
        (Gq := fun q : NewPlaces K S S' => Gloc K q.1) (locq := fun q => locMap K S' q.1)
        (Gur := fun q : NewPlaces K S S' => GUr K q.1)
        (π := fun q => urRes K q.1) (ψ := ψur)
        (fun q g => (locMap_compat K hS q.1 g).trans (hψur q g)) q)) :=
  TameModelQIso.transport
    (@tameModelQIsoF2 (q.1.adicCompletion K) _ _ _ _ (trivGal _) (trivGal_comm _)
      (trivGal_cont _) (actU K ψur q) (actU_comm K ψur q) (actU_cont K ψur q) hp qq hq
      (urRes K q.1) (fun _ => rfl) (@hL (trivGal _) (trivGal_comm _) (trivGal_cont _)))
    (isoTrivL K hS q) (isoTrivU K ψur q) (by
      ext n x
      rcases n with n | m
      · exact contCochains_ext fun v => rfl
      · rfl)

end Final

end ZInQ.Contrib.CloudB3RC53.TameModel
