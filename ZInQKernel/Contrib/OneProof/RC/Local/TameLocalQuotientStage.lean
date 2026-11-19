import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalQuotientPlace
import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalStage
import ZInQKernel.Contrib.OneProof.RC.Limits.SDRRetractRing

/-!
# Lane RC31, round 7: the local quotient retracts integrally, at the stage rings

Manuscript `diophantine_zq.tex`, tex 3470–3480 ((4.4) at augmentation), tex 4176–4184 (the two
quotient blocks, read on the integral model), at the finite stages of the inner limit:
coefficients in a Noetherian self-injective ring `k` (the stage rings) and free coefficient
modules.

* `exists_retract_localQuotient_kInj` (PROVED): for a coefficient ring `k` with `k` injective
  over itself, a free coefficient module and a genuine local complex with injective terms, every
  split inclusion `E` of the genuine unramified condition has a retract of its quotient onto the
  singular block `singCx Φ_X q`, with projection the comparison, given that `tameCochainMap` is
  a quasi-isomorphism (in a profinite group). The quotient complex is K-injective (complements of
  injective modules are injective), the singular block is K-injective and projective termwise
  (free terms), and a split quasi-isomorphism of K-injective complexes is the projection of a
  retract (`exists_retract_of_surjective_quasiIso_kInj`).
* `GenuineCochainsInjective` (a statement, PROVED downstream: `genuineCochainsInjective_proved`,
  by Nöbeling, Invent. Math. 6 (1968), Thm 2, with Bass–Papp): at a stage ring, the genuine local
  cochain modules are injective; it implies round 6's `GenuineCochainsKInjective`
  (`genuineCochainsKInjective_of`).
* **`exists_retract_localQuotient_place_stage`**, **`exists_retract_twoPlaces_place_stage`**
  (PROVED): at the stage rings, from `TameCochainQuasiIso`, `IwasawaGenerators` and
  `GenuineCochainsInjective`, the local quotients at the conjugate places retract onto
  `twoSingCx F q z z⁻¹` over the stage ring itself, so the block `twoPlaceBlock F q z z⁻¹` holds
  in integral (stage) bases.

Kinds: definitions (one statement, PROVED downstream), PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)

attribute [local instance] TopRep.distribMulAction

/-! ### The singular block over a self-injective ring -/

section Block

variable {k : Type} [CommRing k] {V : Type} [AddCommGroup V] [Module k V]

/-- The terms of a singular block over a free module are projective (tex 3478–3480). Kind:
PROVED. -/
theorem singCx_projective [Module.Free k V] (Ψ : V →ₗ[k] V) (q : ℕ) (n : ℤ) :
    Module.Projective k ((singCx Ψ q).X n) := by
  rcases n with (_ | _ | _ | n) | n
  · exact inferInstanceAs (Module.Projective k PUnit)
  · exact inferInstanceAs (Module.Projective k V)
  · exact inferInstanceAs (Module.Projective k V)
  · exact inferInstanceAs (Module.Projective k PUnit)
  · exact inferInstanceAs (Module.Projective k PUnit)

/-- The singular block over a finite free module is K-injective when `k` is injective over
itself (tex 3478–3480). Kind: PROVED. -/
theorem singCx_isKInjective [Module.Injective k k] [Module.Free k V] [Module.Finite k V]
    (Ψ : V →ₗ[k] V) (q : ℕ) : (singCx Ψ q).toCC.IsKInjective :=
  cx3_isKInjective (0 : PUnit →ₗ[k] V) (frobQ Ψ q) (fun _ => by simp) injective_punit
    (injective_of_free V) (injective_of_free V)

end Block

/-! ### The local quotient over a ring -/

section Ring

variable {k : Type} [CommRing k] [TopologicalSpace k] [Module.Injective k k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TotallySeparatedSpace G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hbij : Function.Bijective f)
  (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)
  (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)

/-- **The local quotient retracts onto the singular block over a ring** (tex 3470–3480,
4423–4437): for `k` injective over itself, `X` finite free, the terms of the genuine local
complex injective `k`-modules and `tameCochainMap` a quasi-isomorphism, every split inclusion
`E` of the genuine unramified condition has a retract of its quotient onto `singCx Φ_X q` with
projection the induced comparison. Kind: PROVED. -/
theorem exists_retract_localQuotient_kInj [Module.Free k X.V] [Module.Finite k X.V]
    (hφ : π φ = frobElt e) (hσ : π σ = 1) (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (E : SplitInclusion (ofCC (frobCx (frob e X))) (natCx (contCochains k G M)))
    (hE : E.i = ofCCHom (urToLocal e π X f hf))
    (hQ : QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ
      (smul_eq_of_res_one π X f hbij hf σ hσ) id_invol (comm_id Φ) hrel)))
    (hinj : ∀ n, Module.Injective k ((natCx (contCochains k G M)).X n)) :
    ∃ R : GRetract E.quotientCx (singCx (frob e X) q), ∀ n x,
      R.p.f n n rfl x =
        (localQuotMap e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel E hE).f n n rfl x := by
  obtain ⟨h1, h2, h3⟩ := tame_distinct e π hφ hσ
  have := hinj
  have : (natCx (contCochains k G M)).toCC.IsStrictlyGE 0 := natCx_toCC_isStrictlyGE _
  have : E.quotientCx.toCC.IsKInjective := quotientCx_isKInjective E 0
  have : (singCx (frob e X) q).toCC.IsKInjective := singCx_isKInjective _ q
  have : ∀ n, Module.Projective k ((singCx (frob e X) q).X n) := singCx_projective _ q
  have hqis := quasiIso_quotMap E (unrIncl (frob e X) q hq) (singProj (frob e X) q hq)
    (singProj_unrIncl (frob e X) q hq) (unrLG e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel)
    (ofCCHom (frobToUnr (frob e X))) (by
      intro n y
      rw [hE]
      exact congrArg (fun χ => ModuleCat.Hom.hom (χ.f n) y)
        (unr_square e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel))
    (unrIncl_injective _ q hq) (singProj_surjective _ q hq) (singProj_exact _ q hq)
    (quasiIso_toCC_frobToUnr e X) (quasiIso_unrLG e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel hQ)
  have : QuasiIso (GHom.toCC (localQuotMap e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel E hE)) :=
    hqis
  have hsurj := quotMap_surjective E (unrIncl (frob e X) q hq) (singProj (frob e X) q hq)
    (singProj_unrIncl (frob e X) q hq) (unrLG e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel)
    (ofCCHom (frobToUnr (frob e X))) (by
      intro n y
      rw [hE]
      exact congrArg (fun χ => ModuleCat.Hom.hom (χ.f n) y)
        (unr_square e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel))
    (fun n => (unrModelMap_surjective _ _ q hq _ _ n).comp
      (tameCochainMap_surjective Φ LinearMap.id φ σ q hq hΦ _ id_invol (comm_id Φ) hrel
        h1 h2 h3 n))
    (singProj_surjective _ q hq)
  exact exists_retract_of_surjective_quasiIso_kInj _
    (exists_rightInverse_of_projective _ hsurj)

end Ring

/-! ### At a place, at the stage rings -/

section PlaceStage

/-- **The genuine local cochain modules are injective at a stage ring**
(tex 3470–3480): for a Noetherian self-injective coefficient ring `k` and a finite discrete
coefficient module `M`, free over `k`, every term `C^n_cont(G_{K_w}, M)` of the genuine local
complex is an injective `k`-module. Literature: `C^n_cont(G^n, M)` is the module of locally
constant maps on the profinite set `G^n`, `LC(G^n, ℤ) ⊗ M`, free over `k` since `LC(G^n, ℤ)` is a
free abelian group (Nöbeling, Invent. Math. 6 (1968); Mathlib's `LocallyConstant.freeOfProfinite`);
a free module over a Noetherian self-injective ring is injective (Bass–Papp: direct sums of
injective modules over a Noetherian ring are injective).
Kind: definition (a statement, PROVED downstream: `genuineCochainsInjective_proved`). -/
def GenuineCochainsInjective : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type)
    [CommRing k] [TopologicalSpace k] [IsNoetherianRing k] [Module.Injective k k] (M : Type)
    [AddCommGroup M] [Module k M] [Module.Free k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M] (w : Places K S) (n : ℤ),
    Module.Injective k
      ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
        M w).X n)

/-- The degreewise statement implies round 6's K-injectivity statement (tex 3470–3480; a
bounded below complex of injective modules is K-injective). Kind: PROVED. -/
theorem genuineCochainsKInjective_of (h : GenuineCochainsInjective) :
    GenuineCochainsKInjective := by
  intro K _ _ S k _ _ _ _ M _ _ _ _ _ _ _ _ _ w
  have : ∀ n, Injective ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M w).toCC.X n) := fun n =>
    Module.injective_object_of_injective_module (R := k)
      (M := ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) M w).X n)) (inj := h K S k M w n)
  have : (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M w).toCC.IsStrictlyGE 0 := natCx_toCC_isStrictlyGE _
  exact CochainComplex.isKInjective_of_injective _ 0

/-- **The local quotient at a place retracts onto the singular block, at a stage ring**
(tex 3470–3480, 4176–4184): `exists_retract_localQuotient_place` for a Noetherian self-injective
coefficient ring and a free coefficient module, from `TameCochainQuasiIso`, `IwasawaGenerators`
and `GenuineCochainsInjective`. Kind: PROVED. -/
theorem exists_retract_localQuotient_place_stage (hT : TameCochainQuasiIso)
    (hI : IwasawaGenerators) (hInj : GenuineCochainsInjective)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type}
    [CommRing k] [TopologicalSpace k] [IsNoetherianRing k] [Module.Injective k k]
    {M : Type} [AddCommGroup M] [Module k M] [Module.Free k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
    (w : Places K S) (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V]
    [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    (hbij : Function.Bijective f) (hexp : ∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0)
    (q : ℕ) (hq : Odd q) (hqcard : q = Nat.card (𝓞 K ⧸ w.1.asIdeal))
    (E : SplitInclusion (ofCC (urCx K w.1 X))
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w))
    (hE : E.i = ofCCHom (urToLocal_galois K S w X f hf)) :
    Nonempty (GRetract E.quotientCx (singCx (frob (eUr K w.1) X) q)) := by
  have h2 : (2 : 𝓞 K) ∉ w.1.asIdeal := two_not_mem_of_odd_card (hqcard ▸ hq)
  obtain ⟨φ, σ, P, hIw⟩ := hI K w.1 h2
  have hq' := hqcard.trans (natCard_residueField_adicCompletion K w.1).symm
  subst hq'
  have : Finite (ResMod (locMap K S w.1) M) := inferInstanceAs (Finite M)
  have hexp' : ∃ e : ℕ, ∀ m : ResMod (locMap K S w.1) M, 2 ^ e • m = 0 := hexp
  have hQ := tameCochainQuasiIso_at_inflation hT h2 k (ResMod (locMap K S w.1) M)
    (X := X.V) f hf hbij.2 hIw hexp'
  let f' : X.V →ₗ[k] ResMod (locMap K S w.1) M := f
  have hbij' : Function.Bijective f' := hbij
  have hf' : ∀ (g : Gloc K w.1) (x : X.V), f' (resUr K w.1 g • x) = g • f' x := hf
  have : Module.Free k X.V := Module.Free.of_equiv (LinearEquiv.ofBijective f hbij).symm
  have : Module.Finite k X.V := Module.Finite.equiv (LinearEquiv.ofBijective f hbij).symm
  obtain ⟨R, -⟩ := exists_retract_localQuotient_kInj (eUr K w.1) (resUr K w.1) X
    (G := Gloc K w.1) (M := ResMod (locMap K S w.1) M) f' hbij' hf' _ φ σ _ hq _
    (resUr_of_isArithFrobeniusLift hIw.frob) (resUr_of_mem_inertia hIw.mem_inertia) hIw.rel
    E hE hQ (hInj K S k M w)
  exact ⟨R⟩

/-- **The two local quotients retract onto the two singular blocks over the stage ring**
(tex 4176–4184, read on the integral model): at the stage rings, from `TameCochainQuasiIso`,
`IwasawaGenerators` and `GenuineCochainsInjective`, with stage bases of the coefficients in which
the Frobenius is `z F` at `w₁` and `z⁻¹ F` at `w₂`, the sum of the two local quotients retracts
onto `twoSingCx F q z z⁻¹` over the stage ring, so `twoPlaceBlock F q z z⁻¹` is the block in
integral (stage) bases. Kind: PROVED. -/
theorem exists_retract_twoPlaces_place_stage (hT : TameCochainQuasiIso)
    (hI : IwasawaGenerators) (hInj : GenuineCochainsInjective)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type}
    [CommRing k] [TopologicalSpace k] [IsNoetherianRing k] [Module.Injective k k]
    {M : Type} [AddCommGroup M] [Module k M] [Module.Free k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
    (hexp : ∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0) (q : ℕ) (hq : Odd q)
    (F : Matrix (Fin 2) (Fin 2) k) (z zi : k)
    (w₁ : Places K S) (X₁ : TopRep.{0} k (GUr K w₁.1)) [ContinuousSMul (GUr K w₁.1) X₁.V]
    [DiscreteTopology X₁.V] [Finite X₁.V] (f₁ : X₁.V →ₗ[k] M)
    (hf₁ : ∀ (g : Gloc K w₁.1) (x : X₁.V), f₁ (resUr K w₁.1 g • x) = locMap K S w₁.1 g • f₁ x)
    (hbij₁ : Function.Bijective f₁) (hq₁ : q = Nat.card (𝓞 K ⧸ w₁.1.asIdeal))
    (E₁ : SplitInclusion (ofCC (urCx K w₁.1 X₁))
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w₁))
    (hE₁ : E₁.i = ofCCHom (urToLocal_galois K S w₁ X₁ f₁ hf₁))
    (b₁ : X₁.V ≃ₗ[k] (Fin 2 → k))
    (hb₁ : ∀ v, b₁ (frob (eUr K w₁.1) X₁ v) = Matrix.toLin' (z • F) (b₁ v))
    (w₂ : Places K S) (X₂ : TopRep.{0} k (GUr K w₂.1)) [ContinuousSMul (GUr K w₂.1) X₂.V]
    [DiscreteTopology X₂.V] [Finite X₂.V] (f₂ : X₂.V →ₗ[k] M)
    (hf₂ : ∀ (g : Gloc K w₂.1) (x : X₂.V), f₂ (resUr K w₂.1 g • x) = locMap K S w₂.1 g • f₂ x)
    (hbij₂ : Function.Bijective f₂) (hq₂ : q = Nat.card (𝓞 K ⧸ w₂.1.asIdeal))
    (E₂ : SplitInclusion (ofCC (urCx K w₂.1 X₂))
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w₂))
    (hE₂ : E₂.i = ofCCHom (urToLocal_galois K S w₂ X₂ f₂ hf₂))
    (b₂ : X₂.V ≃ₗ[k] (Fin 2 → k))
    (hb₂ : ∀ v, b₂ (frob (eUr K w₂.1) X₂ v) = Matrix.toLin' (zi • F) (b₂ v)) :
    Nonempty (GRetract (prodGCx E₁.quotientCx E₂.quotientCx) (twoSingCx F q z zi)) := by
  obtain ⟨R₁⟩ := exists_retract_localQuotient_place_stage hT hI hInj w₁ X₁ f₁ hf₁ hbij₁ hexp
    q hq hq₁ E₁ hE₁
  obtain ⟨R₂⟩ := exists_retract_localQuotient_place_stage hT hI hInj w₂ X₂ f₂ hf₂ hbij₂ hexp
    q hq hq₂ E₂ hE₂
  exact ⟨GRetract.twoPlaces _ _ F q z zi b₁ hb₁ b₂ hb₂ R₁ R₂⟩

end PlaceStage

end ZInQ.Manuscript.RC.Local
