import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalQuotient
import ZInQKernel.Contrib.OneProof.RC.Local.TameSurjective
import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalPlace

/-!
# Lane RC31, round 7: the local quotients at the two conjugate places, from the literature

Manuscript `diophantine_zq.tex`, tex 3470–3480 ((4.4) at augmentation), tex 4176–4184 (the two
quotient blocks at the conjugate places of an unused split prime, `δ_q = det(zFr_q − q) ·
det(z⁻¹Fr_q − q)`).

* `frobElt_ne_one` (PROVED): the Frobenius of `ℤ̂` is not the identity; hence, for
  `π φ = Frob` and `π σ = 1`: `φ ≠ σ`, `φ ≠ 1`, `σ ≠ φ⁻¹` (`tame_distinct`).
* **`exists_retract_localQuotient_sep`** (PROVED): in a profinite (totally separated) group, the
  surjectivity hypothesis of `exists_retract_localQuotient` holds (`tameCochainMap_surjective`),
  so the local quotient retracts onto the singular block as soon as `tameCochainMap` is a
  quasi-isomorphism.
* **`exists_retract_localQuotient_place`** (PROVED): at a finite place `w ∤ 2` of a number field,
  for field coefficients, from the literature statements `TameCochainQuasiIso` and
  `IwasawaGenerators`: for every split inclusion `E` of the genuine unramified condition into the
  genuine local complex, `E.quotientCx` retracts onto `singCx Φ_w q`.
* **`exists_retract_twoPlaces_place`** (PROVED): at the two conjugate places `w`, `w̄`, with
  bases of the coefficients in which Frobenius is `z F` and `z⁻¹ F`, the sum of the two local
  quotients retracts onto `twoSingCx F q z z⁻¹`.

Kinds: PROVED.
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

/-! ### Distinctness of the tame generators -/

section Distinct

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Type} [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H] (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H)

/-- **The Frobenius of `ℤ̂` is not the identity** (tex 3478–3481): its image in `ℤ/2` is `1`.
Kind: PROVED. -/
theorem frobElt_ne_one : frobElt e ≠ 1 := by
  intro h
  have h1 := chi_frob e 2
  rw [h, map_one] at h1
  have h2 := congrArg Multiplicative.toAdd h1
  rw [toAdd_one, toAdd_ofAdd] at h2
  exact absurd h2 (by decide)

omit [IsTopologicalGroup G] in
/-- **The tame generators are distinct** (tex 3470–3480): for `π φ = Frob` and `π σ = 1`,
`φ ≠ σ`, `φ ≠ 1` and `σ ≠ φ⁻¹`. Kind: PROVED. -/
theorem tame_distinct {φ σ : G} (hφ : π φ = frobElt e) (hσ : π σ = 1) :
    φ ≠ σ ∧ φ ≠ 1 ∧ σ ≠ φ⁻¹ := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h, hσ] at hφ
    exact frobElt_ne_one e hφ.symm
  · rw [h, map_one] at hφ
    exact frobElt_ne_one e hφ.symm
  · rw [h, map_inv, hφ] at hσ
    exact frobElt_ne_one e (inv_eq_one.1 hσ)

end Distinct

/-! ### The local quotient in a profinite group -/

section Separated

variable {k : Type} [Field k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TotallySeparatedSpace G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hbij : Function.Bijective f)
  (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)
  (Φ : M →ₗ[k] M) (φ σ : G) (q : ℕ) (hq : Odd q) (hΦ : ∀ m, Φ m = φ • m)

/-- **The local quotient retracts onto the singular block, in a profinite group**
(tex 3470–3480, 4423–4437): `exists_retract_localQuotient` without the surjectivity hypothesis
(`tameCochainMap_surjective`, `tame_distinct`). Kind: PROVED. -/
theorem exists_retract_localQuotient_sep (hφ : π φ = frobElt e) (hσ : π σ = 1)
    (hrel : φ * σ * φ⁻¹ = σ ^ q)
    (E : SplitInclusion (ofCC (frobCx (frob e X))) (natCx (contCochains k G M)))
    (hE : E.i = ofCCHom (urToLocal e π X f hf))
    (hQ : QuasiIso (GHom.toCC (tameCochainMap Φ LinearMap.id φ σ q hq hΦ
      (smul_eq_of_res_one π X f hbij hf σ hσ) id_invol (comm_id Φ) hrel))) :
    ∃ R : GRetract E.quotientCx (singCx (frob e X) q), ∀ n x,
      R.p.f n n rfl x =
        (localQuotMap e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel E hE).f n n rfl x := by
  obtain ⟨h1, h2, h3⟩ := tame_distinct e π hφ hσ
  exact exists_retract_localQuotient e π X f hbij hf Φ φ σ q hq hΦ hφ hσ hrel E hE hQ
    (tameCochainMap_surjective Φ LinearMap.id φ σ q hq hΦ _ id_invol (comm_id Φ) hrel h1 h2 h3)

end Separated

/-! ### At a place of a number field -/

section Place

/-- **The local quotient at a finite place retracts onto the singular block, from the
literature** (tex 3470–3480, 4176–4184): at a finite place `w` of odd residue cardinality `q`,
for field coefficients and a finite discrete coefficient module of `2`-power exponent that is
the inflation of an unramified representation `X` (`f : X ≃ M`), given the literature statements
`TameCochainQuasiIso` and `IwasawaGenerators`, every split inclusion `E` of the genuine
unramified condition into the genuine local complex has a retract of its quotient complex onto
the singular block `singCx Φ_w q = [X --Φ_w−q--> X]`. Kind: PROVED. -/
theorem exists_retract_localQuotient_place (hT : TameCochainQuasiIso) (hI : IwasawaGenerators)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type} [Field k]
    [TopologicalSpace k] {M : Type} [AddCommGroup M] [Module k M]
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
  obtain ⟨R, -⟩ := exists_retract_localQuotient_sep (eUr K w.1) (resUr K w.1) X
    (G := Gloc K w.1) (M := ResMod (locMap K S w.1) M) f' hbij' hf' _ φ σ _ hq _
    (resUr_of_isArithFrobeniusLift hIw.frob) (resUr_of_mem_inertia hIw.mem_inertia) hIw.rel
    E hE hQ
  exact ⟨R⟩

/-- **The two local quotients at the conjugate places retract onto the two singular blocks, from
the literature** (tex 4176–4184): at two finite places `w₁`, `w₂` (the conjugate places of an
unused split prime, residue cardinality `q`), with bases of the coefficients in which the
Frobenius is `z F` at `w₁` and `z⁻¹ F` at `w₂`, the sum of the two local quotient complexes
retracts onto `twoSingCx F q z z⁻¹` (differential `twoPlaceBlock F q z z⁻¹` in the coordinates of
the two places), given `TameCochainQuasiIso` and `IwasawaGenerators`. Kind: PROVED. -/
theorem exists_retract_twoPlaces_place (hT : TameCochainQuasiIso) (hI : IwasawaGenerators)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type} [Field k]
    [TopologicalSpace k] {M : Type} [AddCommGroup M] [Module k M]
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
  obtain ⟨R₁⟩ := exists_retract_localQuotient_place hT hI w₁ X₁ f₁ hf₁ hbij₁ hexp q hq hq₁ E₁ hE₁
  obtain ⟨R₂⟩ := exists_retract_localQuotient_place hT hI w₂ X₂ f₂ hf₂ hbij₂ hexp q hq hq₂ E₂ hE₂
  exact ⟨GRetract.twoPlaces _ _ F q z zi b₁ hb₁ b₂ hb₂ R₁ R₂⟩

end Place

end ZInQ.Manuscript.RC.Local
