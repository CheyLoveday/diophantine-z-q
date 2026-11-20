import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalPlace

/-!
# Lane RC31, round 6: the tame local model at a stage ring

Manuscript `diophantine_zq.tex`, tex 3470–3481 ((4.4) at augmentation, the unramified
condition), at the finite stages of the inner limit (a Noetherian self-injective coefficient
ring, free coefficient modules).

`TameLocalModelPrint` (stated in `TameLocalPrint.lean` for Noetherian self-injective coefficient
rings and free coefficient modules) is PROVED here (`tameLocalModelPrint_of_prints`) from:

* `TameCochainQuasiIso` (PRINT): the comparison of the cochains with the tame free model is a
  quasi-isomorphism (for coefficient fields, its `g = 1` part rests on the tree PRINT
  `MilneADT_I_2_8` and the GLUE statement `TameH2Surjective`, `TameEulerField.lean`);
* `IwasawaGenerators` (PRINT): Iwasawa generators at the finite places not above `2`;
* `GenuineCochainsKInjective` (PRINT): the genuine local cochain complex is K-injective.

The model side is PROVED: a finite free module over a self-injective ring is an injective object
(`injective_of_free`), so the three-term complexes, the tame model and the unramified complex
are K-injective (`cx3_isKInjective`, `ofCC_frobCx_isKInjective`).

Kinds: PRINT (one statement), PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (urCx eUr resUr frob frobCx frobElt rel01)
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)

attribute [local instance] TopRep.distribMulAction

/-! ### Injective objects over a self-injective ring -/

section Injective

variable {k : Type} [CommRing k]

/-- **A finite free module over a self-injective ring is an injective object** (tex 3470–3480):
`V ≅ k^n` and `k^n` is injective (`Module.Injective.pi`). Kind: PROVED. -/
theorem injective_of_free [Module.Injective k k] (V : Type) [AddCommGroup V] [Module k V]
    [Module.Free k V] [Module.Finite k V] : Injective (ModuleCat.of k V) := by
  have : Module.Injective k (Module.Free.ChooseBasisIndex k V → k) := Module.Injective.pi k _
  exact Injective.of_iso (Module.Free.chooseBasis k V).equivFun.toModuleIso.symm
    (Module.injective_object_of_injective_module k (Module.Free.ChooseBasisIndex k V → k))

/-- The zero module is an injective object. Kind: PROVED. -/
theorem injective_punit : Injective (ModuleCat.of k PUnit) :=
  Injective.of_iso (ModuleCat.isZero_of_subsingleton _).isoZero.symm inferInstance

/-- **A three-term complex of injective objects is K-injective** (tex 3470–3480; bounded below
with injective terms, Mathlib's `isKInjective_of_injective`). Kind: PROVED. -/
theorem cx3_isKInjective {X0 X1 X2 : Type} [AddCommGroup X0] [Module k X0] [AddCommGroup X1]
    [Module k X1] [AddCommGroup X2] [Module k X2] (d0 : X0 →ₗ[k] X1) (d1 : X1 →ₗ[k] X2)
    (h : ∀ x, d1 (d0 x) = 0) (h0 : Injective (ModuleCat.of k X0))
    (h1 : Injective (ModuleCat.of k X1)) (h2 : Injective (ModuleCat.of k X2)) :
    (cx3 d0 d1 h).toCC.IsKInjective := by
  have : (cx3 d0 d1 h).toCC.IsStrictlyGE 0 := cx3_toCC_isStrictlyGE d0 d1 h
  have : ∀ n, Injective ((cx3 d0 d1 h).toCC.X n) := by
    intro n
    rcases n with (_ | _ | _ | n) | n
    · exact h0
    · exact h1
    · exact h2
    · exact injective_punit
    · exact injective_punit
  exact CochainComplex.isKInjective_of_injective _ 0

/-- **The unramified complex of an injective module is K-injective** (tex 3478–3481). Kind:
PROVED. -/
theorem ofCC_frobCx_isKInjective {W : Type} [AddCommGroup W] [Module k W] (Ψ : W →ₗ[k] W)
    (hW : Injective (ModuleCat.of k W)) : (ofCC (frobCx Ψ)).toCC.IsKInjective := by
  have : (ofCC (frobCx Ψ)).toCC.IsStrictlyGE 0 := ofCC_frobCx_isStrictlyGE Ψ
  have : ∀ n, Injective ((ofCC (frobCx Ψ)).toCC.X n) := by
    intro n
    by_cases h0 : n = 0
    · subst h0
      exact Injective.of_iso
        (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (Ψ - 1)) rel01).symm hW
    · by_cases h1 : n = 1
      · subst h1
        exact Injective.of_iso
          (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Ψ - 1)) rel01 (by decide)).symm hW
      · exact Injective.of_iso
          (HomologicalComplex.isZero_double_X (ModuleCat.ofHom (Ψ - 1)) rel01 n h0 h1).isoZero.symm
          inferInstance
  exact CochainComplex.isKInjective_of_injective _ 0

end Injective

/-! ### The stage statement -/

/-- **PRINT: the genuine local cochains are K-injective at a stage ring** (tex 3470–3480): for a
Noetherian self-injective coefficient ring `k` and a finite discrete coefficient module `M`, free
over `k`, the genuine local complex `C^•_cont(G_{K_w}, M)` is K-injective. Literature: the
cochains are locally constant maps `G^n → M`, a free `k`-module since the locally constant
functions on a profinite set form a free abelian group (Nöbeling, Invent. Math. 6 (1968), in
Mathlib as `LocallyConstant.freeOfProfinite`); free modules over a Noetherian self-injective
ring are injective (Bass–Papp: direct sums of injectives over a Noetherian ring are injective);
a bounded-below complex of injectives is K-injective (Mathlib, `isKInjective_of_injective`).
Kind: PRINT. -/
def GenuineCochainsKInjective : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type)
    [CommRing k] [TopologicalSpace k] [IsNoetherianRing k] [Module.Injective k k] (M : Type)
    [AddCommGroup M] [Module k M] [Module.Free k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M] (w : Places K S),
    (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
      M w).toCC.IsKInjective

/-- **The tame local model at a stage ring, from the literature inputs** (tex 3470–3481):
`TameCochainQuasiIso`, `IwasawaGenerators` and `GenuineCochainsKInjective` imply
`TameLocalModelPrint`. Kind: PROVED. -/
theorem tameLocalModelPrint_of_prints (hT : TameCochainQuasiIso) (hI : IwasawaGenerators)
    (hK : GenuineCochainsKInjective) : TameLocalModelPrint := by
  intro K _ _ S k _ _ _ _ M _ _ _ _ _ _ _ _ _ w X _ _ _ f hf hbij hexp q hq hqcard
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
  -- injectivity of the coefficient module `X ≅ M` and of `X × X`
  have : Module.Finite k M := Module.Finite.of_finite
  have : Module.Free k X.V := Module.Free.of_equiv (LinearEquiv.ofBijective f hbij).symm
  have : Module.Finite k X.V := Module.Finite.equiv (LinearEquiv.ofBijective f hbij).symm
  have hX : Injective (ModuleCat.of k X.V) := injective_of_free X.V
  have hXX : Injective (ModuleCat.of k (X.V × X.V)) := injective_of_free (X.V × X.V)
  have := hK K S k M w
  have : (ofCC (frobCx (frob (eUr K w.1) X))).toCC.IsKInjective := ofCC_frobCx_isKInjective _ hX
  have : (tameNewPlace (ModuleCat.of k X.V) (frob (eUr K w.1) X) _ hq).Lq.toCC.IsKInjective :=
    cx3_isKInjective _ _ (freeD1_freeD0 _ _ _ (tame_DC_CA_one (frob (eUr K w.1) X) _ hq))
      hX hXX hX
  have : (tameNewPlace (ModuleCat.of k X.V) (frob (eUr K w.1) X) _ hq).Uq.toCC.IsKInjective :=
    cx3_isKInjective (frobOne (frob (eUr K w.1) X)) (0 : X.V →ₗ[k] PUnit) (fun _ => rfl)
      hX hX injective_punit
  obtain ⟨m, -, -⟩ := tameLocalModelAt_of_cochainQuasiIso_kInj (eUr K w.1) (resUr K w.1) X
    (G := Gloc K w.1) (M := ResMod (locMap K S w.1) M) f' hbij' hf' _ φ σ _ hq _
    (resUr_of_isArithFrobeniusLift hIw.frob) (resUr_of_mem_inertia hIw.mem_inertia) hIw.rel hQ
  exact ⟨m⟩

end ZInQ.Manuscript.RC.Local
