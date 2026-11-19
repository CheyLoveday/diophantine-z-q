import ZInQKernel.Contrib.OneProof.RC.Local.TameFreeModel
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedCondition
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Instances

/-!
# Lane RC31, round 5: the comparison of the genuine local complexes with the tame model (4.4)

Manuscript `diophantine_zq.tex`, tex 3470–3480 ((4.4): the tame local free model and its splitting
at augmentation), consumed by (4.7) (tex 4176–4184, the two-place quotient block) and (5.9)
(tex 5317–5322, the singular quotient `[Φ − r_i]` in degrees one and two).

* `TameLocalModelAt Lq Uq ιq T`: homotopy equivalences of a local complex `L_q` and a local
  condition `U_q` with the full and unramified complexes of a tame model `T`
  (`UnramifiedNewPlace`), compatible with `ι_q` up to homotopy. With `T` as an extra field this is
  field for field the shape `TameLocalModel` of the support-change retention on genuine cochains.
* `TameLocalModelPrint` (PRINT): at a finite place `w ∈ S` with odd residue cardinality `q`, over
  a Noetherian self-injective coefficient ring (a field or a stage ring), for a finite discrete
  coefficient module, free and of `2`-power exponent, on which inertia at `w` acts
  trivially (it is the inflation of an unramified representation `X`), the genuine local complex
  `C^•_cont(G_{K_w}, M)`, the genuine unramified condition `[X --Φ_w − 1--> X]` and its inflation
  map form a `TameLocalModelAt` for the tame model `tameNewPlace X Φ_w q` of
  `TameFreeModel.lean`.
* At the two conjugate places `w`, `w̄` of an unused split prime, with Frobenius `z F` and
  `z⁻¹ F`, the quotients of the full by the unramified complexes of the two models are the two
  singular blocks, whose differential is `twoPlaceBlock F q z z⁻¹` (PROVED: `tame_split_exact_one`,
  `twoSing_matrix`; in the full-condition pre-cancellation complex: `twoPiece_hBe`).

What the PRINT contains, and what is PROVED around it:
* PROVED (`TameFreeModel.lean`): the model, `D C = C A`, its splitting at augmentation
  (`tame_split_directSum`, `tame_split_exact_one`), its cohomology (`tameH1Equiv`,
  `cohD0_eq_zero_iff`, `cohD1_range`), naturality, the two-place block, the stage transitions.
* PROVED (`TameFreeModelCochains.lean`, `TameQuasiIsoLow.lean`): the explicit comparison map
  `tameCochainMap : C^•_cont(G, M) → tameFreeModel` for Iwasawa generators `φ`, `σ` with the
  exact relation `φ σ φ⁻¹ = σ^q`, natural in `M`; it is a quasi-isomorphism in degrees `≤ 1` for
  the actual local Galois group at `g = 1` over a field (degree one through the tree's
  `coordQLocal_bijective`), so the comparison is a quasi-isomorphism as soon as it is one in
  degrees `≥ 2` (`quasiIso_tameCochainMap_of_two_le`).
* PROVED (`TameLocalReduction.lean`, `FieldQuasiIso.lean`): over a field, two quasi-isomorphisms
  from the genuine complexes to the model, strictly compatible with the inclusions, give a
  `TameLocalModelAt`, and the reverse (model to genuine) form.
* PRINT (literature), the remaining inputs: in degrees `≥ 2`, the comparison of `H²` with
  `coker(Φ − q)` and the vanishing above `2` — the structure of the tame Galois group and the
  splitting of wild inertia (Iwasawa; Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
  Thm 7.5.3), the vanishing of the cohomology of the pro-`q` wild inertia with `2`-primary
  coefficients (Serre, *Galois Cohomology*, I.3.3; NSW 1.6.2), Hochschild–Serre, and local
  duality for `H²`; the comparison of the genuine unramified condition with `[Φ − 1]` under the
  inflation; and, at a stage ring that is not a field, the passage from a quasi-isomorphism to
  homotopy equivalences (the genuine cochains form a bounded-below complex of injective modules
  over the self-injective stage ring).

Kinds: definitions, PRINT, PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (urCx eUr resUr)
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)

/-- **A tame local model of a local complex and a local condition** (tex 3470–3480): homotopy
equivalences of the local complex `L_q` with the full complex of the tame model `T` and of the
local condition `U_q` with its unramified complex, under which `ι_q` corresponds to the inclusion
of the unramified summand up to homotopy. Kind: definition (hypothesis structure). -/
structure TameLocalModelAt {S : Type} [CommRing S] (Lq Uq : GCx S) (ιq : GHom Uq Lq)
    (T : UnramifiedNewPlace S) where
  /-- The local complex is homotopy equivalent to the full complex of the model. -/
  eL : HomotopyEquiv Lq.toCC T.Lq.toCC
  /-- The local condition is homotopy equivalent to the unramified complex of the model. -/
  eU : HomotopyEquiv Uq.toCC T.Uq.toCC
  /-- Compatibility with the inclusions, up to homotopy. -/
  comm : Homotopy (GHom.toCC ιq ≫ eL.hom) (eU.hom ≫ GHom.toCC T.ιq)

attribute [local instance] TopRep.distribMulAction

/-- **PRINT: Elliot's tame local free model (4.4) at augmentation, for the genuine local
complexes** (tex 3470–3480). For a number field `K`, a finite set `S` of places, a Noetherian
self-injective coefficient ring `k` (a field, or a stage ring of the inner limit), a finite
discrete `G_{K,S}`-module `M`, free over `k`, of `2`-power exponent, a place `w ∈ S` with odd
residue cardinality `q`, and an unramified representation `X` of `Gal(K_w^ur/K_w)` with a
`G_{K_w}`-equivariant isomorphism `f : X ≃ M` (so inertia at `w` acts trivially on `M`): the
genuine local complex `C^•_cont(G_{K_w}, M)`, the genuine unramified condition
`[X --Φ_w − 1--> X]` and its inflation form a tame local model for `tameNewPlace X Φ_w q`, with
`Φ_w` the arithmetic Frobenius.
Literature: Iwasawa, NSW Thm 7.5.3 (tame Galois group, splitting of wild inertia); Serre, *Galois
Cohomology*, I.3.3, and NSW 1.6.2 (no cohomology of the pro-`q` wild inertia on `2`-primary
coefficients); Hochschild–Serre; local duality for `H²`. The passage from the quasi-isomorphism to
homotopy equivalences: the genuine cochains are locally constant maps `G^n → M`, a free module
(Nöbeling's theorem for profinite sets) and hence injective over a Noetherian self-injective ring
(Bass–Papp), so both sides are bounded-below complexes of injectives (K-injective). PROVED around
it: degrees `≤ 1` of the comparison (`quasiIsoAt_tameCochainMap_zero_local`,
`quasiIsoAt_tameCochainMap_one`) and, over a field, the passage from quasi-isomorphisms to this
structure (`tameLocalModelAt_of_quasiIso`). Kind: PRINT. -/
def TameLocalModelPrint : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type)
    [CommRing k] [TopologicalSpace k] [IsNoetherianRing k] [Module.Injective k k] (M : Type)
    [AddCommGroup M] [Module k M] [Module.Free k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
    (w : Places K S) (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V]
    [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x),
    Function.Bijective f → (∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0) →
    ∀ (q : ℕ) (hq : Odd q), q = Nat.card (𝓞 K ⧸ w.1.asIdeal) →
      Nonempty (TameLocalModelAt
        (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w)
        (ZInQ.Manuscript.RC.SelmerComplex.ofCC (urCx K w.1 X))
        (ZInQ.Manuscript.RC.SelmerComplex.ofCCHom (urToLocal_galois K S w X f hf))
        (tameNewPlace (ModuleCat.of k X.V)
          (ZInQ.Contrib.CloudB3RC53.UnramifiedComplex.frob (eUr K w.1) X) q hq))

end ZInQ.Manuscript.RC.Local
