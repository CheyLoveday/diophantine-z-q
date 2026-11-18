import ZInQKernel.Contrib.OneProof.RC.CoefModules.Weil
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.ChangeCondition
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedFactorization

/-!
# Lane RC28 (coefficient modules), part 7: the local conditions at the actual modules

Manuscript `diophantine_zq.tex` (11/5), Definition `ex:arith-data` (tex 2743–2760: "the actual
derived Kummer, unramified, full and orthogonal local conditions"), tex 2810–2815 ("A full
condition is paired with the zero condition"), (4.3) at tex 3458–3463 and the support comparisons
at tex 3479–3498 ("the unramified complex `[Φ−1]`"; "the old local conditions are retained and the
unramified condition is put at the new places"; "Use it only when the actual coefficient
representation is unramified at the removed place").

Local conditions in lane RC26's format (`GaloisLocalConditions K S k M`: at every `v ∈ S` a complex
`U_v` with a cochain map `U_v → C^•_cont(G_{K_v}, M)`), assembled place by place:

* `CondAt K S k M v`: a local condition at one place; `CondAt.IsInjective` (a subcomplex of the
  local cochains, the shape required by the leaf's `IsGaloisSelData`).
* `fullAt`: **the full condition** `U_v = C^•_cont(G_{K_v}, M)` (identity); `zeroAt`: **the zero
  condition** `U_v = 0`; both injective.
* **The unramified condition at a place where the coefficients are unramified**: for a module `M₀`
  over `G_{K,S₀}` inflated to `G_{K,S}` (`S₀ ⊆ S`, `InflMod`), at `w ∈ S − S₀` the localization
  factors through `Gal(K_w^{ur}/K_w)` (lane RC26's `urFactor`, PROVED there), so `M₀` is a
  representation `urRep` of `Gal(K_w^{ur}/K_w)` and RC26's genuine `urToLocal_galois`
  (inflation of the `ℤ̂`-cocycles of `[M₀ --(Φ−1)--> M₀]`) is the unramified condition `urAt`;
  injective (RC26's `urToLocal_galois_injective`).
* `ofCondAt`: the local conditions at all places from one choice per place; `ofCondAt_injective`.
* For the actual `M_i = (E[2^i] ⊗ A_i)(α)` over `G_{K,S₀}`: `MinS` (its inflation to `S`), the
  conditions `actualConditions` (unramified at `S − S₀`, any given condition at `S₀`, e.g. full
  or zero there), all injective.

The Kummer condition is in `Kummer.lean`. Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain CategoryTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (idGHom zeroGHom)
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (urCx resUr)

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

section Generic

variable (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

/-- The genuine local complex `C^•_cont(G_{K_v}, M)` at `v ∈ S`. -/
abbrev locAt (v : Places K S) : GCx k :=
  localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M v

/-- **A local condition at one place `v ∈ S`**: a complex `U_v` and a cochain map
`U_v → C^•_cont(G_{K_v}, M)` (Nekovář 6.1.1). -/
structure CondAt (v : Places K S) where
  /-- The complex `U_v`. -/
  U : GCx k
  /-- The map `i_v : U_v → C^•_cont(G_{K_v}, M)`. -/
  i : GHom U (locAt K S k M v)

variable {K S k M}

/-- The condition is a subcomplex of the local cochains (injective in every degree). -/
def CondAt.IsInjective {v : Places K S} (c : CondAt K S k M v) : Prop :=
  ∀ n : ℤ, Function.Injective (c.i.f n n rfl)

variable (K S k M)

/-- **The full condition** `U_v = C^•_cont(G_{K_v}, M)`. -/
def fullAt (v : Places K S) : CondAt K S k M v := ⟨locAt K S k M v, idGHom _⟩

/-- **The zero condition** `U_v = 0`. -/
def zeroAt (v : Places K S) : CondAt K S k M v := ⟨zeroCx k, zeroGHom _ _⟩

theorem fullAt_isInjective (v : Places K S) : (fullAt K S k M v).IsInjective :=
  fun _ _ _ h => h

theorem zeroAt_isInjective (v : Places K S) : (zeroAt K S k M v).IsInjective :=
  fun _ x y _ => Subsingleton.elim (α := PUnit) x y

/-- **The local conditions from one choice per place.** -/
def ofCondAt (c : ∀ v : Places K S, CondAt K S k M v) : GaloisLocalConditions K S k M :=
  ⟨fun v => (c v).U, fun v => (c v).i⟩

theorem ofCondAt_injective (c : ∀ v : Places K S, CondAt K S k M v) (hc : ∀ v, (c v).IsInjective)
    (v : Places K S) (n : ℤ) : Function.Injective (((ofCondAt K S k M c).i v).f n n rfl) :=
  hc v n

/-- The full conditions everywhere are lane RC26's `relaxedConditions`. -/
theorem ofCondAt_fullAt :
    ofCondAt K S k M (fullAt K S k M) = relaxedConditions k _ _ _ M := rfl

/-- The zero conditions everywhere are lane RC26's `strictConditions`. -/
theorem ofCondAt_zeroAt :
    ofCondAt K S k M (zeroAt K S k M) = strictConditions k _ _ _ M := rfl

end Generic

/-! ### The unramified condition at a place where the coefficients are unramified -/

section Unramified

variable {K S} {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (k : Type) [CommRing k]
  (M₀ : Type) [AddCommGroup M₀] [Module k M₀] [DistribMulAction (GKS K S₀) M₀]
  [SMulCommClass (GKS K S₀) k M₀] [TopologicalSpace M₀] [DiscreteTopology M₀]
  [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]

/-- **The inflation of a `G_{K,S₀}`-module to `G_{K,S}`** (`S₀ ⊆ S`), through the restriction
`G_{K,S} → G_{K,S₀}` (lane RC26's `inflMap`). -/
abbrev InflMod : Type := ResMod (inflMap K hS) M₀

instance : IsTopologicalAddGroup M₀ where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

/-- The new place `w ∈ S − S₀`. -/
abbrev newPlace (w : Places K S) (hw : w.1 ∉ S₀) : NewPlaces K S₀ S := ⟨w.1, w.2, hw⟩

/-- `Gal(K_w^{ur}/K_w)` acting on `M₀` through the factorization of the localization
(`urFactor`), as continuous `k`-linear maps. -/
def urRho (w : NewPlaces K S₀ S) : GUr K w.1 →* (M₀ →L[k] M₀) where
  toFun γ := ⟨{ toFun := fun x => (urFactor K w γ) • x
                map_add' := smul_add _
                map_smul' := fun c x => smul_comm _ c x }, continuous_of_discreteTopology⟩
  map_one' := by
    ext x
    change (urFactor K w 1) • x = x
    rw [map_one, one_smul]
  map_mul' γ δ := by
    ext x
    change (urFactor K w (γ * δ)) • x = (urFactor K w γ) • ((urFactor K w δ) • x)
    rw [map_mul, mul_smul]

variable [TopologicalSpace k] [DiscreteTopology k]

instance : ContinuousSMul k M₀ := ⟨continuous_of_discreteTopology⟩

/-- **`M₀` as a representation of `Gal(K_w^{ur}/K_w)`** at a place `w ∉ S₀` (the coefficients
are unramified at `w`). -/
def urRep (w : NewPlaces K S₀ S) : TopRep.{0} k (GUr K w.1) :=
  TopRep.of (ContRepresentation.ofMonoidHom (urRho k M₀ w))

instance (w : NewPlaces K S₀ S) : DiscreteTopology (urRep k M₀ w).V :=
  inferInstanceAs (DiscreteTopology M₀)

instance (w : NewPlaces K S₀ S) : Finite (urRep k M₀ w).V := inferInstanceAs (Finite M₀)

attribute [local instance] TopRep.distribMulAction

theorem urRep_continuousSMul (w : NewPlaces K S₀ S) : ContinuousSMul (GUr K w.1) (urRep k M₀ w).V := by
  refine continuousSMul_iff_stabilizer_isOpen.mpr fun x => ?_
  have h : IsOpen (MulAction.stabilizer (GKS K S₀) (show M₀ from x) : Set (GKS K S₀)) :=
    continuousSMul_iff_stabilizer_isOpen.mp inferInstance _
  have hc := (urFactor K w).continuous.isOpen_preimage _ h
  have he : (MulAction.stabilizer (GUr K w.1) x : Set (GUr K w.1)) =
      (urFactor K w) ⁻¹' (MulAction.stabilizer (GKS K S₀) (show M₀ from x) : Set (GKS K S₀)) := by
    ext γ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage]
    rfl
  rw [he]
  exact hc

/-- The identity `M₀ → M₀` as a map from the `Gal(K_w^{ur}/K_w)`-representation to the inflated
`G_{K,S}`-module. -/
def urId (w : NewPlaces K S₀ S) : (urRep k M₀ w).V →ₗ[k] InflMod hS M₀ := LinearMap.id

/-- The compatibility `f (resUr g • x) = locMap g • f x` for the unramified condition
(lane RC26's `locMap_compat` and `urFactor_spec`). Kind: PROVED. -/
theorem urId_compat (w : Places K S) (hw : w.1 ∉ S₀) (g : Gloc K w.1)
    (x : (urRep k M₀ (newPlace w hw)).V) :
    urId hS k M₀ (newPlace w hw) (resUr K w.1 g • x) = locMap K S w.1 g • urId hS k M₀ _ x := by
  change (urFactor K (newPlace w hw) (resUr K w.1 g)) • (show M₀ from x) =
    (inflMap K hS (locMap K S w.1 g)) • (show M₀ from x)
  rw [locMap_compat K hS w.1 g, urFactor_spec K (newPlace w hw) g]
  rfl

/-- **The unramified condition** at `w ∈ S − S₀` for the inflated module: lane RC26's genuine
`urToLocal_galois`, `[M₀ --(Φ_w−1)--> M₀] → C^•_cont(G_{K_w}, M₀)` (tex 3479–3481, 3483–3487). -/
def urAt (w : Places K S) (hw : w.1 ∉ S₀) : CondAt K S k (InflMod hS M₀) w :=
  haveI := urRep_continuousSMul k M₀ (newPlace w hw)
  ⟨ofCC (urCx K w.1 (urRep k M₀ (newPlace w hw))),
    ofCCHom (urToLocal_galois K S w (urRep k M₀ (newPlace w hw)) (urId hS k M₀ _)
      (urId_compat hS k M₀ w hw))⟩

/-- The unramified condition is a subcomplex of the local cochains. Kind: PROVED (lane RC26's
`urToLocal_galois_injective`). -/
theorem urAt_isInjective (w : Places K S) (hw : w.1 ∉ S₀) : (urAt hS k M₀ w hw).IsInjective :=
  haveI := urRep_continuousSMul k M₀ (newPlace w hw)
  fun n => urToLocal_galois_injective K S w (urRep k M₀ (newPlace w hw)) (urId hS k M₀ _)
    (urId_compat hS k M₀ w hw) (fun _ _ h => h) n

open Classical in
/-- **Unramified conditions at the new places `S − S₀`, given conditions at `S₀`.** -/
def urOutside (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k (InflMod hS M₀) v) :
    ∀ v : Places K S, CondAt K S k (InflMod hS M₀) v :=
  fun v => if h : v.1 ∈ S₀ then c v h else urAt hS k M₀ v h

theorem urOutside_isInjective (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k (InflMod hS M₀) v)
    (hc : ∀ v h, (c v h).IsInjective) (v : Places K S) : (urOutside hS k M₀ c v).IsInjective := by
  unfold urOutside
  split_ifs with h
  · exact hc v h
  · exact urAt_isInjective hS k M₀ v h

end Unramified

/-! ### At the actual coefficient modules -/

section Actual

variable {K S} {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (α : GKS K S₀ →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [IsOpenKer α]

/-- **The actual `M_i` over `G_{K,S}`**: `M_i = (E[2^i] ⊗ A_i)(α)` built over `G_{K,S₀}` (`S₀` the
ramification support of the coefficients: the primes above `2N`, the moving prime and the twist),
inflated to the Selmer support `S ⊇ S₀`. -/
abbrev MinS : Type := InflMod hS (Mcoef K S₀ W i α)

/-- **The actual local conditions**: the given conditions at the old places `S₀` (full, zero,
Kummer, …) and the unramified condition at the new places `S − S₀` (tex 3483–3498). -/
def actualConditions [TopologicalSpace (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)]
    [DiscreteTopology (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)]
    (c : ∀ v : Places K S, v.1 ∈ S₀ →
      CondAt K S (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (MinS hS W i α) v) :
    GaloisLocalConditions K S (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (MinS hS W i α) :=
  ofCondAt K S _ _ (urOutside hS _ (Mcoef K S₀ W i α) c)

end Actual

end ZInQ.Manuscript.RC.CoefModules
