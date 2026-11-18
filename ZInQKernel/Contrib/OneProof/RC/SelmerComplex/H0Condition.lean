import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedCondition

/-!
# Lane RC26: the `H⁰` local condition, and the degree bounds of the local conditions

Nekovář, *Selmer complexes*, Astérisque 310 (2006), 6.1 (local conditions
`i_v⁺ : U_v⁺ → C^•_cont(G_v, X)` and the Selmer complex, 6.1.1–6.1.2) and 6.2 (cup products of
Selmer complexes; the products `U_v⁺(X) ⊗ U_v⁺(Y) → C^•_cont(G_v, T)` that enter the
orthogonality conditions 6.2.1–6.2.2 vanish for degree reasons when the local conditions are
concentrated in low degrees); manuscript
`diophantine_zq.tex`, tex 3471–3481 (the unramified complex `[W --(Φ−1)--> W]` in degrees `0, 1`)
and tex 5068–5072 (local conditions concentrated in degrees `0` and `1`).

For a topological group `G_v` acting continuously on `M` (through `loc_v : G_v → G_S`):

* `invSub k G M`: the invariants `M^G = {m | ∀ g, g • m = m}`, a `k`-submodule of `M`;
* `invLin₀`, `invLin₀_d`: an invariant as a constant `0`-cochain, and its coboundary is `0`
  (`(d⁰ m)(g) = g • m − m = 0`);
* `h0Cx`, `h0ToLocal`, `h0ToLocal_f₀`: the complex `M^G[0]` concentrated in degree `0`
  (Mathlib's `HomologicalComplex.single`), with the cochain map `M^G[0] ⟶ C^•_cont(G, M)` given in
  degree `0` by the inclusion of invariants as constant `0`-cochains;
* `h0Conditions`, `galoisH0Conditions`: the **`H⁰` local conditions** `U_v = M^{G_v}[0]` at every
  place (genuine local conditions, built with `localConditionsOfCC`);
* degree bounds: `h0Conditions_subsingleton` (`U_v^i = 0` for `i ≠ 0`),
  `allUnramified_subsingleton` (`U_w^{ur, j} = 0` for `j ∉ {0, 1}`), the abstract
  `subsingleton_or_of_degrees` and the combined `h0_unramified_degrees`
  (`i + j ≥ 2 ⇒ U_w^i = 0 ∨ U_w^{ur, j} = 0`);
* non-vacuity: `invSub_trivMod_eq_top` (for the residual module `𝔽₂²` with trivial action the
  invariants are everything) and the `H⁰` conditions for it (`galoisH0ConditionsW2`,
  `galoisH0ConditionsW2_subsingleton`).

Everything is PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

universe u

/-! ### Invariants -/

section Invariants

variable (k : Type u) [CommRing k] (G : Type u) [Group G]
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]

/-- **The invariants** `M^G = H⁰(G, M) = {m ∈ M | g • m = m for all g ∈ G}`, a `k`-submodule of
`M` (the action commutes with `k`). For `G = G_v` acting through `loc_v` this is the module of the
`H⁰` local condition (Nekovář 6.1; tex 5068–5072). -/
def invSub : Submodule k M where
  carrier := {m | ∀ g : G, g • m = m}
  add_mem' := by
    intro a b ha hb g
    rw [smul_add, ha g, hb g]
  zero_mem' := by
    intro g
    exact smul_zero g
  smul_mem' := by
    intro c m hm g
    rw [smul_comm g c m, hm g]

/-- **The complex `M^G[0]`**: the invariants concentrated in degree `0` (Mathlib's
`HomologicalComplex.single` for the cochain shape `up ℤ`), the complex of the `H⁰` local
condition (Nekovář 6.1.1; tex 5068–5072). -/
abbrev h0Cx : CochainComplex (ModuleCat.{u} k) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} k) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of k (invSub k G M))

variable {k G M}

/-- Membership in the invariants `M^G`: `m ∈ M^G ↔ ∀ g, g • m = m`. -/
theorem mem_invSub {m : M} : m ∈ invSub k G M ↔ ∀ g : G, g • m = m :=
  Iff.rfl

/-- The complex `M^G[0]` vanishes outside degree `0` (Nekovář 6.1; tex 5068–5072). -/
theorem h0Cx_subsingleton (i : ℤ) (hi : i ≠ 0) : Subsingleton ((h0Cx k G M).X i) :=
  ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ i hi)

end Invariants

/-! ### The `H⁰` condition at one place -/

section Generic

variable {k : Type u} [CommRing k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- Degree `0` of the `H⁰` condition: an invariant `m ∈ M^G` as the constant `0`-cochain
`(G⁰ → M, () ↦ m)` in `C⁰_cont(G, M) = M` (Nekovář 6.1; tex 5068–5072). -/
def invLin₀ : invSub k G M →ₗ[k] contCochain k G M 0 where
  toFun m := ⟨(fun _ => (m : M) : (Fin 0 → G) → M), continuous_const⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

/-- **The coboundary of an invariant vanishes**: `(d⁰ m)(g) = g • m − m = 0` for `m ∈ M^G`, i.e.
`d⁰ ∘ invLin₀ = 0` in the genuine local complex `C^•_cont(G, M)` (so the inclusion of invariants
is a cochain map out of `M^G[0]`; Nekovář 6.1). -/
theorem invLin₀_d (j : ℤ) (hj : (ComplexShape.up ℤ).Rel 0 j) :
    ModuleCat.ofHom (invLin₀ (k := k) (G := G) (M := M)) ≫
      (natCx (contCochains k G M)).toCC.d 0 j = 0 := by
  obtain rfl : j = 1 := by simpa using hj.symm
  ext x
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := k) (G := G) (M := M) 0
    ((contSubCx k G M).ofSub (invLin₀ x)) g
  refine h1.trans ?_
  change g 0 • (x : M) + ∑ j : Fin 1, (-1 : k) ^ ((j : ℕ) + 1) • (x : M) = (0 : M)
  rw [mem_invSub.1 x.2 (g 0)]
  simp

/-- **The `H⁰` condition as a cochain map** `M^G[0] ⟶ C^•_cont(G, M)`: in degree `0` the inclusion
of invariants as constant `0`-cochains (a cochain map since their coboundary vanishes,
`invLin₀_d`); Nekovář 6.1.1, tex 5068–5072. -/
def h0ToLocal : h0Cx k G M ⟶ (natCx (contCochains k G M)).toCC :=
  HomologicalComplex.mkHomFromSingle (ModuleCat.ofHom (invLin₀ (k := k) (G := G) (M := M)))
    invLin₀_d

/-- The degree-`0` component of `h0ToLocal` is the inclusion of invariants as constant
`0`-cochains (up to the structural isomorphism `(M^G[0])⁰ ≅ M^G`); Nekovář 6.1.1. -/
theorem h0ToLocal_f₀ :
    (h0ToLocal (k := k) (G := G) (M := M)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of k (invSub k G M))).hom ≫
        ModuleCat.ofHom (invLin₀ (k := k) (G := G) (M := M)) :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- **The `H⁰` condition on elements**: for `m ∈ M^G` (in degree `0` of `M^G[0]`), its image in
`C⁰_cont(G, M)` is the constant `0`-cochain with value `m` (Nekovář 6.1.1; tex 5068–5072). -/
theorem h0ToLocal_apply (m : invSub k G M) (g : Fin 0 → G) :
    asFun k G M ((contSubCx k G M).el ((h0ToLocal (k := k) (G := G) (M := M)).f 0 |>.hom
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of k (invSub k G M))).inv m)) : contCochain k G M 0) g = m := by
  rw [h0ToLocal_f₀]
  rfl

end Generic

/-! ### The `H⁰` local conditions -/

section Conditions

variable (k : Type u) [CommRing k] (GS : Type u) [Group GS] [TopologicalSpace GS]
  [IsTopologicalGroup GS]
  {ι : Type u} (Gv : ι → Type u) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

/-- **The `H⁰` local conditions** (Nekovář 6.1.1; tex 5068–5072): at every place `v` the complex
`U_v = M^{G_v}[0]` (the `G_v`-invariants, `G_v` acting through `loc_v`, concentrated in degree
`0`) with `i_v : M^{G_v}[0] → C^•_cont(G_v, M)` the inclusion of invariants as constant
`0`-cochains; genuine local conditions via `localConditionsOfCC`. -/
def h0Conditions : LocalConditions k GS Gv loc M :=
  localConditionsOfCC (fun v => h0Cx k (Gv v) (ResMod (loc v) M))
    (fun v => h0ToLocal (k := k) (G := Gv v) (M := ResMod (loc v) M))

/-- **Degree bound for the `H⁰` conditions**: `U_v^i = 0` for `i ≠ 0` (the condition is
concentrated in degree `0`; Nekovář 6.1, 6.2; tex 5068–5072). -/
theorem h0Conditions_subsingleton :
    ∀ v (i : ℤ), i ≠ 0 → Subsingleton (((h0Conditions k GS Gv loc M).U v).X i) :=
  fun v i hi => h0Cx_subsingleton (k := k) (G := Gv v) (M := ResMod (loc v) M) i hi

end Conditions

/-! ### Abstract degree bounds -/

section Degrees

variable {k : Type u} [CommRing k] {ι : Type u}

/-- **Degree bounds for pairs of local conditions** (the degree argument behind Nekovář 6.2: a
product `U_v^i ⊗ U'_v^j` with `i + j ≥ 2` vanishes): if `A_v` is concentrated in degree `0` and
`B_v` in degrees `0, 1`, then for `i + j ≥ 2` one of `A_v^i`, `B_v^j` is zero (tex 5068–5072). -/
theorem subsingleton_or_of_degrees (A B : ι → GCx k)
    (hA : ∀ v (i : ℤ), i ≠ 0 → Subsingleton ((A v).X i))
    (hB : ∀ v (j : ℤ), j ≠ 0 → j ≠ 1 → Subsingleton ((B v).X j)) :
    ∀ v (i j : ℤ), 2 ≤ i + j → Subsingleton ((A v).X i) ∨ Subsingleton ((B v).X j) := by
  intro v i j hij
  by_cases hi : i = 0
  · subst hi
    exact Or.inr (hB v j (by omega) (by omega))
  · exact Or.inl (hA v i hi)

end Degrees

/-! ### At the places of a number field -/

section Galois

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **The `H⁰` local conditions for the genuine Galois data** (Nekovář 6.1.1; tex 5068–5072): at
every `v ∈ S` the complex `M^{G_{K_v}}[0]` with the inclusion of invariants into
`C^•_cont(G_{K_v}, M)` as constant `0`-cochains. A definition: it exists for all data. -/
def galoisH0Conditions (k : Type) [CommRing k]
    (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
    [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M] : GaloisLocalConditions K S k M :=
  h0Conditions k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M

/-- Degree bound for the Galois `H⁰` conditions: `U_v^i = 0` for `i ≠ 0` (Nekovář 6.1;
tex 5068–5072). -/
theorem galoisH0Conditions_subsingleton (k : Type) [CommRing k]
    (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
    [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M] :
    ∀ w (i : ℤ), i ≠ 0 → Subsingleton (((galoisH0Conditions K S k M).U w).X i) :=
  h0Conditions_subsingleton k (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) M

variable {k : Type} [CommRing k] [TopologicalSpace k]

/-- **Degree bound for the unramified conditions**: `U_w^{ur, j} = 0` for `j ∉ {0, 1}` (the
unramified complex `[W --(Φ_w−1)--> W]` lives in degrees `0, 1`; tex 3471–3481, 5068–5072;
Nekovář 6.1). -/
theorem allUnramified_subsingleton
    {M' : Type} [AddCommGroup M'] [Module k M'] [DistribMulAction (GKS K S) M']
    [SMulCommClass (GKS K S) k M'] [TopologicalSpace M'] [DiscreteTopology M']
    [ContinuousSMul (GKS K S) M']
    (X : ∀ w : Places K S, TopRep.{0} k (GUr K w.1))
    [∀ w, ContinuousSMul (GUr K w.1) (X w).V] [∀ w, DiscreteTopology (X w).V]
    [∀ w, Finite (X w).V]
    (f : ∀ w, (X w).V →ₗ[k] M')
    (hf : ∀ w (g : Gloc K w.1) (x : (X w).V), f w (resUr K w.1 g • x) = locMap K S w.1 g • f w x) :
    ∀ w (j : ℤ), j ≠ 0 → j ≠ 1 →
      Subsingleton (((allUnramifiedLocalConditions K S X f hf).U w).X j) :=
  fun w j h0 h1 => ModuleCat.subsingleton_of_isZero (isZero_X (frob (eUr K w.1) (X w)) j h0 h1)

/-- **The `H⁰` and unramified conditions in complementary degrees** (the degree argument of
Nekovář 6.2 for the products `U_w^i(M) ⊗ U_w^{ur, j}(M')`; tex 3471–3481, 5068–5072): for
`i + j ≥ 2` either the `H⁰` condition (coefficients `M`) vanishes in degree `i` or the unramified
condition (coefficients `M'`, unramified data `X, f`) vanishes in degree `j`. -/
theorem h0_unramified_degrees
    (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
    [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]
    {M' : Type} [AddCommGroup M'] [Module k M'] [DistribMulAction (GKS K S) M']
    [SMulCommClass (GKS K S) k M'] [TopologicalSpace M'] [DiscreteTopology M']
    [ContinuousSMul (GKS K S) M']
    (X : ∀ w : Places K S, TopRep.{0} k (GUr K w.1))
    [∀ w, ContinuousSMul (GUr K w.1) (X w).V] [∀ w, DiscreteTopology (X w).V]
    [∀ w, Finite (X w).V]
    (f : ∀ w, (X w).V →ₗ[k] M')
    (hf : ∀ w (g : Gloc K w.1) (x : (X w).V), f w (resUr K w.1 g • x) = locMap K S w.1 g • f w x) :
    ∀ w (i j : ℤ), 2 ≤ i + j →
      Subsingleton (((galoisH0Conditions K S k M).U w).X i) ∨
        Subsingleton (((allUnramifiedLocalConditions K S X f hf).U w).X j) :=
  subsingleton_or_of_degrees _ _ (galoisH0Conditions_subsingleton K S k M)
    (allUnramified_subsingleton K S X f hf)

end Galois

/-! ### Non-vacuity -/

section NonVacuity

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **Non-vacuity**: for the residual module `W = 𝔽₂²` with the trivial action of `G_{K,S}`
(tex 4479–4480) the invariants under every decomposition group `G_{K_v}` are everything,
`W^{G_{K_v}} = W` (Nekovář 6.1; tex 5068–5072). -/
theorem invSub_trivMod_eq_top (v : Places K S) :
    invSub (ZMod 2) (Gloc K v.1) (ResMod (locMap K S v.1) (TrivMod (GKS K S) (Fin 2 → ZMod 2))) =
      ⊤ :=
  Submodule.eq_top_iff'.2 fun _ => mem_invSub.2 fun _ => rfl

/-- **Non-vacuity**: the `H⁰` local conditions for the residual module `𝔽₂²` with trivial action,
`U_v = W^{G_{K_v}}[0] = W[0]` at every `v ∈ S` (Nekovář 6.1.1; tex 5068–5072). -/
def galoisH0ConditionsW2 :
    GaloisLocalConditions K S (ZMod 2) (TrivMod (GKS K S) (Fin 2 → ZMod 2)) :=
  galoisH0Conditions K S (ZMod 2) (TrivMod (GKS K S) (Fin 2 → ZMod 2))

/-- Non-vacuity of the degree bound: for `𝔽₂²` the `H⁰` conditions vanish outside degree `0`
(Nekovář 6.1; tex 5068–5072). -/
theorem galoisH0ConditionsW2_subsingleton :
    ∀ w (i : ℤ), i ≠ 0 → Subsingleton (((galoisH0ConditionsW2 K S).U w).X i) :=
  galoisH0Conditions_subsingleton K S (ZMod 2) (TrivMod (GKS K S) (Fin 2 → ZMod 2))

end NonVacuity

end ZInQ.Manuscript.RC.SelmerComplex
