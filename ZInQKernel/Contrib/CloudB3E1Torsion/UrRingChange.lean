import ZInQKernel.Contrib.CloudB3E1Torsion.SelRingChange
import ZInQKernel.Contrib.OneProof.RC.CoefModules.LocalConditions

/-!
# The unramified and full conditions along a ring isomorphism

Manuscript `diophantine_zq.tex`, tex 3471–3487 (the unramified condition `[Φ_w − 1]` at the new
places), 4385–4414.

This continues `SelRingChange.lean` (piece (3) of `GenCxResidualIso`). Take a coefficient module
`M₀` with two module structures: over `k` and over `k'`, related by a ring isomorphism
`e : k ≃+* k'` with `r • m = e r • m`. This is the case of `M_i` over `StageRing s` through
`stageEquiv s` against `M_i` over `A_s`.

* **`frobSEquiv`** (definition, PROVED fields): `[W --(Φ−1)--> W]` over `k` against the same over
  `k'`, degreewise semilinear and commuting with `d`.
* **`urAtSEquiv`**, **`urAtSEquiv_ι`** (PROVED): the unramified condition `urAt` over `k` against
  `urAt` over `k'`, compatible with the condition maps into the local cochains. The `1`-cocycles
  `c_x` of `Gal(K_w^ur/K_w)` are continuous cocycles with the same value `x` at the Frobenius, so
  they agree (`urCocycle_congr`).
* `fullAtSEquiv`, `fullAtSEquiv_ι` (PROVED): the full condition.
* `CondSEquiv` (structure): a condition over `k` against one over `k'` (complexes and maps);
  `urAtCond`, `fullAtCond`; **`outsideCond`**: the conditions `urOutside c` (given ones at the old
  places, unramified ones at the new places) from old-place `CondSEquiv`s.
* **`actualForm_ringChange`** (PROVED): `selCx (galoisSelData … (ofCondAt (urOutside c)))` over
  `k` against the same over `k'`, degreewise semilinear and commuting with `d`, from the old-place
  condition isomorphisms alone. These are the inputs `fR`, `hfR`, `hdR` of
  `genCxResidualIso_of_ringChange` for lane E2's `actualFormConds` against the standard-old
  family's `actualConditions`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-! ### Subsingletons -/

/-- The additive isomorphism of two subsingleton groups. Kind: definition. -/
def zeroAddEquiv (A B : Type*) [AddCommGroup A] [AddCommGroup B] [Subsingleton A]
    [Subsingleton B] : A ≃+ B where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_add' _ _ := (add_zero 0).symm

/-! ### The Frobenius complex -/

section Frob

variable {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') {V : Type} [AddCommGroup V]
  [Module k V] [Module k' V] (hV : ∀ (r : k) (v : V), r • v = e r • v)
  (Φ : V →ₗ[k] V) (Φ' : V →ₗ[k'] V) (hΦ : ∀ v, Φ v = Φ' v)

theorem frobCx_subsingleton {R : Type} [Ring R] {W : Type} [AddCommGroup W] [Module R W]
    (Ψ : W →ₗ[R] W) (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) : Subsingleton ((frobCx Ψ).X n) :=
  ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_double_X _ _ n h0 h1)

/-- The structural isomorphism in degree `0`. Kind: definition. -/
abbrev i0 {R : Type} [Ring R] {W : Type} [AddCommGroup W] [Module R W] (Ψ : W →ₗ[R] W) :
    (frobCx Ψ).X 0 ≅ ModuleCat.of R W :=
  HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (Ψ - 1)) rel01

/-- The structural isomorphism in degree `1`. Kind: definition. -/
abbrev i1 {R : Type} [Ring R] {W : Type} [AddCommGroup W] [Module R W] (Ψ : W →ₗ[R] W) :
    (frobCx Ψ).X 1 ≅ ModuleCat.of R W :=
  HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (Ψ - 1)) rel01 (by decide)

/-- The degree-`0` identification. Kind: definition. -/
def frobX0 : (frobCx Φ).X 0 ≃+ (frobCx Φ').X 0 :=
  (i0 Φ).toLinearEquiv.toAddEquiv.trans
    ((AddEquiv.refl V).trans (i0 Φ').symm.toLinearEquiv.toAddEquiv)

/-- The degree-`1` identification. Kind: definition. -/
def frobX1 : (frobCx Φ).X 1 ≃+ (frobCx Φ').X 1 :=
  (i1 Φ).toLinearEquiv.toAddEquiv.trans
    ((AddEquiv.refl V).trans (i1 Φ').symm.toLinearEquiv.toAddEquiv)

/-- The degreewise identification of the Frobenius complexes. Kind: definition. -/
def frobXEquiv : ∀ n : ℤ, (frobCx Φ).X n ≃+ (frobCx Φ').X n
  | Int.ofNat 0 => frobX0 Φ Φ'
  | Int.ofNat 1 => frobX1 Φ Φ'
  | Int.ofNat (n + 2) =>
    haveI := frobCx_subsingleton Φ (Int.ofNat (n + 2)) (by rw [Int.ofNat_eq_natCast]; omega)
      (by rw [Int.ofNat_eq_natCast]; omega)
    haveI := frobCx_subsingleton Φ' (Int.ofNat (n + 2)) (by rw [Int.ofNat_eq_natCast]; omega)
      (by rw [Int.ofNat_eq_natCast]; omega)
    zeroAddEquiv _ _
  | Int.negSucc m =>
    haveI := frobCx_subsingleton Φ (Int.negSucc m) (by rw [Int.negSucc_eq]; omega)
      (by rw [Int.negSucc_eq]; omega)
    haveI := frobCx_subsingleton Φ' (Int.negSucc m) (by rw [Int.negSucc_eq]; omega)
      (by rw [Int.negSucc_eq]; omega)
    zeroAddEquiv _ _

theorem i0_inv_hom {R : Type} [Ring R] {W : Type} [AddCommGroup W] [Module R W]
    (Ψ : W →ₗ[R] W) (v : W) : (i0 Ψ).hom.hom ((i0 Ψ).inv.hom v) = v :=
  congrArg (fun g => ModuleCat.Hom.hom g v) (i0 Ψ).inv_hom_id

theorem i1_inv_hom {R : Type} [Ring R] {W : Type} [AddCommGroup W] [Module R W]
    (Ψ : W →ₗ[R] W) (v : W) : (i1 Ψ).hom.hom ((i1 Ψ).inv.hom v) = v :=
  congrArg (fun g => ModuleCat.Hom.hom g v) (i1 Ψ).inv_hom_id

theorem frobX0_apply (x : (frobCx Φ).X 0) :
    (i0 Φ').hom.hom (frobX0 Φ Φ' x) = (i0 Φ).hom.hom x :=
  i0_inv_hom Φ' _

theorem frobX1_apply (x : (frobCx Φ).X 1) :
    (i1 Φ').hom.hom (frobX1 Φ Φ' x) = (i1 Φ).hom.hom x :=
  i1_inv_hom Φ' _


theorem d01_apply {R : Type} [Ring R] {W : Type} [AddCommGroup W] [Module R W]
    (Ψ : W →ₗ[R] W) (x : (frobCx Ψ).X 0) :
    ((frobCx Ψ).d 0 1).hom x = (i1 Ψ).inv.hom ((Ψ - 1) ((i0 Ψ).hom.hom x)) := by
  rw [frobCx_d01]
  rfl

include hV in
theorem frobXEquiv_smul : ∀ (n : ℤ) (r : k) (x : (frobCx Φ).X n),
    frobXEquiv Φ Φ' n (r • x) = e r • frobXEquiv Φ Φ' n x
  | Int.ofNat 0, r, x => by
    change (i0 Φ').inv.hom ((i0 Φ).hom.hom (r • x)) = e r • (i0 Φ').inv.hom ((i0 Φ).hom.hom x)
    rw [map_smul, hV, map_smul]
  | Int.ofNat 1, r, x => by
    change (i1 Φ').inv.hom ((i1 Φ).hom.hom (r • x)) = e r • (i1 Φ').inv.hom ((i1 Φ).hom.hom x)
    rw [map_smul, hV, map_smul]
  | Int.ofNat (n + 2), _, _ => by
    have := frobCx_subsingleton Φ' (Int.ofNat (n + 2)) (by rw [Int.ofNat_eq_natCast]; omega)
      (by rw [Int.ofNat_eq_natCast]; omega)
    exact Subsingleton.elim _ _
  | Int.negSucc m, _, _ => by
    have := frobCx_subsingleton Φ' (Int.negSucc m) (by rw [Int.negSucc_eq]; omega)
      (by rw [Int.negSucc_eq]; omega)
    exact Subsingleton.elim _ _

include hΦ in
theorem frobXEquiv_comm (i j : ℤ) (h : i + 1 = j) (x : (frobCx Φ).X i) :
    frobXEquiv Φ Φ' j (((frobCx Φ).d i j).hom x) =
      ((frobCx Φ').d i j).hom (frobXEquiv Φ Φ' i x) := by
  by_cases hj : j = 0 ∨ j = 1
  · rcases hj with rfl | rfl
    · have := frobCx_subsingleton Φ i (by omega) (by omega)
      rw [Subsingleton.elim x 0]
      simp only [map_zero]
    · obtain rfl : i = 0 := by omega
      change (i1 Φ').inv.hom ((i1 Φ).hom.hom (((frobCx Φ).d 0 1).hom x)) =
        ((frobCx Φ').d 0 1).hom ((i0 Φ').inv.hom ((i0 Φ).hom.hom x))
      rw [d01_apply, d01_apply, i1_inv_hom Φ, i0_inv_hom Φ']
      congr 1
      simp only [LinearMap.sub_apply, Module.End.one_apply, hΦ]
  · push Not at hj
    have := frobCx_subsingleton Φ' j hj.1 hj.2
    exact Subsingleton.elim _ _

/-- **The Frobenius complex over `k` against the same over `k'`.** Kind: definition (PROVED
fields). -/
def frobSEquiv : GCxSEquiv e (ofCC (frobCx Φ)) (ofCC (frobCx Φ')) where
  f := frobXEquiv Φ Φ'
  smul := frobXEquiv_smul e hV Φ Φ'
  comm i j h x := frobXEquiv_comm Φ Φ' hΦ i j h x

end Frob

/-! ### The components of the unramified condition map -/

section UrComponents

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  {k : Type} [CommRing k] [TopologicalSpace k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]

theorem urToLocal_galois_f₀ (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x) :
    (urToLocal_galois K S w X f hf).f 0 =
      (HomologicalComplex.doubleXIso₀ _ rel01).hom ≫
        ModuleCat.ofHom (urLin₀ (G := Gloc K w.1) (M := ResMod (locMap K S w.1) M) X f) :=
  urToLocal_f₀ _ _ _ _ _

theorem urToLocal_galois_f₁ (w : Places K S) (X : TopRep.{0} k (GUr K w.1))
    [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V] [Finite X.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x) :
    (urToLocal_galois K S w X f hf).f 1 =
      (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).hom ≫
        ModuleCat.ofHom (urLin₁ (M := ResMod (locMap K S w.1) M) (eUr K w.1) (resUr K w.1) X f) :=
  urToLocal_f₁ _ _ _ _ _

end UrComponents

/-! ### The unramified condition -/

section Unramified

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace k'] [DiscreteTopology k']
  (M₀ : Type) [AddCommGroup M₀] [Module k M₀] [Module k' M₀] [DistribMulAction (GKS K S₀) M₀]
  [SMulCommClass (GKS K S₀) k M₀] [SMulCommClass (GKS K S₀) k' M₀] [TopologicalSpace M₀]
  [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  (hV : ∀ (r : k) (m : M₀), r • m = e r • m)

/-- **The unramified condition over `k` against the same over `k'`** (the complexes).
Kind: definition. -/
def urAtSEquiv (w : Places K S) (hw : w.1 ∉ S₀) :
    GCxSEquiv e (urAt hS k M₀ w hw).U (urAt hS k' M₀ w hw).U :=
  frobSEquiv e (V := M₀) hV (frob (eUr K w.1) (urRep k M₀ (newPlace w hw)))
    (frob (eUr K w.1) (urRep k' M₀ (newPlace w hw))) (fun _ => rfl)

/-- The local cochains of the inflated module along the identity. Kind: definition. -/
abbrev inflLocalSEquiv (w : Places K S) :=
  localSEquiv e (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
    (AddEquiv.refl (InflMod hS M₀)) continuous_id continuous_id (fun r m => hV r m)
    (fun _ _ => rfl) w

/-- **The unramified condition maps are compatible** with the identifications (degree `1`: the
`ℤ̂`-cocycles `c_x` agree). Kind: PROVED. -/
theorem urAtSEquiv_ι (w : Places K S) (hw : w.1 ∉ S₀) (i j : ℤ) (h : i = j)
    (x : (urAt hS k M₀ w hw).U.X i) :
    (inflLocalSEquiv hS e M₀ hV w).f j ((urAt hS k M₀ w hw).i.f i j h x) =
      (urAt hS k' M₀ w hw).i.f i j h ((urAtSEquiv hS e M₀ hV w hw).f i x) := by
  subst h
  have := urRep_continuousSMul k M₀ (newPlace w hw)
  have := urRep_continuousSMul k' M₀ (newPlace w hw)
  rcases i with (_ | _ | n) | m
  · change (inflLocalSEquiv hS e M₀ hV w).f 0
        (((urToLocal_galois K S w (urRep k M₀ (newPlace w hw)) (urId hS k M₀ _)
          (urId_compat hS k M₀ w hw)).f 0).hom x) =
        ((urToLocal_galois K S w (urRep k' M₀ (newPlace w hw)) (urId hS k' M₀ _)
          (urId_compat hS k' M₀ w hw)).f 0).hom ((urAtSEquiv hS e M₀ hV w hw).f 0 x)
    rw [urToLocal_galois_f₀, urToLocal_galois_f₀]
    apply Subtype.ext
    funext y
    change (i0 (frob (eUr K w.1) (urRep k M₀ (newPlace w hw)))).hom.hom x =
      (i0 (frob (eUr K w.1) (urRep k' M₀ (newPlace w hw)))).hom.hom
        (frobX0 (V := M₀) (frob (eUr K w.1) (urRep k M₀ (newPlace w hw)))
          (frob (eUr K w.1) (urRep k' M₀ (newPlace w hw))) x)
    exact (i0_inv_hom (frob (eUr K w.1) (urRep k' M₀ (newPlace w hw)))
      ((i0 (frob (eUr K w.1) (urRep k M₀ (newPlace w hw)))).hom.hom x)).symm
  · change (inflLocalSEquiv hS e M₀ hV w).f 1
        (((urToLocal_galois K S w (urRep k M₀ (newPlace w hw)) (urId hS k M₀ _)
          (urId_compat hS k M₀ w hw)).f 1).hom x) =
        ((urToLocal_galois K S w (urRep k' M₀ (newPlace w hw)) (urId hS k' M₀ _)
          (urId_compat hS k' M₀ w hw)).f 1).hom ((urAtSEquiv hS e M₀ hV w hw).f 1 x)
    rw [urToLocal_galois_f₁, urToLocal_galois_f₁]
    apply Subtype.ext
    funext y
    change urCocycle (eUr K w.1) (urRep k M₀ (newPlace w hw))
        ((i1 (frob (eUr K w.1) (urRep k M₀ (newPlace w hw)))).hom.hom x) (resUr K w.1 (y 0)) =
      urCocycle (eUr K w.1) (urRep k' M₀ (newPlace w hw))
        ((i1 (frob (eUr K w.1) (urRep k' M₀ (newPlace w hw)))).hom.hom
          ((i1 (frob (eUr K w.1) (urRep k' M₀ (newPlace w hw)))).inv.hom
            ((i1 (frob (eUr K w.1) (urRep k M₀ (newPlace w hw)))).hom.hom x))) (resUr K w.1 (y 0))
    have key : ∀ v : M₀, urCocycle (eUr K w.1) (urRep k M₀ (newPlace w hw)) v (resUr K w.1 (y 0)) =
        urCocycle (eUr K w.1) (urRep k' M₀ (newPlace w hw)) v (resUr K w.1 (y 0)) :=
      fun v => rfl
    exact (key _).trans (congrArg
      (fun v : M₀ => urCocycle (eUr K w.1) (urRep k' M₀ (newPlace w hw)) v (resUr K w.1 (y 0)))
      (i1_inv_hom (frob (eUr K w.1) (urRep k' M₀ (newPlace w hw)))
        ((i1 (frob (eUr K w.1) (urRep k M₀ (newPlace w hw)))).hom.hom x)).symm)
  · have hx : x = 0 := @Subsingleton.elim _
      (frobCx_subsingleton (frob (eUr K w.1) (urRep k M₀ (newPlace w hw))) (Int.ofNat (n + 2))
        (by rw [Int.ofNat_eq_natCast]; omega) (by rw [Int.ofNat_eq_natCast]; omega)) x 0
    rw [hx]
    simp only [map_zero]
  · have hx : x = 0 := @Subsingleton.elim _
      (frobCx_subsingleton (frob (eUr K w.1) (urRep k M₀ (newPlace w hw))) (Int.negSucc m)
        (by rw [Int.negSucc_eq]; omega) (by rw [Int.negSucc_eq]; omega)) x 0
    rw [hx]
    simp only [map_zero]

/-- **The full condition over `k` against the same over `k'`.** Kind: definition. -/
abbrev fullAtSEquiv (v : Places K S) :
    GCxSEquiv e (fullAt K S k (InflMod hS M₀) v).U (fullAt K S k' (InflMod hS M₀) v).U :=
  inflLocalSEquiv hS e M₀ hV v

omit [TopologicalSpace k] [DiscreteTopology k] [TopologicalSpace k'] [DiscreteTopology k']
  [Finite M₀] in
theorem fullAtSEquiv_ι (v : Places K S) (i j : ℤ) (h : i = j)
    (x : (fullAt K S k (InflMod hS M₀) v).U.X i) :
    (inflLocalSEquiv hS e M₀ hV v).f j ((fullAt K S k (InflMod hS M₀) v).i.f i j h x) =
      (fullAt K S k' (InflMod hS M₀) v).i.f i j h ((fullAtSEquiv hS e M₀ hV v).f i x) := by
  subst h
  rfl

/-- **A condition over `k` against a condition over `k'`** at a place `v`: a degreewise
semilinear isomorphism of the complexes, compatible with the condition maps. Kind: definition
(structure). -/
structure CondSEquiv (v : Places K S) (d : CondAt K S k (InflMod hS M₀) v)
    (d' : CondAt K S k' (InflMod hS M₀) v) where
  /-- the complexes -/
  E : GCxSEquiv e d.U d'.U
  /-- compatibility with the condition maps -/
  hι : ∀ i j (hij : i = j) (x : d.U.X i),
    (inflLocalSEquiv hS e M₀ hV v).f j (d.i.f i j hij x) = d'.i.f i j hij (E.f i x)

/-- The unramified condition, as a `CondSEquiv`. Kind: definition. -/
def urAtCond (w : Places K S) (hw : w.1 ∉ S₀) :
    CondSEquiv hS e M₀ hV w (urAt hS k M₀ w hw) (urAt hS k' M₀ w hw) :=
  ⟨urAtSEquiv hS e M₀ hV w hw, urAtSEquiv_ι hS e M₀ hV w hw⟩

/-- The full condition, as a `CondSEquiv`. Kind: definition. -/
def fullAtCond (v : Places K S) :
    CondSEquiv hS e M₀ hV v (fullAt K S k (InflMod hS M₀) v) (fullAt K S k' (InflMod hS M₀) v) :=
  ⟨fullAtSEquiv hS e M₀ hV v, fullAtSEquiv_ι hS e M₀ hV v⟩

variable {hS e M₀ hV}

/-- **The conditions `urOutside c` over `k` against `urOutside c'` over `k'`**, from the old
places. Kind: definition. -/
def outsideCond {c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k (InflMod hS M₀) v}
    {c' : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k' (InflMod hS M₀) v}
    (EU : ∀ v h, CondSEquiv hS e M₀ hV v (c v h) (c' v h)) (v : Places K S) :
    CondSEquiv hS e M₀ hV v (urOutside hS k M₀ c v) (urOutside hS k' M₀ c' v) := by
  unfold urOutside
  split_ifs with h
  · exact EU v h
  · exact urAtCond hS e M₀ hV v h

/-- **The actual-conditions Selmer complex along a ring isomorphism** (tex 4385–4414): for `M₀`
over `k` and over `k'` with `r • m = e r • m`, old conditions `c` over `k` and `c'` over `k'`
with condition isomorphisms `EU` at the old places, the Selmer complexes of
`ofCondAt (urOutside c)` and `ofCondAt (urOutside c')` (unramified conditions at the new places)
are related by degreewise semilinear additive isomorphisms commuting with `d`. These are the
inputs `fR`, `hfR`, `hdR` of `genCxResidualIso_of_ringChange`, for lane E2's `actualFormConds`
(`c = oldCond …`) against the standard-old family's `actualConditions` (`c' = standardOldAt …`).
Kind: PROVED. -/
theorem actualForm_ringChange {c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k (InflMod hS M₀) v}
    {c' : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S k' (InflMod hS M₀) v}
    (EU : ∀ v h, CondSEquiv hS e M₀ hV v (c v h) (c' v h)) :
    ∃ fR : ∀ n, (selCx (galoisSelData K S k (InflMod hS M₀)
        (ofCondAt K S k (InflMod hS M₀) (urOutside hS k M₀ c)))).X n ≃+
      (selCx (galoisSelData K S k' (InflMod hS M₀)
        (ofCondAt K S k' (InflMod hS M₀) (urOutside hS k' M₀ c')))).X n,
      (∀ n (r : k) x, fR n (r • x) = e r • fR n x) ∧
      ∀ i j (h : i + 1 = j) x, fR j ((selCx (galoisSelData K S k (InflMod hS M₀)
          (ofCondAt K S k (InflMod hS M₀) (urOutside hS k M₀ c)))).d i j h x) =
        (selCx (galoisSelData K S k' (InflMod hS M₀)
          (ofCondAt K S k' (InflMod hS M₀) (urOutside hS k' M₀ c')))).d i j h (fR i x) :=
  galoisSel_ringChange e (AddEquiv.refl (InflMod hS M₀)) continuous_id continuous_id
    (fun r m => hV r m) (fun _ _ => rfl) _ _ (fun v => (outsideCond EU v).E)
    (fun v i j h x => (outsideCond EU v).hι i j h x)

end Unramified

end ZInQ.Contrib.CloudB3E1Torsion
