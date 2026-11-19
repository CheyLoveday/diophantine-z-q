import ZInQKernel.Contrib.CloudB3E1Torsion.UrRingChange
import ZInQKernel.Contrib.OneProof.RC.CoefModules.KummerAt

/-!
# The Kummer and zero conditions along a ring isomorphism

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer` (tex 3413–3438: the Kummer
condition with coefficients extended along `ι`), tex 4385–4414.

This continues `UrRingChange.lean` (piece (3) of `GenCxResidualIso`) at the old places. Take a
discrete `G`-module `M` with two module structures, over `k` and over `k'`, related by a ring
isomorphism `e : k ≃+* k'` (`r • m = e r • m`). Then:

* `subXEquiv`, **`subSEquiv`**, `subSEquiv_ι` (PROVED): subcomplexes of the continuous cochains
  with the same members correspond, compatibly with the inclusions.
* `condP_iff` (PROVED): the cocycle condition `[C⁰ → Z ⊔ B¹]` has the same members over `k` and
  over `k'` when `Z` does. The coboundaries `B¹` correspond because `f ∘ −` commutes with `d⁰`.
* **`kummerZ'_iff`** (PROVED): the extended Kummer submodule `kummerZ'` (the span of the cocycles
  `g ↦ a • ι(κ_P(g))`) has the same members over `k` and over `k'`. The `k`-span and the
  `k'`-span of the Kummer cocycles agree, because `e` is surjective and
  `a • ι(κ_P(g)) = e a • ι(κ_P(g))`.
* **`kummerAtCond`**, `zeroAtCond` (definitions, PROVED fields): the Kummer and zero conditions
  over `k` against the same over `k'`, as `CondSEquiv`s. Together with `fullAtCond`, they cover
  every label of the standard-old conditions (`standardOldAt`: zero, full, Kummer) and the
  presentation's old conditions (`stageCondsK`: Kummer at `P`, full elsewhere).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (zeroGHom)

/-! ### Subcomplexes of the continuous cochains -/

section SubCx

variable {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k')
  {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type} [AddCommGroup M] [Module k M] [Module k' M] [DistribMulAction G M]
  [SMulCommClass G k M] [SMulCommClass G k' M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousConstSMul k' M] [ContinuousSMul G M]
  (hV : ∀ (r : k) (m : M), r • m = e r • m)

/-- The identity on cochains, from `k` to `k'`. Kind: definition. -/
abbrev φc (n : ℕ) : (contCochains k G M).X n ≃+ (contCochains k' G M).X n :=
  cochainSEquiv (k := k) (k' := k') (AddEquiv.refl M) continuous_id continuous_id n

variable (P : SubCx (contCochains k G M)) (Q : SubCx (contCochains k' G M))
  (hPQ : ∀ n x, x ∈ P.P n ↔ φc (k' := k') n x ∈ Q.P n)

/-- The degreewise identification of the subcomplexes. Kind: definition. -/
def subXEquiv (n : ℕ) : P.toCx.X n ≃+ Q.toCx.X n where
  toFun x := Q.ofSub ⟨φc (k' := k') n (P.el x).1, (hPQ n _).1 (P.el x).2⟩
  invFun y := P.ofSub ⟨(φc (k' := k') n).symm (Q.el y).1,
    (hPQ n _).2 (by rw [AddEquiv.apply_symm_apply]; exact (Q.el y).2)⟩
  left_inv x := Subtype.ext ((φc (k' := k') n).symm_apply_apply _)
  right_inv y := Subtype.ext ((φc (k' := k') n).apply_symm_apply _)
  map_add' x y := Subtype.ext (map_add (φc (k' := k') n) _ _)

/-- **Subcomplexes with the same members, over `k` and over `k'`.** Kind: definition (PROVED
fields). -/
def subSEquiv : GCxSEquiv e (natCx P.toCx) (natCx Q.toCx) :=
  natSEquiv (subXEquiv P Q hPQ)
    (fun n r x => Subtype.ext (cochainSEquiv_smul (fun r m => hV r m) n r (P.el x).1))
    (fun n x => by
      apply Subtype.ext
      rw [SubCx.toCx_d_apply]
      change φc (k' := k') (n + 1) ((P.el ((P.toCx.d n (n + 1)).hom x)).1) = _
      rw [SubCx.toCx_d_apply]
      exact cochainSEquiv_d (fun r m => hV r m) (fun _ _ => rfl) n _)

/-- The identification commutes with the inclusions into the cochains. Kind: PROVED. -/
theorem subSEquiv_ι (i j : ℤ) (h : i = j) (x : (natCx P.toCx).X i) :
    (natSEquiv (cochainSEquiv (k := k) (k' := k') (AddEquiv.refl M) continuous_id continuous_id)
        (cochainSEquiv_smul (fun r m => hV r m)) (cochainSEquiv_d (fun r m => hV r m)
          (fun _ _ => rfl))).f j ((natHom P.ι).f i j h x) =
      (natHom Q.ι).f i j h ((subSEquiv e hV P Q hPQ).f i x) := by
  subst h
  rcases i with n | n
  · rfl
  · rfl

end SubCx

/-! ### The cocycle condition and the Kummer submodule -/

section Cocycle

variable {k k' : Type} [CommRing k] [CommRing k'] {e : k ≃+* k'}
  {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type} [AddCommGroup M] [Module k M] [Module k' M] [DistribMulAction G M]
  [SMulCommClass G k M] [SMulCommClass G k' M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousConstSMul k' M] [ContinuousSMul G M]
  (hV : ∀ (r : k) (m : M), r • m = e r • m)

/-- The identity on continuous cochains, from `k` to `k'` (as submodule elements).
Kind: definition. -/
abbrev φs (n : ℕ) : contCochain k G M n ≃+ contCochain k' G M n :=
  φc (k := k) (k' := k') (G := G) (M := M) n

include hV in
theorem φs_smul (n : ℕ) (r : k) (y : contCochain k G M n) :
    φs (k' := k') n (r • y) = e r • φs (k' := k') n y :=
  Subtype.ext (funext fun _ => hV r _)

include hV in
/-- `f ∘ −` carries coboundaries to coboundaries, both ways. Kind: PROVED. -/
theorem contB1_iff (x : contCochain k G M 1) :
    x ∈ contB1 k G M ↔ φs (k' := k') 1 x ∈ contB1 k' G M := by
  have hd : ∀ c : contCochain k G M 0,
      φs (k' := k') 1 (contD k G M 0 c) = contD k' G M 0 (φs (k' := k') 0 c) :=
    fun c => cochainSEquiv_d (fun r m => hV r m) (fun _ _ => rfl) 0 c
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨φs (k' := k') 0 c, (hd c).symm⟩
  · rintro ⟨c', hc'⟩
    refine ⟨(φs (k' := k') 0).symm c', (φs (k' := k') 1).injective ?_⟩
    change φs (k' := k') 1 (contD k G M 0 ((φs (k' := k') 0).symm c')) = φs (k' := k') 1 x
    rw [hd, AddEquiv.apply_symm_apply]
    exact hc'

include hV in
/-- **The cocycle condition has the same members over `k` and over `k'`** when `Z` does.
Kind: PROVED. -/
theorem condP_iff (Z : Submodule k (contCochain k G M 1))
    (Z' : Submodule k' (contCochain k' G M 1))
    (hZ : ∀ x, x ∈ Z ↔ φs (k' := k') 1 x ∈ Z') :
    ∀ n x, x ∈ condP Z n ↔ φs (k' := k') n x ∈ condP Z' n
  | 0, _ => ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩
  | 1, x => by
    change x ∈ Z ⊔ contB1 k G M ↔ φs (k' := k') 1 x ∈ Z' ⊔ contB1 k' G M
    constructor
    · intro hx
      obtain ⟨z, hz, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact Submodule.add_mem_sup ((hZ z).1 hz) ((contB1_iff hV b).1 hb)
    · intro hx
      obtain ⟨z', hz', b', hb', hzb⟩ := Submodule.mem_sup.1 hx
      have hz : (φs (k' :=
        k') 1).symm z' ∈ Z := (hZ _).2 (by rw [AddEquiv.apply_symm_apply]; exact hz')
      have hb : (φs (k' := k') 1).symm b' ∈ contB1 k G M :=
        (contB1_iff hV _).2 (by rw [AddEquiv.apply_symm_apply]; exact hb')
      have hx' : x = (φs (k' := k') 1).symm z' + (φs (k' := k') 1).symm b' := by
        apply (φs (k' := k') 1).injective
        rw [map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hzb]
      rw [hx']
      exact Submodule.add_mem_sup hz hb
  | n + 2, x => by
    change x ∈ (⊥ : Submodule k _) ↔ φs (k' := k') (n + 2) x ∈ (⊥ : Submodule k' _)
    rw [Submodule.mem_bot, Submodule.mem_bot, AddEquivClass.map_eq_zero_iff]

end Cocycle

section Kummer

variable {F : Type} [Field F] [CharZero F] [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic]
  {m : ℕ} [NeZero m]
  {k k' : Type} [CommRing k] [CommRing k'] {e : k ≃+* k'}
  {M : Type} [AddCommGroup M] [Module k M] [Module k' M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) k M]
  [SMulCommClass (Field.absoluteGaloisGroup F) k' M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  (hV : ∀ (r : k) (m : M), r • m = e r • m)
  (ι : TorsAlg F B m →+ M)

include hV in
theorem φs_kummer (a : k) (P : B.toAffine.Point) :
    φs (k' := k') 1 (kummerCocycleIn (k := k) ι a P) = kummerCocycleIn (k := k') ι (e a) P :=
  Subtype.ext (funext fun _ => hV a _)

include hV in
theorem φs_symm_kummer (a : k') (P : B.toAffine.Point) :
    (φs (k := k) (k' := k') 1).symm (kummerCocycleIn (k := k') ι a P) =
      kummerCocycleIn (k := k) ι (e.symm a) P := by
  apply (φs (k := k) (k' := k') 1).injective
  rw [AddEquiv.apply_symm_apply, φs_kummer hV, RingEquiv.apply_symm_apply]

omit [CharZero F] [DecidableEq F] in
include hV in
theorem φs_symm_smul (r : k') (y : contCochain k' (Field.absoluteGaloisGroup F) M 1) :
    (φs (k := k) (k' := k') 1).symm (r • y) = e.symm r • (φs (k := k) (k' := k') 1).symm y := by
  apply (φs (k := k) (k' := k') 1).injective
  rw [AddEquiv.apply_symm_apply, φs_smul hV, RingEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

include hV in
/-- **The extended Kummer submodule has the same members over `k` and over `k'`.**
Kind: PROVED. -/
theorem kummerZ'_iff (x : contCochain k (Field.absoluteGaloisGroup F) M 1) :
    x ∈ kummerZ' k ι ↔ φs (k' := k') 1 x ∈ kummerZ' k' ι := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨a, P⟩, rfl⟩ := hy
      rw [φs_kummer hV]
      exact Submodule.subset_span ⟨(e a, P), rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [φs_smul hV]
      exact Submodule.smul_mem _ _ hy
  · intro hx
    have key : ∀ y ∈ kummerZ' k' ι, (φs (k := k) (k' := k') 1).symm y ∈ kummerZ' k ι := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨⟨a, P⟩, rfl⟩ := hy
        rw [φs_symm_kummer hV]
        exact Submodule.subset_span ⟨(e.symm a, P), rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | smul r y _ hy =>
        rw [φs_symm_smul hV]
        exact Submodule.smul_mem _ _ hy
    simpa using key _ hx

end Kummer

/-! ### The Kummer and zero conditions -/

section Conditions

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace k'] [DiscreteTopology k']
  (M₀ : Type) [AddCommGroup M₀] [Module k M₀] [Module k' M₀] [DistribMulAction (GKS K S₀) M₀]
  [SMulCommClass (GKS K S₀) k M₀] [SMulCommClass (GKS K S₀) k' M₀] [TopologicalSpace M₀]
  [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  (hV : ∀ (r : k) (m : M₀), r • m = e r • m)

/-- **The Kummer condition over `k` against the same over `k'`** at a place `v ∈ S`, with
coefficients extended along the same `ι`. Kind: definition (PROVED fields). -/
def kummerAtCond (v : Places K S) [DecidableEq (v.1.adicCompletion K)]
    (B : WeierstrassCurve (v.1.adicCompletion K)) [B.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) (InflMod hS M₀))
    (hι : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι (σ • t) = σ • ι t) :
    CondSEquiv hS e M₀ hV v (kummerAt (k := k) v B m ι hι) (kummerAt (k := k') v B m ι hι) :=
  have hV' : ∀ (r : k) (m : ResMod (locMap K S v.1) (InflMod hS M₀)), r • m = e r • m :=
    fun r m => hV r m
  have hP := condP_iff (G := Gloc K v.1) (M := ResMod (locMap K S v.1) (InflMod hS M₀))
    hV' (kummerZ' k ι) (kummerZ' k' ι) (kummerZ'_iff hV' ι)
  ⟨subSEquiv e hV' (condSubCx (kummerZ' k ι) (kummerZ'_cocycle k ι hι))
      (condSubCx (kummerZ' k' ι) (kummerZ'_cocycle k' ι hι)) (fun n x => hP n x),
    subSEquiv_ι e hV' (condSubCx (kummerZ' k ι) (kummerZ'_cocycle k ι hι))
      (condSubCx (kummerZ' k' ι) (kummerZ'_cocycle k' ι hι)) (fun n x => hP n x)⟩

/-- **The zero condition over `k` against the same over `k'`.** Kind: definition (PROVED
fields). -/
def zeroAtCond (v : Places K S) :
    CondSEquiv hS e M₀ hV v (zeroAt K S k (InflMod hS M₀) v) (zeroAt K S k' (InflMod hS M₀) v) :=
  ⟨⟨fun _ => AddEquiv.refl PUnit, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩,
    fun i j h x => by
      change (inflLocalSEquiv hS e M₀ hV v).f j 0 = 0
      exact map_zero _⟩

end Conditions

end ZInQ.Contrib.CloudB3E1Torsion
