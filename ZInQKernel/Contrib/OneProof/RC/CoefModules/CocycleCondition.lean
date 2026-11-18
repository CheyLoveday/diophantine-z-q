import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Selmer

/-!
# Lane RC28: local conditions cut out by a submodule of continuous `1`-cocycles

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer` (tex 3413–3468): for the actual
local twist `B = E^{(h)}` over `F = K_v`, the condition `U_F = B(F)^∧_2[−1] → RΓ(F, T_2 B)`
"includes the finite two-primary torsion. Its reduction modulo `2^a` has `B(F)[2^a]` in degree
zero and `B(F)/2^a B(F)` in degree one" (tex 3415–3417, 3429–3431).

This file provides the generic finite-level shape of such a condition, inside the genuine
continuous cochains `C^•_cont(G, M)` of lane RC26 (`contCochains`). For a submodule
`Z ⊆ C¹_cont(G, M)` consisting of cocycles, the **cocycle condition** is the subcomplex

```text
U⁰ = C⁰_cont(G, M),     U¹ = Z ⊔ B¹_cont(G, M),     Uⁿ = 0   (n ≥ 2, and n < 0),
```

where `B¹_cont(G, M) = d⁰ C⁰_cont(G, M)` are the continuous coboundaries; the differential out of
degree one is zero because `Z` and `B¹` consist of cocycles. It is a relation-indexed complex
`cocycleCondition Z hZ : GCx k` (the format of the local conditions `LocalConditions` of
`SelmerComplex/Selmer.lean`) with the inclusion
`cocycleConditionι Z hZ : GHom (cocycleCondition Z hZ) (natCx (contCochains k G M))`, injective
in every degree (`cocycleConditionι_injective`).

Cohomology (Mathlib's homology of the `ℤ`-indexed complex `(cocycleCondition Z hZ).toCC`):
* `cocycleConditionH1Iso`: `H¹(U) ≅ U¹ ⧸ B¹ = (Z ⊔ B¹) ⧸ B¹`, where `U¹ = Z ⊔ B¹` definitionally
  (`cocycleCondition_X_one`) and `condB1 Z hZ` is `B¹` read inside `U¹` (`mem_condB1`);
  `cocycleCondition_mono_homologyMap_one`: `H¹(U) → H¹(C^•_cont(G, M))` is injective; on
  classes, `cocycleConditionH1Iso_inv_mk` and `cocycleCondition_homologyMap_inv_mk` (the class of
  `x ∈ U¹` is the homology class `π` of the cycle `x`, in `U` and in `C^•_cont(G, M)`);
* `cocycleCondition_isIso_homologyMap_zero`: the inclusion induces an isomorphism
  `H⁰(U) ≅ H⁰(C^•_cont(G, M))`; `cocycleConditionH0IsoInvariants`: `H⁰(U) ≅ M^G` (the invariants
  `invariantsSub k G M`); `cocycleConditionH0Iso`: `H⁰(U)` is the kernel of the degree-zero
  differential.

DEPARTURE (form): the text's condition is the derived object `B(F)^∧_2[−1]` and its derived
reduction modulo `2^a`; the finite-level object here is the explicit subcomplex above of genuine
continuous cochains, whose cohomology is the one prescribed by the text once `Z` is the Kummer
submodule (`Kummer.lean`). It maps injectively into the local cochains, as the downstream local
condition interface requires.

Kinds: all declarations are genuine definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.SelmerComplex

universe u

/-! ### Invariants -/

section Invariants

variable (k : Type u) [CommRing k] (G : Type u) [Group G]
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]

/-- Definition (tex 3415–3417, degree zero). The invariants `M^G = {m | ∀ g, g • m = m}`, a
`k`-submodule of `M`. -/
def invariantsSub : Submodule k M where
  carrier := {m | ∀ g : G, g • m = m}
  add_mem' ha hb g := by rw [smul_add, ha g, hb g]
  zero_mem' g := smul_zero g
  smul_mem' c m hm g := by rw [smul_comm, hm g]

variable {k G M}

/-- PROVED (tex 3415–3417). Membership in the invariants. -/
theorem mem_invariantsSub (m : M) : m ∈ invariantsSub k G M ↔ ∀ g : G, g • m = m :=
  Iff.rfl

end Invariants

/-! ### Differentials and coboundaries of the continuous cochains -/

section Differentials

variable (k : Type u) [CommRing k] (G : Type u) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- Definition (tex 3413–3468, ambient complex `RΓ(F, −)`). The differential
`dⁿ : Cⁿ_cont(G, M) → Cⁿ⁺¹_cont(G, M)` of the genuine continuous cochains `contCochains k G M`,
as a linear map between the submodules `contCochain k G M n`. -/
abbrev contD (n : ℕ) : contCochain k G M n →ₗ[k] contCochain k G M (n + 1) :=
  ((contCochains k G M).d n (n + 1)).hom

/-- Definition (tex 3413–3468). The continuous `1`-coboundaries
`B¹_cont(G, M) = d⁰ C⁰_cont(G, M) ⊆ C¹_cont(G, M)`. -/
def contB1 : Submodule k (contCochain k G M 1) :=
  LinearMap.range (contD k G M 0)

variable {k G M}

/-- PROVED (tex 3413–3468, complex structure of `RΓ(F, −)`). `dⁿ⁺¹ ∘ dⁿ = 0` on continuous
cochains. -/
theorem contD_contD (n : ℕ) (c : contCochain k G M n) :
    contD k G M (n + 1) (contD k G M n c) = 0 :=
  congrArg (fun f => f.hom c) ((contCochains k G M).d_comp_d n (n + 1) (n + 1 + 1))

/-- Definition (tex 3413–3468). A continuous `n`-cochain read as a function `Gⁿ → M`. -/
abbrev cfun {n : ℕ} (c : contCochain k G M n) : (Fin n → G) → M := asFun k G M c.1

/-- PROVED (tex 3413–3468). The degree-zero differential is `(d⁰ c)(g) = g • c() − c()`, where
`c()` is the value of the `0`-cochain `c` at the unique point of `G⁰`. -/
theorem contD_zero_apply (c : contCochain k G M 0) (g : Fin 1 → G) :
    cfun (contD k G M 0 c) g = g 0 • cfun c default - cfun c default := by
  have h := contCochains_d_apply (k := k) (G := G) (M := M) 0 c g
  refine h.trans ?_
  rw [Fin.sum_univ_one]
  have e1 : (fun i : Fin 0 => g i.succ) = default := Subsingleton.elim _ _
  have e2 : Fin.contractNth (0 : Fin 1) (· * ·) g = default := Subsingleton.elim _ _
  simp only [e1, e2, Fin.val_zero, zero_add, pow_one, neg_one_smul, sub_eq_add_neg]

/-- PROVED (tex 3413–3468). Membership in `B¹_cont(G, M)`. -/
theorem mem_contB1_iff (b : contCochain k G M 1) :
    b ∈ contB1 k G M ↔ ∃ c : contCochain k G M 0, contD k G M 0 c = b :=
  LinearMap.mem_range

/-- Definition (tex 3413–3468). The constant `0`-cochain with value `t`. -/
def constCochain (t : M) : contCochain k G M 0 :=
  ⟨(fun _ => t : (Fin 0 → G) → M), continuous_const⟩

omit [ContinuousMul G] [ContinuousSMul G M] in
/-- PROVED (tex 3413–3468). The value of a constant `0`-cochain. -/
@[simp]
theorem cfun_constCochain (t : M) (x : Fin 0 → G) : cfun (constCochain (G := G) (k := k) t) x = t :=
  rfl

/-- PROVED (tex 3413–3468). The coboundary of the constant `0`-cochain `t` is `g ↦ g • t − t`. -/
theorem cfun_contD_constCochain (t : M) (g : Fin 1 → G) :
    cfun (contD k G M 0 (constCochain t)) g = g 0 • t - t :=
  contD_zero_apply _ g

omit [ContinuousMul G] [ContinuousSMul G M] in
/-- PROVED (tex 3413–3468). Every continuous `0`-cochain is constant (`G⁰` is a point). -/
theorem eq_constCochain (c : contCochain k G M 0) : c = constCochain (cfun c default) := by
  apply Subtype.ext
  funext x
  exact congrArg (cfun c) (Subsingleton.elim x default)

/-- PROVED (tex 3415–3417, degree zero). A continuous `0`-cochain is a cocycle iff its value is
`G`-invariant: `d⁰ c = 0 ↔ ∀ g, g • c() = c()`. -/
theorem contD_zero_eq_zero_iff (c : contCochain k G M 0) :
    contD k G M 0 c = 0 ↔ ∀ g : G, g • cfun c default = cfun c default := by
  constructor
  · intro h g
    have h1 := (contD_zero_apply c (fun _ => g)).symm.trans
      (congrArg (fun f : contCochain k G M 1 => cfun f (fun _ => g)) h)
    exact sub_eq_zero.1 h1
  · intro h
    apply Subtype.ext
    funext g
    refine (contD_zero_apply c g).trans ?_
    rw [h (g 0), sub_self]
    rfl

end Differentials

/-! ### The cocycle condition -/

section Condition

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- Definition (tex 3415–3417, 3429–3431: the finite-level condition, degrees zero and one). The
terms of the cocycle condition attached to `Z ⊆ C¹_cont(G, M)`: all continuous `0`-cochains in
degree zero, `Z ⊔ B¹_cont(G, M)` in degree one, `0` in degrees `≥ 2`. -/
def condP (Z : Submodule k (contCochain k G M 1)) :
    ∀ n : ℕ, Submodule k (contCochain k G M n)
  | 0 => ⊤
  | 1 => Z ⊔ contB1 k G M
  | _ + 2 => ⊥

/-- PROVED (tex 3413–3468). The terms of the cocycle condition are stable under the differential,
when `Z` consists of cocycles: `d⁰(C⁰) = B¹ ⊆ Z ⊔ B¹`, `d¹(Z ⊔ B¹) = 0`. -/
theorem condP_d_mem (Z : Submodule k (contCochain k G M 1))
    (hZ : ∀ z ∈ Z, contD k G M 1 z = 0) :
    ∀ (n : ℕ) (x : contCochain k G M n), x ∈ condP Z n → contD k G M n x ∈ condP Z (n + 1)
  | 0, x, _ => Submodule.mem_sup_right (LinearMap.mem_range.2 ⟨x, rfl⟩)
  | 1, x, hx => by
      obtain ⟨z, hz, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.1 hb
      have h : contD k G M 1 (z + contD k G M 0 c) = 0 := by
        rw [map_add, hZ z hz, contD_contD 0 c, add_zero]
      exact h ▸ zero_mem _
  | n + 2, x, hx => by
      have hx0 : x = 0 := (Submodule.mem_bot k).1 hx
      subst hx0
      rw [map_zero]
      exact zero_mem _

/-- Definition (tex 3413–3468). The cocycle condition as a subcomplex (`SubCx`) of the genuine
continuous cochains `C^•_cont(G, M)`. -/
def condSubCx (Z : Submodule k (contCochain k G M 1)) (hZ : ∀ z ∈ Z, contD k G M 1 z = 0) :
    SubCx (contCochains k G M) where
  P := condP Z
  d_mem := condP_d_mem Z hZ

/-- Definition (tex 3413–3468; DEPARTURE of form, see the module docstring). **The cocycle
condition** `U = [C⁰_cont(G, M) --d⁰--> Z ⊔ B¹_cont(G, M)]` (degrees `0, 1`, zero elsewhere), as a
relation-indexed complex `GCx k` — the format of the local condition complexes `U_v` of
`LocalConditions`. -/
def cocycleCondition (Z : Submodule k (contCochain k G M 1))
    (hZ : ∀ z ∈ Z, contD k G M 1 z = 0) : GCx k :=
  natCx (condSubCx Z hZ).toCx

/-- Definition (tex 3413–3468, the local map `U_F → RΓ(F, −)`). The inclusion of the cocycle
condition into the genuine local complex `natCx (contCochains k G M)`, a chain map `GHom`. -/
def cocycleConditionι (Z : Submodule k (contCochain k G M 1))
    (hZ : ∀ z ∈ Z, contD k G M 1 z = 0) :
    GHom (cocycleCondition Z hZ) (natCx (contCochains k G M)) :=
  natHom (condSubCx Z hZ).ι

/-- PROVED (tex 3413–3468). **The inclusion of the cocycle condition is injective in every
degree.** -/
theorem cocycleConditionι_injective (Z : Submodule k (contCochain k G M 1))
    (hZ : ∀ z ∈ Z, contD k G M 1 z = 0) :
    ∀ i : ℤ, Function.Injective ((cocycleConditionι Z hZ).f i i rfl)
  | Int.ofNat n => SubCx.ι_f_injective _ n
  | Int.negSucc _ => fun _ _ _ => rfl

/-- PROVED (tex 3413–3468). The inclusion of the cocycle condition is a monomorphism of Mathlib
cochain complexes in every degree. -/
theorem cocycleConditionι_mono (Z : Submodule k (contCochain k G M 1))
    (hZ : ∀ z ∈ Z, contD k G M 1 z = 0) (i : ℤ) :
    Mono ((GHom.toCC (cocycleConditionι Z hZ)).f i) :=
  (ModuleCat.mono_iff_injective _).2 (cocycleConditionι_injective Z hZ i)

/-- Definition (tex 3417–3418: the span of the Kummer cocycles). The `k`-span of a set of
continuous `1`-cochains, a submodule of `C¹_cont(G, M)`. (Stated in the generic setting, so that
for `k = ℤ` its module structure is literally the one `cocycleCondition` uses.) -/
abbrev cochainSpan (s : Set (contCochain k G M 1)) : Submodule k (contCochain k G M 1) :=
  Submodule.span k s

/-- PROVED (tex 3417–3418). The span of a set of cocycles consists of cocycles. -/
theorem cochainSpan_cocycle (s : Set (contCochain k G M 1)) (hs : ∀ c ∈ s, contD k G M 1 c = 0) :
    ∀ z ∈ cochainSpan s, contD k G M 1 z = 0 := by
  intro z hz
  have hle : cochainSpan s ≤ LinearMap.ker (contD k G M 1) :=
    Submodule.span_le.2 fun c hc => hs c hc
  exact hle hz

variable (Z : Submodule k (contCochain k G M 1)) (hZ : ∀ z ∈ Z, contD k G M 1 z = 0)

/-- PROVED (tex 3415–3417). The degree-zero term of the cocycle condition is all of
`C⁰_cont(G, M)`. -/
theorem cocycleCondition_X_zero :
    (cocycleCondition Z hZ).X 0 = ModuleCat.of k ↥(⊤ : Submodule k (contCochain k G M 0)) :=
  rfl

/-- PROVED (tex 3415–3417). The degree-one term of the cocycle condition is `Z ⊔ B¹_cont(G, M)`. -/
theorem cocycleCondition_X_one :
    (cocycleCondition Z hZ).X 1 = ModuleCat.of k ↥(Z ⊔ contB1 k G M) :=
  rfl

/-- PROVED (tex 3415–3417). The degree-two term of the cocycle condition is zero. -/
theorem cocycleCondition_X_two :
    (cocycleCondition Z hZ).X 2 = ModuleCat.of k ↥(⊥ : Submodule k (contCochain k G M 2)) :=
  rfl

/-- Definition (tex 3413–3468). Read an element of `U¹` as an element of `Z ⊔ B¹_cont(G, M)`
(the identity map; `cocycleCondition_X_one`). -/
def condOne (x : (cocycleCondition Z hZ).X 1) : ↥(Z ⊔ contB1 k G M) := x

/-- Definition (tex 3413–3468). Read an element of `Z ⊔ B¹_cont(G, M)` as an element of `U¹`
(the identity map). -/
def ofCondOne (x : ↥(Z ⊔ contB1 k G M)) : (cocycleCondition Z hZ).X 1 := x

/-- Definition (tex 3413–3468). Read an element of `U⁰` as an element of `⊤ ⊆ C⁰_cont(G, M)`
(the identity map; `cocycleCondition_X_zero`). -/
def condZero (x : (cocycleCondition Z hZ).X 0) : ↥(⊤ : Submodule k (contCochain k G M 0)) := x

/-- Definition (tex 3413–3468). Read a continuous `0`-cochain as an element of `U⁰`. -/
def ofCondZero (c : contCochain k G M 0) : (cocycleCondition Z hZ).X 0 :=
  (⟨c, trivial⟩ : ↥(⊤ : Submodule k (contCochain k G M 0)))

/-- PROVED (tex 3413–3468). `condOne` and `ofCondOne` are inverse. -/
@[simp]
theorem condOne_ofCondOne (x : ↥(Z ⊔ contB1 k G M)) : condOne Z hZ (ofCondOne Z hZ x) = x :=
  rfl

/-- PROVED (tex 3413–3468). `condZero` of `ofCondZero c` is `c`. -/
@[simp]
theorem condZero_ofCondZero (c : contCochain k G M 0) :
    (condZero Z hZ (ofCondZero Z hZ c) : contCochain k G M 0) = c :=
  rfl

/-- PROVED (tex 3413–3468). The degree-zero differential of the cocycle condition is the
differential `d⁰` of the continuous cochains. -/
theorem cocycleCondition_d₀ (x : (cocycleCondition Z hZ).X 0) :
    ((condOne Z hZ ((cocycleCondition Z hZ).d 0 1 rfl x) : contCochain k G M 1)) =
      contD k G M 0 (condZero Z hZ x : contCochain k G M 0) :=
  SubCx.toCx_d_apply (condSubCx Z hZ) 0 x

/-- PROVED (tex 3413–3468). The differential of the cocycle condition out of degree one is
zero. -/
theorem cocycleCondition_d₁ (x : (cocycleCondition Z hZ).X 1) :
    (cocycleCondition Z hZ).d 1 2 rfl x = 0 :=
  Subtype.ext ((Submodule.mem_bot k).1 ((cocycleCondition Z hZ).d 1 2 rfl x).2)

/-- PROVED (tex 3413–3468). The inclusion of the cocycle condition in degree one is the inclusion
`Z ⊔ B¹ ⊆ C¹_cont(G, M)`. -/
theorem cocycleConditionι_f_one (x : (cocycleCondition Z hZ).X 1) :
    (cocycleConditionι Z hZ).f 1 1 rfl x = (condOne Z hZ x : contCochain k G M 1) :=
  rfl

/-- PROVED (tex 3413–3468). The inclusion of the cocycle condition in degree zero is the identity
of `C⁰_cont(G, M)`. -/
theorem cocycleConditionι_f_zero (x : (cocycleCondition Z hZ).X 0) :
    (cocycleConditionι Z hZ).f 0 0 rfl x = (condZero Z hZ x : contCochain k G M 0) :=
  rfl

/-- PROVED (tex 3413–3468). The degree-one differential of `(cocycleCondition Z hZ).toCC` is
zero. -/
theorem cocycleCondition_toCC_d₁ (x : (cocycleCondition Z hZ).toCC.X 1) :
    ((cocycleCondition Z hZ).toCC.d 1 2).hom x = 0 :=
  (GCx.toCC_d_hom (cocycleCondition Z hZ) 1 2 rfl x).trans (cocycleCondition_d₁ Z hZ x)

/-- PROVED (tex 3413–3468). The degree-zero differential of `(cocycleCondition Z hZ).toCC` is
`d⁰`. -/
theorem cocycleCondition_toCC_d₀ (x : (cocycleCondition Z hZ).toCC.X 0) :
    ((condOne Z hZ (((cocycleCondition Z hZ).toCC.d 0 1).hom x) : contCochain k G M 1)) =
      contD k G M 0 (condZero Z hZ x : contCochain k G M 0) :=
  (congrArg (fun y => ((condOne Z hZ y : ↥(Z ⊔ contB1 k G M)) : contCochain k G M 1))
    (GCx.toCC_d_hom (cocycleCondition Z hZ) 0 1 rfl x)).trans (cocycleCondition_d₀ Z hZ x)

/-- PROVED (tex 3415–3417, degree zero). An element of `U⁰` is a `0`-cocycle of the cocycle
condition iff it is a `0`-cocycle of `C^•_cont(G, M)`. -/
theorem cocycleCondition_toCC_d₀_eq_zero_iff (x : (cocycleCondition Z hZ).toCC.X 0) :
    ((cocycleCondition Z hZ).toCC.d 0 1).hom x = 0 ↔
      contD k G M 0 (condZero Z hZ x : contCochain k G M 0) = 0 := by
  rw [← cocycleCondition_toCC_d₀]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

/-- Definition (tex 3415–3417, degree one). The submodule `B¹_cont(G, M)` read inside
`U¹ = Z ⊔ B¹_cont(G, M)`. -/
def condB1 : Submodule k ((cocycleCondition Z hZ).X 1) :=
  (contB1 k G M).comap (Z ⊔ contB1 k G M).subtype

/-- PROVED (tex 3415–3417). Membership in `condB1`. -/
theorem mem_condB1 (x : (cocycleCondition Z hZ).X 1) :
    x ∈ condB1 Z hZ ↔ (condOne Z hZ x : contCochain k G M 1) ∈ contB1 k G M :=
  Iff.rfl

/-- PROVED (tex 3413–3468). Every element of `U¹` is a `1`-cocycle of the cocycle condition. -/
theorem cocycleCondition_ker_d₁ :
    LinearMap.ker ((cocycleCondition Z hZ).toCC.sc' 0 1 2).g.hom = ⊤ :=
  LinearMap.ker_eq_top.2 (LinearMap.ext fun x => cocycleCondition_toCC_d₁ Z hZ x)

/-- PROVED (tex 3415–3417). The `1`-coboundaries of the cocycle condition are exactly
`B¹_cont(G, M)` (inside `U¹`). -/
theorem cocycleCondition_range_d₀ :
    (LinearMap.range ((cocycleCondition Z hZ).toCC.sc' 0 1 2).moduleCatToCycles).map
        (LinearEquiv.ofTop _ (cocycleCondition_ker_d₁ Z hZ)).toLinearMap =
      condB1 Z hZ := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨condZero Z hZ x, (cocycleCondition_toCC_d₀ Z hZ x).symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨((cocycleCondition Z hZ).toCC.sc' 0 1 2).moduleCatToCycles (ofCondZero Z hZ c),
      ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (cocycleCondition_toCC_d₀ Z hZ _).trans hc

/-- PROVED (tex 3415–3417, degree one: "`B(F)/2^aB(F)` in degree one" for the Kummer submodule).
**The first cohomology of the cocycle condition is `(Z ⊔ B¹) ⧸ B¹`**: Mathlib's homology
`H¹((cocycleCondition Z hZ).toCC)` is isomorphic to `U¹ ⧸ B¹`, where `U¹ = Z ⊔ B¹_cont(G, M)`
(`cocycleCondition_X_one`) and `condB1 Z hZ` is `B¹_cont(G, M)` inside it. -/
def cocycleConditionH1Iso :
    (cocycleCondition Z hZ).toCC.homology 1 ≅
      ModuleCat.of k ((cocycleCondition Z hZ).X 1 ⧸ condB1 Z hZ) :=
  (cocycleCondition Z hZ).toCC.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    ((cocycleCondition Z hZ).toCC.sc' 0 1 2).moduleCatHomologyIso ≪≫
    (Submodule.Quotient.equiv
      (LinearMap.range ((cocycleCondition Z hZ).toCC.sc' 0 1 2).moduleCatToCycles) (condB1 Z hZ)
      (LinearEquiv.ofTop _ (cocycleCondition_ker_d₁ Z hZ))
      (cocycleCondition_range_d₀ Z hZ)).toModuleIso

/-- PROVED (tex 3413–3468). Nothing comes into degree zero of the cocycle condition. -/
theorem cocycleCondition_range_dneg :
    LinearMap.range ((cocycleCondition Z hZ).toCC.sc' (-1) 0 1).moduleCatToCycles = ⊥ := by
  rw [LinearMap.range_eq_bot]
  ext x
  have hx : x = 0 := rfl
  rw [hx, map_zero, LinearMap.zero_apply]

/-- PROVED (tex 3415–3417, degree zero). **The zeroth cohomology of the cocycle condition** is the
kernel of its degree-zero differential (the `0`-cocycles of `C^•_cont(G, M)`). -/
def cocycleConditionH0Iso :
    (cocycleCondition Z hZ).toCC.homology 0 ≅
      ModuleCat.of k ↥(LinearMap.ker ((cocycleCondition Z hZ).toCC.sc' (-1) 0 1).g.hom) :=
  (cocycleCondition Z hZ).toCC.homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    ((cocycleCondition Z hZ).toCC.sc' (-1) 0 1).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEqBot _ (cocycleCondition_range_dneg Z hZ)).toModuleIso

/-- Definition (tex 3415–3417, degree zero). The `0`-cocycles of the cocycle condition are the
invariants `M^G` (value at the point of `G⁰`; inverse: constant cochains). -/
def cocycleConditionZ0Equiv :
    ↥(LinearMap.ker ((cocycleCondition Z hZ).toCC.sc' (-1) 0 1).g.hom) ≃ₗ[k]
      ↥(invariantsSub k G M) where
  toFun x := ⟨cfun (condZero Z hZ x.1 : contCochain k G M 0) default,
    (contD_zero_eq_zero_iff _).1
      ((cocycleCondition_toCC_d₀_eq_zero_iff Z hZ x.1).1 (LinearMap.mem_ker.1 x.2))⟩
  invFun m := ⟨ofCondZero Z hZ (constCochain m.1), by
    change ((cocycleCondition Z hZ).toCC.d 0 1).hom (ofCondZero Z hZ (constCochain m.1)) = 0
    exact (cocycleCondition_toCC_d₀_eq_zero_iff Z hZ _).2
      ((contD_zero_eq_zero_iff _).2 (fun g => m.2 g))⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := by
    apply Subtype.ext
    change ofCondZero Z hZ (constCochain (cfun (condZero Z hZ x.1 : contCochain k G M 0)
      default)) = x.1
    rw [← eq_constCochain]
    rfl
  right_inv m := rfl

/-- PROVED (tex 3415–3417, degree zero: "the invariants"). **`H⁰` of the cocycle condition is the
invariants `M^G`.** -/
def cocycleConditionH0IsoInvariants :
    (cocycleCondition Z hZ).toCC.homology 0 ≅ ModuleCat.of k ↥(invariantsSub k G M) :=
  cocycleConditionH0Iso Z hZ ≪≫ (cocycleConditionZ0Equiv Z hZ).toModuleIso

/-- PROVED (tex 3415–3417, degree zero). **The inclusion of the cocycle condition induces an
isomorphism on `H⁰`**: `H⁰(U) ≅ H⁰(C^•_cont(G, M))` (both are the `0`-cocycles, i.e. the
invariants `M^G`). -/
theorem cocycleCondition_isIso_homologyMap_zero :
    IsIso (HomologicalComplex.homologyMap (GHom.toCC (cocycleConditionι Z hZ)) 0) := by
  have h1 : Epi ((GHom.toCC (cocycleConditionι Z hZ)).f ((ComplexShape.up ℤ).prev 0)) := by
    rw [CochainComplex.prev]
    change Epi ((GHom.toCC (cocycleConditionι Z hZ)).f (Int.negSucc 0))
    rw [ModuleCat.epi_iff_surjective]
    intro y
    exact ⟨0, rfl⟩
  have h2 : IsIso ((GHom.toCC (cocycleConditionι Z hZ)).f 0) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨cocycleConditionι_injective Z hZ 0, fun y => ?_⟩
    exact ⟨ofCondZero Z hZ y, rfl⟩
  have h3 : Mono ((GHom.toCC (cocycleConditionι Z hZ)).f ((ComplexShape.up ℤ).next 0)) := by
    rw [CochainComplex.next]
    exact cocycleConditionι_mono Z hZ (0 + 1)
  exact CategoryTheory.ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _ h1 h2 h3

/-- PROVED (tex 3417–3418). On the short complexes `U⁰ → U¹ → U²` and `C⁰ → C¹ → C²` the
inclusion is injective on `opcycles` (`U¹ ⧸ d⁰U⁰ → C¹ ⧸ d⁰C⁰`): a `1`-cochain of `U` that is a
coboundary in `C^•_cont(G, M)` is already a coboundary in `U`, because `U⁰ = C⁰`. -/
theorem cocycleCondition_mono_opcyclesMap_one :
    Mono (ShortComplex.opcyclesMap ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k)
      (ComplexShape.up ℤ) 0 1 2).map (GHom.toCC (cocycleConditionι Z hZ)))) := by
  set ψ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (ComplexShape.up ℤ) 0 1 2).map
    (GHom.toCC (cocycleConditionι Z hZ)) with hψ
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((cocycleCondition Z hZ).toCC.sc' 0 1 2).pOpcycles) x
  have h1 : (ShortComplex.opcyclesMap ψ).hom
      (((cocycleCondition Z hZ).toCC.sc' 0 1 2).pOpcycles.hom y) =
        ((natCx (contCochains k G M)).toCC.sc' 0 1 2).pOpcycles.hom (ψ.τ₂.hom y) :=
    congrArg (fun f => f.hom y) (ShortComplex.p_opcyclesMap ψ)
  rw [h1] at hx
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_pOpcycles_eq_zero_iff _ _).1 hx
  refine (ShortComplex.moduleCat_pOpcycles_eq_zero_iff _ _).2 ⟨ofCondZero Z hZ c, ?_⟩
  apply cocycleConditionι_injective Z hZ 1
  have h2 := congrArg (fun f => f.hom (ofCondZero Z hZ c)) ψ.comm₁₂
  exact h2.trans hc

/-- PROVED (tex 3417–3418: "Its Kummer image", the first cohomology of the condition as a subgroup
of the local cohomology). **The inclusion of the cocycle condition is injective on `H¹`**:
`H¹(U) → H¹(C^•_cont(G, M))` is a monomorphism (Mathlib homology of the `ℤ`-indexed complexes). -/
theorem cocycleCondition_mono_homologyMap_one :
    Mono (HomologicalComplex.homologyMap (GHom.toCC (cocycleConditionι Z hZ)) 1) := by
  set e := HomologicalComplex.homologyFunctorIso' (ModuleCat.{u} k) (ComplexShape.up ℤ) 0 1 2
    (by simp) (by simp)
  have hnat := e.hom.naturality (GHom.toCC (cocycleConditionι Z hZ))
  simp only [Functor.comp_map, ShortComplex.homologyFunctor_map,
    HomologicalComplex.homologyFunctor_map] at hnat
  have hm : Mono (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor'
      (ModuleCat.{u} k) (ComplexShape.up ℤ) 0 1 2).map (GHom.toCC (cocycleConditionι Z hZ)))) :=
    ShortComplex.mono_homologyMap_of_mono_opcyclesMap' _
      (cocycleCondition_mono_opcyclesMap_one Z hZ)
  have he : Mono (e.hom.app (cocycleCondition Z hZ).toCC) :=
    @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom (e.app (cocycleCondition Z hZ).toCC))
  have h3 : Mono (e.hom.app (cocycleCondition Z hZ).toCC ≫
      ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k)
        (ComplexShape.up ℤ) 0 1 2).map (GHom.toCC (cocycleConditionι Z hZ)))) :=
    @mono_comp _ _ _ _ _ _ he _ hm
  exact @mono_of_mono_fac _ _ _ _ _ _ _ _ h3 hnat

/-- PROVED (tex 3415–3417). **Classes in `H¹(U)`**: the inverse of `cocycleConditionH1Iso` sends
the class of `x ∈ U¹` to the homology class `π(c)` of the `1`-cycle `c` of `U` with underlying
cochain `x`. -/
theorem cocycleConditionH1Iso_inv_mk (x : (cocycleCondition Z hZ).X 1) :
    ∃ c : (cocycleCondition Z hZ).toCC.cycles 1,
      ((cocycleCondition Z hZ).toCC.iCycles 1).hom c = x ∧
      (cocycleConditionH1Iso Z hZ).inv.hom (Submodule.Quotient.mk x) =
        ((cocycleCondition Z hZ).toCC.homologyπ 1).hom c := by
  set S := (cocycleCondition Z hZ).toCC.sc' 0 1 2 with hS
  have hx : x ∈ LinearMap.ker S.g.hom := by
    rw [cocycleCondition_ker_d₁]
    trivial
  let y : ↥(LinearMap.ker S.g.hom) := ⟨x, hx⟩
  refine ⟨((cocycleCondition Z hZ).toCC.cyclesIsoSc' 0 1 2 (by simp) (by simp)).inv.hom
    (S.moduleCatCyclesIso.inv.hom y), ?_, ?_⟩
  · have h1 := congrArg (fun f => f.hom (S.moduleCatCyclesIso.inv.hom y))
      ((cocycleCondition Z hZ).toCC.cyclesIsoSc'_inv_iCycles 0 1 2 (by simp) (by simp))
    refine h1.trans ?_
    exact S.moduleCatCyclesIso_inv_iCycles_apply y
  · have h2 := congrArg (fun f => f.hom (S.moduleCatCyclesIso.inv.hom y))
      ((cocycleCondition Z hZ).toCC.π_homologyIsoSc'_inv 0 1 2 (by simp) (by simp))
    refine Eq.trans ?_ h2
    have h3 := S.moduleCatCyclesIso_inv_π_apply y
    have h4 := congrArg (fun z => ((cocycleCondition Z hZ).toCC.homologyIsoSc' 0 1 2
      (by simp) (by simp)).inv.hom z) h3
    refine Eq.trans ?_ h4.symm
    rfl

/-- PROVED (tex 3417–3418). **The map `H¹(U) → H¹(C^•_cont(G, M))` on classes**: the class of
`x ∈ U¹` goes to the homology class `π(c)` of the `1`-cycle `c` of the genuine local complex with
underlying cochain `x`. -/
theorem cocycleCondition_homologyMap_inv_mk (x : (cocycleCondition Z hZ).X 1) :
    ∃ c : (natCx (contCochains k G M)).toCC.cycles 1,
      ((natCx (contCochains k G M)).toCC.iCycles 1).hom c =
        (condOne Z hZ x : contCochain k G M 1) ∧
      (HomologicalComplex.homologyMap (GHom.toCC (cocycleConditionι Z hZ)) 1).hom
          ((cocycleConditionH1Iso Z hZ).inv.hom (Submodule.Quotient.mk x)) =
        ((natCx (contCochains k G M)).toCC.homologyπ 1).hom c := by
  obtain ⟨c, hc1, hc2⟩ := cocycleConditionH1Iso_inv_mk Z hZ x
  refine ⟨(HomologicalComplex.cyclesMap (GHom.toCC (cocycleConditionι Z hZ)) 1).hom c, ?_, ?_⟩
  · have h1 := congrArg (fun f => f.hom c)
      (HomologicalComplex.cyclesMap_i (GHom.toCC (cocycleConditionι Z hZ)) 1)
    refine h1.trans ?_
    change (cocycleConditionι Z hZ).f 1 1 rfl (((cocycleCondition Z hZ).toCC.iCycles 1).hom c) = _
    rw [hc1]
    rfl
  · rw [hc2]
    exact congrArg (fun f => f.hom c)
      (HomologicalComplex.homologyπ_naturality (GHom.toCC (cocycleConditionι Z hZ)) 1)

end Condition

end ZInQ.Manuscript.RC.CoefModules
