import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.Derivative
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Selmer

/-!
# Genuine instantiations, part 18: the derivative local conditions at the actual coefficient
modules `M_i`

Manuscript `diophantine_zq.tex`, the derivative conditions of Lemma `ex:limits-derivative-switch`
(tex 4835–4876: strict `D⁰ = τ_{≤0}`, relaxed `D⁰ ⊕ (F ⊕ S)[−1] = τ_{≤1}`) at the finite levels
`M_i = (E[2^i] ⊗ A_i)(α_i)` over `A_i = (ℤ/2^i)[t]/t^i` (tex 2724–2727; the other team's
`RC/CoefModules`).

For any coefficient ring `k` (not only `𝔽₂`) and any discrete `k[G]`-module `M`:

* `relaxedDK`, **`relaxedCxK`** `= [C⁰ → Z¹]`, **`strictCxK`** `= [Z⁰ → 0]`, and their inclusions
  `relaxedToLocalK`, `strictToLocalK` into the genuine `C^•_cont(G, M)` (as in `Derivative.lean`,
  which is the case `k = 𝔽₂`);
* **lengths**: `length H⁰(τ_{≤1}) + length H¹(τ_{≤1}) = length H⁰_cont(G, M) + length H¹_cont(G, M)`
  (`length_relaxedCxK`) and `length H⁰(τ_{≤0}) + length H¹(τ_{≤0}) = length H⁰_cont(G, M)`
  (`length_strictCxK`), through `contH0IsoK : H⁰_cont ≅ Z⁰`, `contH1IsoK : H¹_cont ≅ Z¹ / d C⁰`;
* at a place `v ∈ S` and the actual module (`MinS`, the other team's `M_i` over `G_{K,S}`):
  **`relaxedAt`, `strictAt`** — the derivative conditions as `CondAt` in the other team's format
  (a complex with a cochain map into the genuine local complex `locAt`), injective
  (`relaxedAt_isInjective`, `strictAt_isInjective`), so `ofCondAt` / `actualConditions` assemble
  them into genuine `GaloisLocalConditions` of `M_i`;
* `length_derivAt`: the table's derivative rows at any coefficient module, in lengths (the
  relaxed condition has the lengths of `H⁰ + H¹` of the genuine local cohomology, the strict one
  that of `H⁰`); `actualDerivConditions` (+ `_injective`): the actual local conditions of `M_i`
  with a derivative condition at the switch place.

The numerical values of the table (`2`, `4`, …) are for the residual module `W = 𝔽₂²`; at `M_i`
the lengths of the local cohomology are not computed here.

**Classification.** Definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open CategoryTheory Limits ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

section Deriv

variable (k : Type) [CommRing k]
  (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [SMulCommClass G k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- The `0`-cocycles `Z⁰ = ker d⁰`. -/
abbrev Z0K : Submodule k ((contCochains k G M).X 0) :=
  LinearMap.ker ((contCochains k G M).d 0 1).hom

/-- The `1`-cocycles `Z¹ = ker d¹`. -/
abbrev Z1K : Submodule k ((contCochains k G M).X 1) :=
  LinearMap.ker ((contCochains k G M).d 1 2).hom

/-- `d⁰ : C⁰ → Z¹`. -/
def relaxedDK : (contCochains k G M).X 0 →ₗ[k] Z1K k G M :=
  ((contCochains k G M).d 0 1).hom.codRestrict (Z1K k G M) fun x => LinearMap.mem_ker.mpr (by
    have h := congrArg (fun φ => ModuleCat.Hom.hom φ x) ((contCochains k G M).d_comp_d 0 1 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    exact h)

/-- **The relaxed derivative condition** `τ_{≤1} C^•_cont(G, M) = [C⁰ → Z¹]` over `k`. -/
abbrev relaxedCxK : CochainComplex (ModuleCat.{0} k) ℤ := dblCx (relaxedDK k G M)

/-- **The strict derivative condition** `τ_{≤0} C^•_cont(G, M) = [Z⁰ → 0]` over `k`. -/
abbrev strictCxK : CochainComplex (ModuleCat.{0} k) ℤ :=
  dblCx (0 : Z0K k G M →ₗ[k] PUnit.{1})

/-- The inclusion `τ_{≤1} C^• → C^•`. -/
def relaxedToLocalK : relaxedCxK k G M ⟶ (natCx (contCochains k G M)).toCC :=
  HomologicalComplex.mkHomFromDouble rel01 (by decide)
    (ModuleCat.ofHom (LinearMap.id : (contCochains k G M).X 0 →ₗ[k] _))
    (ModuleCat.ofHom (Z1K k G M).subtype)
    (by
      ext x
      exact (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC_d_hom
        (natCx (contCochains k G M)) 0 1 rfl x).trans rfl)
    (by
      intro j hj
      have hj' : j = 2 := by simp at hj; omega
      subst hj'
      ext x
      exact (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC_d_hom
        (natCx (contCochains k G M)) 1 2 rfl (x : (contCochains k G M).X 1)).trans x.2)

/-- The inclusion `τ_{≤0} C^• → C^•`. -/
def strictToLocalK : strictCxK k G M ⟶ (natCx (contCochains k G M)).toCC :=
  HomologicalComplex.mkHomFromDouble rel01 (by decide)
    (ModuleCat.ofHom (Z0K k G M).subtype) 0
    (by
      ext x
      exact (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC_d_hom
        (natCx (contCochains k G M)) 0 1 rfl (x : (contCochains k G M).X 0)).trans x.2)
    (fun _ _ => zero_comp)

/-- `H⁰_cont(G, M) ≅ Z⁰`. -/
def contH0IsoK : contCohomology k G M 0 ≅ ModuleCat.of k (Z0K k G M) :=
  ((contCochains k G M).isoHomologyπ 0 0 (by simp)
      ((contCochains k G M).shape 0 0 (by simp))).symm ≪≫
    (contCochains k G M).cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫
    ShortComplex.cyclesIsoKernel _ ≪≫ ModuleCat.kernelIsoKer _

/-- `H¹_cont(G, M) ≅ Z¹ / d⁰ C⁰`. -/
def contH1IsoK : contCohomology k G M 1 ≅
    ModuleCat.of k (Z1K k G M ⧸ LinearMap.range (relaxedDK k G M)) :=
  (contCochains k G M).homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    ((contCochains k G M).sc' 0 1 2).moduleCatLeftHomologyData.homologyIso

theorem length_eq_of_iso {A B : ModuleCat.{0} k} (e : A ≅ B) :
    Module.length k A = Module.length k B :=
  e.toLinearEquiv.length_eq

/-- **The lengths of the relaxed derivative condition**: `length H⁰_cont + length H¹_cont`. -/
theorem length_relaxedCxK :
    Module.length k ((relaxedCxK k G M).homology 0) +
        Module.length k ((relaxedCxK k G M).homology 1) =
      Module.length k (contCohomology k G M 0) + Module.length k (contCohomology k G M 1) := by
  rw [length_eq_of_iso k (dblH0Iso _), length_eq_of_iso k (dblH1Iso _),
    length_eq_of_iso k (contH0IsoK k G M), length_eq_of_iso k (contH1IsoK k G M)]
  congr 1
  exact (LinearEquiv.ofEq _ _ (LinearMap.ker_codRestrict _ _ _)).length_eq

/-- **The lengths of the strict derivative condition**: `length H⁰_cont`. -/
theorem length_strictCxK :
    Module.length k ((strictCxK k G M).homology 0) +
        Module.length k ((strictCxK k G M).homology 1) =
      Module.length k (contCohomology k G M 0) := by
  rw [length_eq_of_iso k (dblH0Iso _), length_eq_of_iso k (dblH1Iso _),
    length_eq_of_iso k (contH0IsoK k G M), LinearMap.ker_zero]
  have hs : Subsingleton (PUnit.{1} ⧸ LinearMap.range (0 : Z0K k G M →ₗ[k] PUnit.{1})) :=
    ⟨fun a b => Quotient.inductionOn₂' a b fun _ _ => rfl⟩
  rw [Module.length_eq_zero (M := ModuleCat.of k (PUnit.{1} ⧸ LinearMap.range
    (0 : Z0K k G M →ₗ[k] PUnit.{1}))), add_zero]
  exact (Submodule.topEquiv).length_eq

/-- A two-term complex map whose degree-`0` and degree-`1` components are injective is injective in
every degree. -/
theorem injective_mkHomFromDouble {A B : Type} [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (f : A →ₗ[k] B) {L : CochainComplex (ModuleCat.{0} k) ℤ}
    (φ₀ : ModuleCat.of k A ⟶ L.X 0) (φ₁ : ModuleCat.of k B ⟶ L.X 1)
    (comm : φ₀ ≫ L.d 0 1 = ModuleCat.ofHom f ≫ φ₁) (zero : ∀ j, (ComplexShape.up ℤ).Rel 1 j →
      φ₁ ≫ L.d 1 j = 0)
    (h₀ : Function.Injective φ₀.hom) (h₁ : Function.Injective φ₁.hom) (n : ℤ) :
    Function.Injective ((HomologicalComplex.mkHomFromDouble rel01 (by decide) φ₀ φ₁ comm zero
      : dblCx f ⟶ L).f n).hom := by
  by_cases n0 : n = 0
  · subst n0
    rw [HomologicalComplex.mkHomFromDouble_f₀, ModuleCat.hom_comp]
    exact h₀.comp ((ModuleCat.mono_iff_injective _).mp inferInstance)
  by_cases n1 : n = 1
  · subst n1
    rw [HomologicalComplex.mkHomFromDouble_f₁, ModuleCat.hom_comp]
    exact h₁.comp ((ModuleCat.mono_iff_injective _).mp inferInstance)
  · intro x y _
    have hz := HomologicalComplex.isZero_double_X (ModuleCat.ofHom f) rel01 n n0 n1
    have hx := congrArg (fun φ => ModuleCat.Hom.hom φ x) (hz.eq_of_src (𝟙 _) 0)
    have hy := congrArg (fun φ => ModuleCat.Hom.hom φ y) (hz.eq_of_src (𝟙 _) 0)
    simp only [ModuleCat.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at hx hy
    exact hx.trans hy.symm

end Deriv

/-! ### At a place, and at the actual coefficient modules -/

section Places

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.CoefModules

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

/-- **The relaxed derivative condition at `v ∈ S`** `τ_{≤1} C^•_cont(G_{K_v}, M) ⊆ C^•_cont`, in the
other team's `CondAt` format. -/
def relaxedAt (v : Places K S) : CondAt K S k M v :=
  ⟨ZInQ.Manuscript.RC.SelmerComplex.ofCC (relaxedCxK k (Gloc K v.1) (ResMod (locMap K S v.1) M)),
    ZInQ.Manuscript.RC.SelmerComplex.ofCCHom (relaxedToLocalK k _ _)⟩

/-- **The strict derivative condition at `v ∈ S`** `τ_{≤0} C^•_cont(G_{K_v}, M) ⊆ C^•_cont`. -/
def strictAt (v : Places K S) : CondAt K S k M v :=
  ⟨ZInQ.Manuscript.RC.SelmerComplex.ofCC (strictCxK k (Gloc K v.1) (ResMod (locMap K S v.1) M)),
    ZInQ.Manuscript.RC.SelmerComplex.ofCCHom (strictToLocalK k _ _)⟩

/-- The relaxed derivative condition is a subcomplex. PROVED. -/
theorem relaxedAt_isInjective (v : Places K S) : (relaxedAt K S k M v).IsInjective := fun n =>
  injective_mkHomFromDouble k _ _ _ _ _ (fun _ _ h => h) Subtype.val_injective n

/-- The strict derivative condition is a subcomplex. PROVED. -/
theorem strictAt_isInjective (v : Places K S) : (strictAt K S k M v).IsInjective := fun n =>
  injective_mkHomFromDouble k _ _ _ _ _ Subtype.val_injective
    (fun x y _ => Subsingleton.elim (α := PUnit) x y) n

/-- **The table's derivative rows at any coefficient module, in lengths** (tex 4561–4573 at the
module `M`): the relaxed condition has
`length H⁰ + length H¹ = length H⁰(K_v, M) + length H¹(K_v, M)`
and the strict one `length H⁰(K_v, M)`. PROVED. -/
theorem length_derivAt (v : Places K S) :
    (Module.length k ((relaxedCxK k (Gloc K v.1) (ResMod (locMap K S v.1) M)).homology 0) +
        Module.length k ((relaxedCxK k (Gloc K v.1) (ResMod (locMap K S v.1) M)).homology 1) =
      Module.length k (contCohomology k (Gloc K v.1) (ResMod (locMap K S v.1) M) 0) +
        Module.length k (contCohomology k (Gloc K v.1) (ResMod (locMap K S v.1) M) 1)) ∧
    (Module.length k ((strictCxK k (Gloc K v.1) (ResMod (locMap K S v.1) M)).homology 0) +
        Module.length k ((strictCxK k (Gloc K v.1) (ResMod (locMap K S v.1) M)).homology 1) =
      Module.length k (contCohomology k (Gloc K v.1) (ResMod (locMap K S v.1) M) 0)) :=
  ⟨length_relaxedCxK k _ _, length_strictCxK k _ _⟩

end Places

section Actual

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.CoefModules
  ZInQ.Manuscript.RC.HeegnerAlgebra

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S₀ →* (Acoef i)ˣ)
  [IsOpenKer α]

open Classical in
/-- **The actual local conditions with a derivative condition at the switch place `q`**: the
relaxed (or strict) derivative condition at `q ∈ S₀`, the given conditions at the other old places,
and the unramified conditions at `S − S₀` (the other team's `actualConditions`), at the actual
coefficient module `M_i`. -/
def actualDerivConditions (q : Places K S) (relaxed : Bool)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v) :
    GaloisLocalConditions K S (Acoef i) (MinS hS W i α) :=
  letI := acoefTop i
  haveI := acoefTop_discrete i
  actualConditions hS W i α fun v hv => if v = q then
      (if relaxed then relaxedAt K S (Acoef i) (MinS hS W i α) v
        else strictAt K S (Acoef i) (MinS hS W i α) v)
    else c v hv

open Classical in
/-- **The actual derivative conditions are subcomplexes** when the given old conditions are.
PROVED. -/
theorem actualDerivConditions_injective (q : Places K S) (relaxed : Bool)
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v h, (c v h).IsInjective) (v : Places K S) (n : ℤ) :
    letI := acoefTop i
    haveI := acoefTop_discrete i
    Function.Injective (((actualDerivConditions hS W i α q relaxed c).i v).f n n rfl) := by
  let := acoefTop i
  have := acoefTop_discrete i
  refine actualConditions_injective hS W i α _ (fun w h => ?_) v n
  by_cases hw : w = q
  · rw [if_pos hw]
    cases relaxed
    · exact strictAt_isInjective K S (Acoef i) (MinS hS W i α) w
    · exact relaxedAt_isInjective K S (Acoef i) (MinS hS W i α) w
  · rw [if_neg hw]
    exact hc w h

end Actual

end ZInQ.Contrib.CloudB3RC53.GenuineInst
