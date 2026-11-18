import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.LocalSum

/-!
# Genuine instantiations, part 8: the derivative local conditions as genuine local conditions;
non-vacuity of `hL_of_genuineModel`

Manuscript `diophantine_zq.tex`, tex 4561–4573 (the derivative rows of the table: strict `D⁰`,
finite or singular `D⁰ ⊕ F[−1]`, `D⁰ ⊕ S[−1]`, relaxed `D⁰ ⊕ (F ⊕ S)[−1]`, which "does not include
`D²`") at an inert derivative prime (odd, `W` trivial).

* `dblCx f = [A --f--> B]` with `dblH0Iso : H⁰ ≅ ker f`, `dblH1Iso : H¹ ≅ B ⧸ f A` (as for the
  unramified complex);
* **genuine derivative conditions**, as Mathlib cochain complexes with cochain maps into the other
  team's genuine local complex `(natCx C^•_cont(G, M)).toCC` (so `localConditionsOfCC` turns them
  into genuine Galois local conditions):
  - strict `D⁰ = τ_{≤0} C^•_cont = [Z⁰ → 0]` (`strictCx`, `strictToLocal`);
  - relaxed `D⁰ ⊕ (F ⊕ S)[−1] = τ_{≤1} C^•_cont = [C⁰ → Z¹]` (`relaxedCx`, `relaxedToLocal`);
  - finite (and, with the same dimension, singular) `D⁰ ⊕ F[−1]`: the unramified complex
    `[W --(Φ−1)--> W]` via the other team's `urToLocal_galois` (`F = H¹_ur`, `D⁰ = W^{G_w}`);
* their dimensions from the genuine cohomology: `finrank_strictCx` (`h⁰`), `finrank_relaxedCx`
  (`h⁰ + h¹`), through `kerToH0`, `kerToH1` (`z0EquivH0`, `z1QuotEquivH1`) and `contH0/1AddEquiv`;
* `genCondDim2`, **`genCondDim2_eq`**: every row of the table except the old-Kummer one (Mattuck,
  the input `kd`) is computed from genuine objects and equals RC6's `condDimAt` — the named input
  `hD` is removed; `hL_of_genuineModel2` (RC6's `hL` with no `hD`);
* **non-vacuity** (LESSON 2): `hL_of_genuineModel_nonvacuous`, `hL_of_genuineModel2_nonvacuous` —
  the minimal model built from the genuine dimensions (`rankModel`) meets both rank bounds with
  equality.

The switching lane's `LocalJ` (the action `J` on `F`, `−J` on `S` at the inert derivative prime) is
not needed for the dimensions: the planes `F`, `S` enter only through `dim F = dim S = h¹_ur`.

**Classification.** PROVED (the old-Kummer dimension is the Mattuck input).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open CategoryTheory Limits ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

section Double

variable {k : Type} [Ring k] {A B : Type} [AddCommGroup A] [Module k A] [AddCommGroup B]
  [Module k B] (f : A →ₗ[k] B)

/-- The two-term complex `[A --f--> B]` in degrees `0`, `1`. -/
def dblCx : CochainComplex (ModuleCat.{0} k) ℤ :=
  HomologicalComplex.double (ModuleCat.ofHom f) rel01

/-- The differential `d⁰¹` is `f` up to the structural isomorphisms. -/
theorem dblCx_d01 : (dblCx f).d 0 1 =
    (HomologicalComplex.doubleXIso₀ _ rel01).hom ≫ ModuleCat.ofHom f ≫
      (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).inv :=
  HomologicalComplex.double_d _ _ _

/-- The differential into degree `0` vanishes. -/
theorem dblCx_d_prev : (dblCx f).d (-1) 0 = 0 :=
  HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide)

/-- The differential out of degree `1` vanishes. -/
theorem dblCx_d_next : (dblCx f).d 1 2 = 0 :=
  HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide)

/-- The kernel of the differential `d⁰¹` is the kernel of `f`. -/
def dblKerIso : kernel ((dblCx f).d 0 1) ≅ kernel (ModuleCat.ofHom f) :=
  kernelIsoOfEq (dblCx_d01 f) ≪≫
    kernelIsIsoComp (HomologicalComplex.doubleXIso₀ _ rel01).hom
      (ModuleCat.ofHom f ≫ (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).inv) ≪≫
    kernelCompMono (ModuleCat.ofHom f)
      (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).inv

/-- The cokernel of the differential `d⁰¹` is the cokernel of `f`. -/
def dblCokerIso : cokernel ((dblCx f).d 0 1) ≅ cokernel (ModuleCat.ofHom f) :=
  cokernelIsoOfEq ((dblCx_d01 f).trans (Category.assoc _ _ _).symm) ≪≫
    cokernelCompIsIso ((HomologicalComplex.doubleXIso₀ _ rel01).hom ≫ ModuleCat.ofHom f)
      (HomologicalComplex.doubleXIso₁ _ rel01 (by decide)).inv ≪≫
    cokernelEpiComp (HomologicalComplex.doubleXIso₀ _ rel01).hom (ModuleCat.ofHom f)

/-- `H⁰` of `[A --f--> B]` is `ker f`. -/
def dblH0Iso : (dblCx f).homology 0 ≅ ModuleCat.of k (LinearMap.ker f) :=
  ((dblCx f).isoHomologyπ (-1) 0 prev0 (dblCx_d_prev f)).symm ≪≫
    (dblCx f).cyclesIsoSc' (-1) 0 1 prev0 next0 ≪≫ ShortComplex.cyclesIsoKernel _ ≪≫
    dblKerIso f ≪≫ ModuleCat.kernelIsoKer _

/-- `H¹` of `[A --f--> B]` is `B ⧸ f A`. -/
def dblH1Iso : (dblCx f).homology 1 ≅ ModuleCat.of k (B ⧸ LinearMap.range f) :=
  (dblCx f).isoHomologyι 1 2 next1 (dblCx_d_next f) ≪≫
    (dblCx f).opcyclesIsoSc' 0 1 2 prev1 next1 ≪≫ ShortComplex.opcyclesIsoCokernel _ ≪≫
    dblCokerIso f ≪≫ ModuleCat.cokernelIsoRangeQuotient _

end Double

section Deriv

open ZInQ.Manuscript.RC.SelmerComplex TauCeti.ContCohomology

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction G M]
  [SMulCommClass G (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- The `0`-cocycles `Z⁰ = ker d⁰` of the genuine continuous cochains. -/
abbrev Z0 : Submodule (ZMod 2) ((contCochains (ZMod 2) G M).X 0) :=
  LinearMap.ker ((contCochains (ZMod 2) G M).d 0 1).hom

/-- The `1`-cocycles `Z¹ = ker d¹`. -/
abbrev Z1 : Submodule (ZMod 2) ((contCochains (ZMod 2) G M).X 1) :=
  LinearMap.ker ((contCochains (ZMod 2) G M).d 1 2).hom

/-- `d⁰ : C⁰ → Z¹`. -/
def relaxedD : (contCochains (ZMod 2) G M).X 0 →ₗ[ZMod 2] Z1 G M :=
  ((contCochains (ZMod 2) G M).d 0 1).hom.codRestrict (Z1 G M) fun x => LinearMap.mem_ker.mpr (by
    have h := congrArg (fun φ => ModuleCat.Hom.hom φ x) ((contCochains (ZMod 2) G M).d_comp_d 0 1 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h
    exact h)

/-- **The relaxed derivative condition** `D⁰ ⊕ (F ⊕ S)[−1] = τ_{≤1} C^•_cont(G, M) = [C⁰ → Z¹]`
(it does not include `D²`, tex 4567–4570). -/
abbrev relaxedCx : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ := dblCx (relaxedD G M)

/-- **The strict derivative condition** `D⁰ = τ_{≤0} C^•_cont(G, M) = [Z⁰ → 0]`. -/
abbrev strictCx : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ :=
  dblCx (0 : Z0 G M →ₗ[ZMod 2] PUnit.{1})

/-- `ker d⁰ ≃ H⁰(G, M)` (explicit invariants). -/
def z0EquivH0 : Z0 G M ≃+ H0 G M :=
  AddEquiv.ofBijective kerToH0 ⟨by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := (kerToH0_eq_zero_iff x).1 hx
    rw [(contCochains (ZMod 2) G M).shape 0 0 (by simp)] at hy
    exact Subtype.ext hy.symm, kerToH0_surjective⟩

/-- `Z¹ ⧸ d⁰(C⁰) ≃ H¹(G, M)` (explicit). -/
def z1QuotEquivH1 : (Z1 G M ⧸ LinearMap.range (relaxedD G M)) ≃+ H1 G M :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
    ext x
    rw [AddMonoidHom.mem_ker, kerToH1_eq_zero_iff]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, congrArg Subtype.val hy⟩
    · rintro ⟨y, hy⟩; exact ⟨y, Subtype.ext hy⟩ :
      (LinearMap.range (relaxedD G M)).toAddSubgroup = (kerToH1 (k := ZMod 2) (G := G) (M := M)).ker)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ kerToH1_surjective)

/-- **Dimensions of the relaxed derivative condition**: `h⁰ + h¹` of the genuine `C^•_cont(G, M)`. -/
theorem finrank_relaxedCx :
    Module.finrank (ZMod 2) ((relaxedCx G M).homology 0) +
        Module.finrank (ZMod 2) ((relaxedCx G M).homology 1) =
      Module.finrank (ZMod 2) (contCohomology (ZMod 2) G M 0) +
        Module.finrank (ZMod 2) (contCohomology (ZMod 2) G M 1) := by
  rw [(dblH0Iso (relaxedD G M)).toLinearEquiv.finrank_eq,
    (dblH1Iso (relaxedD G M)).toLinearEquiv.finrank_eq]
  congr 1
  · exact ((LinearEquiv.ofEq _ _ (LinearMap.ker_codRestrict _ _ _)).trans
      (toLin ((z0EquivH0 G M).trans (contH0AddEquiv (ZMod 2) G M).symm))).finrank_eq
  · exact (toLin ((z1QuotEquivH1 G M).trans (contH1AddEquiv (ZMod 2) G M).symm)).finrank_eq

/-- **Dimensions of the strict derivative condition**: `h⁰` of the genuine `C^•_cont(G, M)`. -/
theorem finrank_strictCx :
    Module.finrank (ZMod 2) ((strictCx G M).homology 0) +
        Module.finrank (ZMod 2) ((strictCx G M).homology 1) =
      Module.finrank (ZMod 2) (contCohomology (ZMod 2) G M 0) := by
  rw [(dblH0Iso _).toLinearEquiv.finrank_eq, (dblH1Iso _).toLinearEquiv.finrank_eq,
    LinearMap.ker_zero, finrank_top]
  have hs : Subsingleton (PUnit.{1} ⧸ LinearMap.range (0 : Z0 G M →ₗ[ZMod 2] PUnit.{1})) :=
    ⟨fun a b => Quotient.inductionOn₂' a b fun _ _ => rfl⟩
  have : Module.finrank (ZMod 2) (PUnit.{1} ⧸ LinearMap.range (0 : Z0 G M →ₗ[ZMod 2] PUnit.{1})) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [this, add_zero]
  exact (toLin ((z0EquivH0 G M).trans (contH0AddEquiv (ZMod 2) G M).symm)).finrank_eq

/-- **The relaxed derivative condition as a genuine local condition**: the inclusion
`τ_{≤1} C^•_cont(G, M) → C^•_cont(G, M)` (identity on `C⁰`, `Z¹ ⊆ C¹`). -/
def relaxedToLocal : relaxedCx G M ⟶ (natCx (contCochains (ZMod 2) G M)).toCC :=
  HomologicalComplex.mkHomFromDouble rel01 (by decide)
    (ModuleCat.ofHom (LinearMap.id : (contCochains (ZMod 2) G M).X 0 →ₗ[ZMod 2] _))
    (ModuleCat.ofHom (Z1 G M).subtype)
    (by
      ext x
      exact (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC_d_hom
        (natCx (contCochains (ZMod 2) G M)) 0 1 rfl x).trans rfl)
    (by
      intro j hj
      have hj' : j = 2 := by simp at hj; omega
      subst hj'
      ext x
      exact (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC_d_hom
        (natCx (contCochains (ZMod 2) G M)) 1 2 rfl (x : (contCochains (ZMod 2) G M).X 1)).trans x.2)

/-- **The strict derivative condition as a genuine local condition**: `Z⁰ ⊆ C⁰`. -/
def strictToLocal : strictCx G M ⟶ (natCx (contCochains (ZMod 2) G M)).toCC :=
  HomologicalComplex.mkHomFromDouble rel01 (by decide)
    (ModuleCat.ofHom (Z0 G M).subtype) 0
    (by
      ext x
      exact (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC_d_hom
        (natCx (contCochains (ZMod 2) G M)) 0 1 rfl (x : (contCochains (ZMod 2) G M).X 0)).trans x.2)
    (fun _ _ => zero_comp)

end Deriv

section Places

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Manuscript.RC.Limits

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- `G_{K_w}` acts `𝔽₂`-linearly on the genuine local module. -/
instance smulCommClass_locMod (w : HeightOneSpectrum (𝓞 K)) :
    SMulCommClass (Gloc K w) (ZMod 2) (locMod K S W2v w) :=
  ⟨fun h c m => (smul_comm (locMap K S w h) c (show TrivMod (GKS K S) W2v from m) : _)⟩

/-- **The residual dimension of a local condition from genuine objects, every row** (tex
4551–4573): unramified and derivative finite/singular — the unramified complex
`[W --(Φ−1)--> W]` (the derivative finite plane `F = H¹_ur` with `D⁰ = W^{G_w}`; the singular plane
has the same dimension); zero `0`; full — `C^•_cont(G_{K_w}, W)`; derivative strict —
`τ_{≤0} C^•_cont(G_{K_w}, W)` (`strictCx`); derivative relaxed — `τ_{≤1} C^•_cont(G_{K_w}, W)`
(`relaxedCx`); the old Kummer row is the Mattuck input `kd`. -/
def genCondDim2 (w : HeightOneSpectrum (𝓞 K)) (c : LocalCondition) (kd : ℕ) : ℕ :=
  match c with
  | .unramified => Module.finrank (ZMod 2) ((urCx K w (W2 K w)).homology 0) +
      Module.finrank (ZMod 2) ((urCx K w (W2 K w)).homology 1)
  | .zero => 0
  | .full => genLocDim K S w
  | .derivStrict => Module.finrank (ZMod 2) ((strictCx (Gloc K w) (locMod K S W2v w)).homology 0) +
      Module.finrank (ZMod 2) ((strictCx (Gloc K w) (locMod K S W2v w)).homology 1)
  | .derivFiniteOrSingular => Module.finrank (ZMod 2) ((urCx K w (W2 K w)).homology 0) +
      Module.finrank (ZMod 2) ((urCx K w (W2 K w)).homology 1)
  | .derivRelaxed =>
      Module.finrank (ZMod 2) ((relaxedCx (Gloc K w) (locMod K S W2v w)).homology 0) +
      Module.finrank (ZMod 2) ((relaxedCx (Gloc K w) (locMod K S W2v w)).homology 1)
  | .oldKummer => kd

/-- **All condition dimensions except the old-Kummer one come from genuine objects** and are
RC6's `condDimAt` — the named input `hD` of `genCondDim_eq` is removed for the derivative rows.
PROVED. -/
theorem genCondDim2_eq (w : HeightOneSpectrum (𝓞 K)) (c : LocalCondition) (kd : ℕ) :
    genCondDim2 K S w c kd = condDimAt K w c kd := by
  cases c with
  | unramified =>
    simp only [genCondDim2, condDimAt]
    rw [finrank_urCx_W2, hUr_zero, hUr_one]
  | zero => rfl
  | full => exact genLocDim_eq K S w
  | derivStrict =>
    simp only [genCondDim2, condDimAt]
    rw [finrank_strictCx, finrank_genLocH K S W2v w 0 (by omega)]
  | derivFiniteOrSingular =>
    simp only [genCondDim2, condDimAt]
    rw [finrank_urCx_W2, hLoc_zero, hUr_one]
  | derivRelaxed =>
    simp only [genCondDim2, condDimAt]
    rw [finrank_relaxedCx, finrank_genLocH K S W2v w 0 (by omega),
      finrank_genLocH K S W2v w 1 (by omega)]
  | oldKummer => rfl

open Classical in
/-- `genCondDim2` as a function of the prime ideal. -/
def genCondDimFun2 (cond : Ideal (𝓞 K) → LocalCondition) (kd : Ideal (𝓞 K) → ℕ)
    (P : Ideal (𝓞 K)) : ℕ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then genCondDim2 K S ⟨P, h.1, h.2⟩ (cond P) (kd P) else 0

/-- `genCondDimFun2` is RC6's `condDimFun`. PROVED. -/
theorem genCondDimFun2_eq (cond : Ideal (𝓞 K) → LocalCondition) (kd : Ideal (𝓞 K) → ℕ) :
    genCondDimFun2 K S cond kd = condDimFun K cond kd := by
  funext P
  simp only [genCondDimFun2, condDimFun]
  split_ifs
  · exact genCondDim2_eq K S _ _ _
  · rfl

/-- **RC6's `hL` from a residual model of the genuine local complexes and conditions, with genuine
derivative conditions** (no `hD`; only the old-Kummer dimension `kd`, Mattuck, is an input).
PROVED. -/
theorem hL_of_genuineModel2 {N r : ℕ} {Dp : Finset ℕ} (hr : r.Prime) (hDp : ∀ p ∈ Dp, p.Prime)
    (cond : Ideal (𝓞 K) → LocalCondition) (kd : Ideal (𝓞 K) → ℕ)
    (Dsel : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (ZMod 2)) (s : Finset ℤ)
    (archTot : ℕ)
    (hUm : ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r Dp, condSum K (genCondDimFun2 K S cond kd) p)
    (hLm : ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r Dp, genLocSum K S p) :
    ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.U.X n) +
        ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r Dp, ((placesList K cond (condDimFun K cond kd) p).map
        PlaceData.cost).sum + archTot := by
  have h : ∑ p ∈ chargedPrimes N r Dp, ((placesList K cond (condDimFun K cond kd) p).map
      PlaceData.cost).sum = ∑ p ∈ chargedPrimes N r Dp, condSum K (genCondDimFun2 K S cond kd) p +
      ∑ p ∈ chargedPrimes N r Dp, genLocSum K S p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [sum_cost_placesList' K S cond _ (prime_of_mem_chargedPrimes hr hDp p hp),
      genCondDimFun2_eq K S cond kd]
  rw [h]
  omega


/-- The free `𝔽₂`-module of rank `A` in degree `d`, `0` elsewhere. -/
def rankAt (d : ℤ) (A : ℕ) (n : ℤ) : ModuleCat.{0} (ZMod 2) :=
  ModuleCat.of (ZMod 2) (Fin (if n = d then A else 0) → ZMod 2)

theorem finrank_rankAt (d : ℤ) (A : ℕ) (n : ℤ) :
    Module.finrank (ZMod 2) (rankAt d A n) = if n = d then A else 0 :=
  Module.finrank_fin_fun (ZMod 2)

/-- The residual model with condition part of rank `A` in degree `0` and local part of rank `B`
in degree `−1` (zero differentials). -/
def rankModel (A B : ℕ) : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (ZMod 2) where
  G := RankCounts.zeroCx
  U := zeroDiffCx (rankAt 0 A)
  L := zeroDiffCx (rankAt (-1) B)
  res := ⟨fun _ _ _ => 0, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  ι := ⟨fun _ _ _ => 0, fun _ _ _ _ _ _ _ _ _ => rfl⟩

/-- **Non-vacuity of `hL_of_genuineModel`'s rank hypotheses** (LESSON 2): the minimal model built
from the genuine dimensions — condition part of rank `∑_p condSum (genCondDimFun …)` and local part
of rank `∑_p genLocSum` (the genuine local cohomology dimensions over the places above the charged
primes), zero differentials — meets both bounds with equality. PROVED. -/
theorem hL_of_genuineModel_nonvacuous {N r : ℕ} {Dp : Finset ℕ}
    (cond : Ideal (𝓞 K) → LocalCondition) (dD : Ideal (𝓞 K) → ℕ) :
    ∃ (Dsel : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (ZMod 2)) (s : Finset ℤ),
      ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.U.X n) =
        ∑ p ∈ chargedPrimes N r Dp, condSum K (genCondDimFun K S cond dD) p ∧
      ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) =
        ∑ p ∈ chargedPrimes N r Dp, genLocSum K S p := by
  refine ⟨rankModel (∑ p ∈ chargedPrimes N r Dp, condSum K (genCondDimFun K S cond dD) p)
    (∑ p ∈ chargedPrimes N r Dp, genLocSum K S p), {0}, ?_, ?_⟩
  · simp only [Finset.sum_singleton]
    exact (finrank_rankAt 0 _ 0).trans (if_pos rfl)
  · simp only [Finset.sum_singleton]
    exact (finrank_rankAt (-1) _ (0 - 1)).trans (if_pos (by norm_num))


/-- Non-vacuity for `hL_of_genuineModel2`: the minimal model built from the genuine dimensions. -/
theorem hL_of_genuineModel2_nonvacuous {N r : ℕ} {Dp : Finset ℕ}
    (cond : Ideal (𝓞 K) → LocalCondition) (kd : Ideal (𝓞 K) → ℕ) :
    ∃ (Dsel : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (ZMod 2)) (s : Finset ℤ),
      ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.U.X n) =
        ∑ p ∈ chargedPrimes N r Dp, condSum K (genCondDimFun2 K S cond kd) p ∧
      ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) =
        ∑ p ∈ chargedPrimes N r Dp, genLocSum K S p := by
  refine ⟨rankModel (∑ p ∈ chargedPrimes N r Dp, condSum K (genCondDimFun2 K S cond kd) p)
    (∑ p ∈ chargedPrimes N r Dp, genLocSum K S p), {0}, ?_, ?_⟩
  · simp only [Finset.sum_singleton]
    exact (finrank_rankAt 0 _ 0).trans (if_pos rfl)
  · simp only [Finset.sum_singleton]
    exact (finrank_rankAt (-1) _ (0 - 1)).trans (if_pos (by norm_num))

end Places

end ZInQ.Contrib.CloudB3RC53.GenuineInst
