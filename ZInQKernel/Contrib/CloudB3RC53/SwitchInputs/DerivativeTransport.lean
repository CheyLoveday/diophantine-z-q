import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenuineSteps
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.ChangeCondition

/-!
# RC53 SwitchInputs: the quasi switch sides as the local conditions themselves

Proposition `ex:limits-uniform-lower-bound`, the switch at a new derivative prime, tex L5068–5086:
the conditions `D⁰ ⊂ D⁰ ⊕ F[−1], D⁰ ⊕ S[−1] ⊂ D⁰ ⊕ (F ⊕ S)[−1]` at the switch place, the old
conditions retained elsewhere.

`DerivativeSides.lean` proved the homology facts of the local quotients on explicit `H¹` models.
Here the transport to the homology of the ACTUAL chain maps is done without computing the explicit
models at all: the three local quotients sit in a degreewise short exact sequence
`0 → side/strict → relaxed/strict → relaxed/side → 0`, and its long exact cohomology sequence gives
`ker H¹(p) = im H¹(i)` (exactness at `H¹(W_rel)`) and the injectivity of `H¹(i)` as soon as
`H⁰(relaxed/side) = 0`, i.e. the inertia property "`d a` in the side condition ⇒ `a` in the side
condition" (`hcob` of `DerivativeSides.SideCond`). `H⁰(side/strict) = 0` is the same property for the
strict condition.

The local conditions are subcomplexes `SubFam` of the local complexes (for the genuine data: of
`C^•_cont(G_v, M)`), so the per-place assembly needs no casts: the side, strict and relaxed local
condition families are families of subcomplexes, their products `piCx` are literally the local
condition complexes of the genuine Selmer data `selData` (`galoisSelData`) with the inclusions as
local-condition maps, and the quotients are the other team's `quotCx` of the product inclusions.

Nodes:
* `subsingleton_h0_of_injective` (PROVED): `H⁰ = 0` when `d⁰` is injective.
* `QuasiFactsOfSES` / `quasiFactsOfSES_proof` (PROVED, tex L5080–5083): for a degreewise short exact
  sequence `0 → W₁ → W → W₂ → 0` of relation-indexed complexes with `H⁰(W₂) = 0`, `H¹(i)` is injective
  and `ker H¹(p) = im H¹(i)` — exactly the fields `hi`, `hpi` of `QuasiSwitchSide`, now about the
  homology maps of the actual chain maps.
* `SubFam`, `SubFam.cx`, `SubFam.incl`, `SubFam.inclLe`: subcomplexes and their inclusions.
* `DerivFamily`: per-place families `strict ≤ side ≤ relaxed` of subcomplexes with the inertia
  properties `hcobS` (`d x ∈ side ⇒ x ∈ side` for `x` relaxed) and `hcobStr` (for the strict
  condition inside the side one).
* `DerivFamily.relaxedData`, `DerivFamily.sideData`: the Selmer data of the relaxed and the side
  local conditions; `sideData_eq` (PROVED): the side Selmer data of the quasi side is the Selmer
  data of the side local conditions (no identification left as an input).
* `DerivFamily.toQuasiRelaxed` and `DerivFamily.toQuasiSide` (PROVED from the coordinates): the
  `QuasiRelaxedLocalization` and the `QuasiSwitchSide` with all exactness and homology fields
  proved; the coordinates `eR : H¹(W_rel) ≃ k² × k²` and the plane equation `hP` remain inputs
  (`DerivativeAssembly.TameCoordinates`, tex L5027–5037).
* `galois_relaxedData_eq` (PROVED): for genuine local conditions given by subcomplexes of the genuine
  local complexes, `relaxedData` is literally `galoisSelData` of the relaxed conditions (`rfl`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.SelmerComplex

variable {k : Type} [Field k]

/-! ### `H⁰` and the long exact sequence -/

/-- `H⁰` of a relation-indexed complex vanishes when `d⁰ : X⁰ → X¹` is injective. PROVED. -/
theorem subsingleton_h0_of_injective (W : GCx k) (h : Function.Injective (W.d 0 1 rfl)) :
    Subsingleton (W.toCC.homology 0) := by
  have hinj : Function.Injective (W.toCC.iCycles 0).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hcyc : Subsingleton (W.toCC.cycles 0) := by
    refine ⟨fun a b => hinj ?_⟩
    have hz : ∀ c : W.toCC.cycles 0, (W.toCC.iCycles 0).hom c = 0 := by
      intro c
      apply h
      have e := congrArg (fun f => f.hom c) (W.toCC.iCycles_d 0 1)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at e
      exact ((GCx.toCC_d_hom W 0 1 rfl _).symm.trans e).trans (map_zero _).symm
    rw [hz a, hz b]
  exact ((ModuleCat.epi_iff_surjective _).mp inferInstance :
    Function.Surjective (W.toCC.homologyπ 0).hom).subsingleton

/-- The short complex `W₁ → W → W₂` of a pair of relation-indexed chain maps with zero composite. -/
def gSES {W₁ W W₂ : GCx k} (i : GHom W₁ W) (p : GHom W W₂)
    (h : ∀ n x, p.f n n rfl (i.f n n rfl x) = 0) :
    ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ) :=
  ShortComplex.mk (GHom.toCC i) (GHom.toCC p) (by
    rw [GHom.toCC_comp]
    ext n x
    exact h n x)

theorem gSES_shortExact {W₁ W W₂ : GCx k} (i : GHom W₁ W) (p : GHom W W₂)
    (h : ∀ n x, p.f n n rfl (i.f n n rfl x) = 0) (hinj : ∀ n, Function.Injective (i.f n n rfl))
    (hsurj : ∀ n, Function.Surjective (p.f n n rfl))
    (hex : ∀ n y, p.f n n rfl y = 0 → ∃ x, i.f n n rfl x = y) : (gSES i p h).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    exact hex n y hy
  · rw [ModuleCat.mono_iff_injective]
    exact hinj n
  · rw [ModuleCat.epi_iff_surjective]
    exact hsurj n

/-- **The quasi-side homology facts from a short exact sequence** (tex L5080–5083). For a degreewise
short exact sequence `0 → W₁ --i--> W --p--> W₂ → 0` of relation-indexed complexes with
`H⁰(W₂) = 0`, `H¹(i)` is injective and `ker H¹(p) = im H¹(i)`. Classification: PROVED. -/
def QuasiFactsOfSES : Prop :=
  ∀ (k : Type) [Field k] (W₁ W W₂ : GCx k) (i : GHom W₁ W) (p : GHom W W₂)
    (_h : ∀ n x, p.f n n rfl (i.f n n rfl x) = 0), (∀ n, Function.Injective (i.f n n rfl)) →
    (∀ n, Function.Surjective (p.f n n rfl)) →
    (∀ n y, p.f n n rfl y = 0 → ∃ x, i.f n n rfl x = y) →
    Subsingleton (W₂.toCC.homology 0) →
    Function.Injective (H1 i) ∧ LinearMap.ker (H1 p) = LinearMap.range (H1 i)

theorem quasiFactsOfSES_proof : QuasiFactsOfSES := by
  intro k _ W₁ W W₂ i p h hinj hsurj hex h0
  have hS := gSES_shortExact i p h hinj hsurj hex
  haveI : Subsingleton ((gSES i p h).X₃.homology 0) := h0
  refine ⟨?_, ?_⟩
  · have ex1 := (hS.homology_exact₁ 0 1 (by simp)).moduleCat_range_eq_ker
    rw [← LinearMap.ker_eq_bot]
    change LinearMap.ker (HomologicalComplex.homologyMap (gSES i p h).f 1).hom = ⊥
    rw [← ex1, eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_bot, Subsingleton.elim x 0, map_zero]
  · exact (hS.homology_exact₂ 1).moduleCat_range_eq_ker.symm

/-! ### Subcomplexes -/

/-- A subcomplex of a relation-indexed complex: submodules closed under the differential. -/
structure SubFam (L : GCx k) where
  /-- The submodules. -/
  S : ∀ n, Submodule k (L.X n)
  /-- Closure under `d`. -/
  hd : ∀ i j (h : i + 1 = j), S i ≤ (S j).comap (L.d i j h)

variable {L : GCx k}

/-- The subcomplex as a complex. -/
def SubFam.cx (A : SubFam L) : GCx k where
  X n := ModuleCat.of k (A.S n)
  d i j h := ((L.d i j h).domRestrict (A.S i)).codRestrict (A.S j) fun x => A.hd i j h x.2
  d_d i j l hij hjl x := Subtype.ext (L.d_d i j l hij hjl x.1)

/-- The inclusion of a subcomplex. -/
def SubFam.incl (A : SubFam L) : GHom A.cx L where
  f i j h := by subst h; exact (A.S i).subtype
  comm i i₁ j j₁ hij h₁ h₂ hj x := by subst hij hj; rfl

/-- The inclusion of nested subcomplexes. -/
def SubFam.inclLe {A B : SubFam L} (hAB : ∀ n, A.S n ≤ B.S n) : GHom A.cx B.cx where
  f i j h := by subst h; exact Submodule.inclusion (hAB i)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by subst hij hj; rfl

theorem SubFam.inclLe_injective {A B : SubFam L} (hAB : ∀ n, A.S n ≤ B.S n) (n : ℤ) :
    Function.Injective ((SubFam.inclLe hAB).f n n rfl) :=
  Submodule.inclusion_injective (hAB n)

/-! ### Maps between quotient complexes -/

/-- The map of quotient complexes `B/φ(A) → B'/ψ(A')` induced by `χ : B → B'` with
`χ(φ(A)) ⊆ ψ(A')`. -/
def qMap {A B A' B' : GCx k} (φ : GHom A B) (ψ : GHom A' B') (χ : GHom B B')
    (h : ∀ n, quotSub φ n ≤ (quotSub ψ n).comap (χ.f n n rfl)) : GHom (quotCx φ) (quotCx ψ) where
  f i j hij := by subst hij; exact (quotSub φ i).mapQ (quotSub ψ i) (χ.f i i rfl) (h i)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    obtain ⟨b, rfl⟩ := (quotSub φ i).mkQ_surjective x
    change Submodule.Quotient.mk (χ.f i₁ i₁ rfl (B.d i i₁ h₁ b)) =
      Submodule.Quotient.mk (B'.d i i₁ h₂ (χ.f i i rfl b))
    rw [χ.comm i i₁ i i₁ rfl h₁ h₂ rfl]

theorem qMap_mk {A B A' B' : GCx k} (φ : GHom A B) (ψ : GHom A' B') (χ : GHom B B')
    (h : ∀ n, quotSub φ n ≤ (quotSub ψ n).comap (χ.f n n rfl)) (n : ℤ) (b : B.X n) :
    (qMap φ ψ χ h).f n n rfl (Submodule.Quotient.mk b) = Submodule.Quotient.mk (χ.f n n rfl b) :=
  rfl

/-! ### The derivative families -/

variable {ι : Type} {Lv : ι → GCx k}

/-- **The derivative local-condition families** (tex L5068–5083): at every place `v` subcomplexes
`strict ≤ side ≤ relaxed` of the local complex `L_v` (the old conditions: all three equal), with
the inertia properties: `d x ∈ side ⇒ x ∈ side` in degree `0` for `x` relaxed (`hcobS`), and
`d x ∈ strict ⇒ x ∈ strict` in degree `0` for `x` in the side condition (`hcobStr`). -/
structure DerivFamily (Lv : ι → GCx k) where
  /-- The strict condition `D⁰`. -/
  str : ∀ v, SubFam (Lv v)
  /-- The side condition `D⁰ ⊕ F[−1]` (or `D⁰ ⊕ S[−1]`). -/
  side : ∀ v, SubFam (Lv v)
  /-- The relaxed condition `D⁰ ⊕ (F ⊕ S)[−1]`. -/
  rel : ∀ v, SubFam (Lv v)
  hss : ∀ v n, (str v).S n ≤ (side v).S n
  hsr : ∀ v n, (side v).S n ≤ (rel v).S n
  hcobS : ∀ v (x : (Lv v).X 0), x ∈ (rel v).S 0 → (Lv v).d 0 1 rfl x ∈ (side v).S 1 →
    x ∈ (side v).S 0
  hcobStr : ∀ v (x : (Lv v).X 0), x ∈ (side v).S 0 → (Lv v).d 0 1 rfl x ∈ (str v).S 1 →
    x ∈ (str v).S 0

variable (F : DerivFamily Lv)

/-- The strict, side and relaxed local-condition complexes `∏_v U_v`. -/
abbrev DerivFamily.Ustr : GCx k := piCx fun v => (F.str v).cx
abbrev DerivFamily.Uside : GCx k := piCx fun v => (F.side v).cx
abbrev DerivFamily.Urel : GCx k := piCx fun v => (F.rel v).cx

/-- `strict → side`, `side → relaxed`, `strict → relaxed`. -/
def DerivFamily.fs : GHom F.Ustr F.Uside := piMap fun v => SubFam.inclLe (F.hss v)
def DerivFamily.f₁ : GHom F.Uside F.Urel := piMap fun v => SubFam.inclLe (F.hsr v)
def DerivFamily.fr : GHom F.Ustr F.Urel :=
  piMap fun v => SubFam.inclLe fun n => (F.hss v n).trans (F.hsr v n)

theorem DerivFamily.fs_injective (n : ℤ) : Function.Injective (F.fs.f n n rfl) := by
  intro x y h
  funext v
  exact SubFam.inclLe_injective (F.hss v) n (congrFun h v)

theorem DerivFamily.f₁_injective (n : ℤ) : Function.Injective (F.f₁.f n n rfl) := by
  intro x y h
  funext v
  exact SubFam.inclLe_injective (F.hsr v) n (congrFun h v)

theorem DerivFamily.f₁_fs (n : ℤ) (x : F.Ustr.X n) :
    F.f₁.f n n rfl (F.fs.f n n rfl x) = F.fr.f n n rfl x := rfl

/-- The local quotients `W₁ = side/strict`, `W_rel = relaxed/strict`, `W₂ = relaxed/side`. -/
abbrev DerivFamily.W₁ : GCx k := quotCx F.fs
abbrev DerivFamily.Wrel : GCx k := quotCx F.fr
abbrev DerivFamily.W₂ : GCx k := quotCx F.f₁

/-- `i : W₁ → W_rel`, induced by `side → relaxed`. -/
def DerivFamily.i : GHom F.W₁ F.Wrel :=
  qMap F.fs F.fr F.f₁ (by
    rintro n _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩)

/-- `p : W_rel → W₂`, induced by the identity of the relaxed condition. -/
def DerivFamily.p : GHom F.Wrel F.W₂ :=
  qMap F.fr F.f₁ (idGHom F.Urel) (by
    rintro n _ ⟨x, rfl⟩
    exact ⟨F.fs.f n n rfl x, rfl⟩)

theorem DerivFamily.p_i (n : ℤ) (x : F.W₁.X n) : F.p.f n n rfl (F.i.f n n rfl x) = 0 := by
  obtain ⟨b, rfl⟩ := (quotSub F.fs n).mkQ_surjective x
  change Submodule.Quotient.mk (F.f₁.f n n rfl b) = (0 : F.Urel.X n ⧸ quotSub F.f₁ n)
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨b, rfl⟩

theorem DerivFamily.i_injective (n : ℤ) : Function.Injective (F.i.f n n rfl) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨b, rfl⟩ := (quotSub F.fs n).mkQ_surjective x
  change Submodule.Quotient.mk (F.f₁.f n n rfl b) = (0 : F.Urel.X n ⧸ quotSub F.fr n) at hx
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨a, ha⟩ := hx
  show (Submodule.Quotient.mk b : F.Uside.X n ⧸ quotSub F.fs n) ∈ (⊥ : Submodule k (F.Uside.X n ⧸ quotSub F.fs n))
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  refine ⟨a, F.f₁_injective n ?_⟩
  rw [F.f₁_fs]
  exact ha

theorem DerivFamily.p_surjective (n : ℤ) : Function.Surjective (F.p.f n n rfl) := by
  intro y
  obtain ⟨c, rfl⟩ := (quotSub F.f₁ n).mkQ_surjective y
  exact ⟨Submodule.Quotient.mk c, rfl⟩

theorem DerivFamily.p_exact (n : ℤ) (y : F.Wrel.X n) (hy : F.p.f n n rfl y = 0) :
    ∃ x, F.i.f n n rfl x = y := by
  obtain ⟨c, rfl⟩ := (quotSub F.fr n).mkQ_surjective y
  change Submodule.Quotient.mk c = (0 : F.Urel.X n ⧸ quotSub F.f₁ n) at hy
  rw [Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨b, rfl⟩ := hy
  exact ⟨Submodule.Quotient.mk b, rfl⟩

/-- `H⁰(W₂) = 0` from the inertia property `hcobS`. PROVED. -/
theorem DerivFamily.h0_W₂ : Subsingleton (F.W₂.toCC.homology 0) := by
  apply subsingleton_h0_of_injective
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨c, rfl⟩ := (quotSub F.f₁ 0).mkQ_surjective x
  change Submodule.Quotient.mk (F.Urel.d 0 1 rfl c) = (0 : F.Urel.X 1 ⧸ quotSub F.f₁ 1) at hx
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨b, hb⟩ := hx
  show (Submodule.Quotient.mk c : F.Urel.X 0 ⧸ quotSub F.f₁ 0) ∈ (⊥ : Submodule k (F.Urel.X 0 ⧸ quotSub F.f₁ 0))
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have hv : ∀ v, ((c : ∀ v, (F.rel v).S 0) v).1 ∈ (F.side v).S 0 := by
    intro v
    have e : (((F.f₁.f 1 1 rfl b : F.Urel.X 1) : ∀ v, (F.rel v).S 1) v).1 =
        (((F.Urel.d 0 1 rfl c : F.Urel.X 1) : ∀ v, (F.rel v).S 1) v).1 := by rw [hb]
    have e2 : (((F.Urel.d 0 1 rfl c : F.Urel.X 1) : ∀ v, (F.rel v).S 1) v).1 =
        (Lv v).d 0 1 rfl ((c : ∀ v, (F.rel v).S 0) v).1 := rfl
    refine F.hcobS v _ ((c : ∀ v, (F.rel v).S 0) v).2 ?_
    rw [← e2, ← e]
    exact ((b : ∀ v, (F.side v).S 1) v).2
  exact ⟨fun v => ⟨((c : ∀ v, (F.rel v).S 0) v).1, hv v⟩, rfl⟩

/-- `H⁰(W₁) = 0` from the inertia property `hcobStr`. PROVED. -/
theorem DerivFamily.h0_W₁ : Subsingleton (F.W₁.toCC.homology 0) := by
  apply subsingleton_h0_of_injective
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨c, rfl⟩ := (quotSub F.fs 0).mkQ_surjective x
  change Submodule.Quotient.mk (F.Uside.d 0 1 rfl c) = (0 : F.Uside.X 1 ⧸ quotSub F.fs 1) at hx
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨b, hb⟩ := hx
  show (Submodule.Quotient.mk c : F.Uside.X 0 ⧸ quotSub F.fs 0) ∈ (⊥ : Submodule k (F.Uside.X 0 ⧸ quotSub F.fs 0))
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have hv : ∀ v, ((c : ∀ v, (F.side v).S 0) v).1 ∈ (F.str v).S 0 := by
    intro v
    have e : (((F.fs.f 1 1 rfl b : F.Uside.X 1) : ∀ v, (F.side v).S 1) v).1 =
        (((F.Uside.d 0 1 rfl c : F.Uside.X 1) : ∀ v, (F.side v).S 1) v).1 := by rw [hb]
    have e2 : (((F.Uside.d 0 1 rfl c : F.Uside.X 1) : ∀ v, (F.side v).S 1) v).1 =
        (Lv v).d 0 1 rfl ((c : ∀ v, (F.side v).S 0) v).1 := rfl
    refine F.hcobStr v _ ((c : ∀ v, (F.side v).S 0) v).2 ?_
    rw [← e2, ← e]
    exact ((b : ∀ v, (F.str v).S 1) v).2
  exact ⟨fun v => ⟨((c : ∀ v, (F.side v).S 0) v).1, hv v⟩, rfl⟩

/-- **The transported quasi-side facts** (tex L5072–5083): `H⁰(W₁) = 0`, `H¹(i)` injective and
`ker H¹(p) = im H¹(i)` for the actual chain maps. Classification: PROVED. -/
theorem DerivFamily.quasiFacts :
    Subsingleton (F.W₁.toCC.homology 0) ∧ Function.Injective (H1 F.i) ∧
      LinearMap.ker (H1 F.p) = LinearMap.range (H1 F.i) :=
  ⟨F.h0_W₁, quasiFactsOfSES_proof k F.W₁ F.Wrel F.W₂ F.i F.p F.p_i F.i_injective F.p_surjective
    F.p_exact F.h0_W₂⟩

/-! ### The Selmer data and the quasi sides -/

variable (G : GCx k) (res : GHom G (piCx Lv))

/-- The Selmer data of the relaxed local conditions: `G --res--> ∏_v L_v <-- ∏_v U_v^{rel}`. -/
def DerivFamily.relaxedData : SelData k :=
  ⟨G, F.Urel, piCx Lv, res, piMap fun v => (F.rel v).incl⟩

/-- The Selmer data of the side local conditions. -/
def DerivFamily.sideData : SelData k :=
  ⟨G, F.Uside, piCx Lv, res, piMap fun v => (F.side v).incl⟩

/-- The relaxed localization of the derivative family, given coordinates
`eR : H¹(W_rel) ≃ k² × k²` (tex L5027–5037). -/
def DerivFamily.toQuasiRelaxed (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k)) :
    QuasiRelaxedLocalization k :=
  ⟨F.relaxedData G res, F.Wrel, quotMk F.fr, eR⟩

/-- **The quasi switch side of the derivative family** (tex L5068–5086): every exactness field and
the homology fields `h0`, `hi`, `hpi` are PROVED; the plane equation `hP` (the image of `H¹(W₁)`
in the coordinates is the side plane, tex L5027–5037) is the remaining input. -/
def DerivFamily.toQuasiSide (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (P : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (hP : (LinearMap.range (H1 F.i)).map eR.toLinearMap = P) :
    QuasiSwitchSide (F.toQuasiRelaxed G res eR) P where
  U₁ := F.Uside
  Ustr := F.Ustr
  W₁ := F.W₁
  W₂ := F.W₂
  f₁ := F.f₁
  g₂ := quotMk F.f₁
  fs := F.fs
  g₁ := quotMk F.fs
  i := F.i
  p := F.p
  hfg₂ n u := quotMk_comp_apply F.f₁ n u
  f₁_inj := F.f₁_injective
  g₂_surj := quotMk_surjective F.f₁
  ex₂ n u hu := (quotMk_eq_zero_iff F.f₁ n u).1 hu
  hfg₁ n u := quotMk_comp_apply F.fs n u
  fs_inj := F.fs_injective
  g₁_surj := quotMk_surjective F.fs
  ex₁ n u hu := (quotMk_eq_zero_iff F.fs n u).1 hu
  hRF _ _ := rfl
  hpR _ _ := rfl
  h0 := F.quasiFacts.1
  hi := F.quasiFacts.2.1
  hpi := F.quasiFacts.2.2
  hP := hP

/-- **The side Selmer data is the Selmer data of the side local conditions** (tex L5072–5083): the
quasi side's `Dside = restrictData R.D f₁` is `sideData`, with the local-condition map the inclusion
of the side conditions. So the switch steps' sides are the genuine fibres of the side
configuration by construction. Classification: PROVED. -/
theorem DerivFamily.sideData_eq (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (P : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (hP : (LinearMap.range (H1 F.i)).map eR.toLinearMap = P) :
    (F.toQuasiSide G res eR P hP).Dside = F.sideData G res := by
  change restrictData (F.relaxedData G res) F.f₁ = F.sideData G res
  unfold restrictData DerivFamily.sideData DerivFamily.relaxedData
  congr 1
  exact ghom_ext fun n x => rfl

/-! ### The genuine Selmer data -/

section Galois

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

/-- The genuine local complexes `C^•_cont(G_v, M)` at the places of `S`. -/
abbrev galLv : Places K S → GCx k :=
  localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M

/-- The genuine local conditions given by a family of subcomplexes of the genuine local
complexes. -/
def galCond (A : ∀ v, SubFam (galLv (k := k) K S M v)) : GaloisLocalConditions K S k M :=
  ⟨fun v => (A v).cx, fun v => (A v).incl⟩

/-- **The relaxed and side Selmer data are the genuine Selmer data** (tex L5068–5083): for a
derivative family of subcomplexes of the genuine local complexes, `relaxedData` (with the global
complex `C^•_cont(G_{K,S}, M)` and `res_S`) is literally `galoisSelData` of the relaxed conditions,
and `sideData` that of the side conditions. Classification: PROVED (`rfl`). -/
theorem galois_relaxedData_eq (F : DerivFamily (galLv (k := k) K S M)) :
    F.relaxedData (globalCx k (GKS K S) M)
        (resS k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M) =
      galoisSelData K S k M (galCond K S M F.rel) ∧
    F.sideData (globalCx k (GKS K S) M)
        (resS k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M) =
      galoisSelData K S k M (galCond K S M F.side) :=
  ⟨rfl, rfl⟩

end Galois

/-! ### Non-vacuity -/

/-- The whole complex as a subcomplex. -/
def SubFam.top (L : GCx k) : SubFam L := ⟨fun _ => ⊤, fun _ _ _ _ _ => Submodule.mem_top⟩

/-- **Non-vacuity of `DerivFamily`** (LESSON 2): the old conditions (all three equal) at every
place, for any family of complexes; the inertia properties hold. -/
def DerivFamily.const (Lv : ι → GCx k) (A : ∀ v, SubFam (Lv v)) : DerivFamily Lv where
  str := A
  side := A
  rel := A
  hss _ _ := le_rfl
  hsr _ _ := le_rfl
  hcobS _ _ hx _ := hx
  hcobStr _ _ hx _ := hx

/-- The complex with `V` in every degree and zero differentials. -/
def zdCx (V : Type) [AddCommGroup V] [Module k V] : GCx k where
  X _ := ModuleCat.of k V
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- The plane-supported subcomplex of the zero-differential complex `constCx V`: `P` in degree one,
`0` elsewhere. -/
def planeSub {V : Type} [AddCommGroup V] [Module k V] (P : Submodule k V) :
    SubFam (zdCx (k := k) V) where
  S n := if n = 1 then P else ⊥
  hd _ j _ _ _ := (Submodule.zero_mem _ : (0 : V) ∈ (if j = 1 then P else ⊥))

/-- **A nontrivial derivative family** (LESSON 2): one place, the local complex `constCx (k² × k²)`
(zero differential), strict condition `0`, side condition the finite plane `F` in degree one,
relaxed condition all of `F ⊕ S` in degree one; the inertia properties hold, and the transported
quasi-side facts apply (`quasiFacts`). -/
def exDerivFamily : DerivFamily (fun _ : Unit => zdCx (k := k) ((Fin 2 → k) × (Fin 2 → k))) where
  str _ := planeSub ⊥
  side _ := planeSub (ZInQ.Manuscript.RC.Uniform.finPlane k (Fin 2 → k) (Fin 2 → k))
  rel _ := planeSub ⊤
  hss _ n := by
    change (if n = 1 then (⊥ : Submodule k ((Fin 2 → k) × (Fin 2 → k))) else ⊥) ≤
      (if n = 1 then ZInQ.Manuscript.RC.Uniform.finPlane k (Fin 2 → k) (Fin 2 → k) else ⊥)
    split_ifs <;> exact bot_le
  hsr _ n := by
    change (if n = 1 then ZInQ.Manuscript.RC.Uniform.finPlane k (Fin 2 → k) (Fin 2 → k) else ⊥) ≤
      (if n = 1 then (⊤ : Submodule k ((Fin 2 → k) × (Fin 2 → k))) else ⊥)
    split_ifs <;> simp
  hcobS _ x hx _ := by
    have h' : x = 0 := by
      simpa [planeSub] using hx
    show (x : (Fin 2 → k) × (Fin 2 → k)) ∈ (if (0 : ℤ) = 1 then ZInQ.Manuscript.RC.Uniform.finPlane k (Fin 2 → k) (Fin 2 → k) else ⊥)
    rw [h']
    exact Submodule.zero_mem _
  hcobStr _ x hx _ := by
    have h' : x = 0 := by
      simpa [planeSub] using hx
    show (x : (Fin 2 → k) × (Fin 2 → k)) ∈ (if (0 : ℤ) = 1 then (⊥ : Submodule k ((Fin 2 → k) × (Fin 2 → k))) else ⊥)
    rw [h']
    exact Submodule.zero_mem _

theorem exDerivFamily_quasiFacts :
    Subsingleton ((exDerivFamily (k := k)).W₁.toCC.homology 0) ∧
      Function.Injective (H1 (exDerivFamily (k := k)).i) ∧
      LinearMap.ker (H1 (exDerivFamily (k := k)).p) = LinearMap.range (H1 (exDerivFamily (k := k)).i) :=
  (exDerivFamily (k := k)).quasiFacts

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
