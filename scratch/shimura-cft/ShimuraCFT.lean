import ZInQKernel.OneProof.H.TailZ12
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.SmoothFibre.Basic
import ZInQKernel.Contrib.FrobChain.Rigidity
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Adeles.FiniteBaseChange

/-!
# shimura-cft: Shimura's Main Theorem I with its reciprocity law (Deligne's adelic form, Tau Ceti's
# Artin map), and the fields `shimuraFamily` / `shimuraFamilyAb` from it

Part A (verbatim copies, scratch files cannot import each other):
* A1: `scratch/r1univ-rigid/R1UnivLeaves.lean` (origin/wip/route-a-fold), lines 10-564: the core
  `LeafQM.AV.R1UnivRigid` (`R1fpPropsAb`, `MumfordRigidityCore`, `r1fpProps_iff_ab_core`);
* A2: `scratch/c-to-printed/Shimura.lean` (origin/wip/c-to-printed), without its `import` line:
  `ShimuraSplit.IsHolFamily`, `holP1_of_isHolFamily`, `IsShimuraHolFamily`, `ShimuraHolFamily`,
  `InGamma3`, `ShimuraMainThmIY3`, `shimuraFamily_of_mainThmI`;
* A3: `HDec.QMSplit.Moduli.ShimuraFamilyAb` from `R1UnivLeaves.lean` (the field of route-a-fold's
  `OpenResearchLeaves11`).

Part B (new): see the section headers below and `docs/research/shimura-cft.md`.
-/

set_option linter.all false

/-!
# r1univ-rigid: closing the `R1univProps` gap with Mumford's rigidity

`LeafQM.AV.R1univProps` (ZInQKernel/HDecomp/QM/Leaves.lean) classifies families `QMFamily S`
(proper smooth families with endomorphisms `ι(a)` and sections `η(a)`, *no group law*), while the
published fine-moduli theorems classify abelian schemes. This file

1. states Mumford's rigidity/abelian-scheme theorem as one leaf `MumfordRigidity` over Mathlib's
   schemes and the kernel's `PkgI3.AbVar`;
2. defines `QMAbScheme S` (an abelian scheme over `S` with `𝒪`-action and level-3 structure, i.e.
   the objects of the published moduli problem) and states the abelian-scheme versions
   `R1univAbProps`, `R1famAbProps`, `R1fpPropsAb` of the kernel's clauses;
3. proves `R1univProps Y Φ` from `MumfordRigidity` and `R1univAbProps Y Φ`
   (`r1univProps_of_ab`), and `R1fpProps Y Φ ↔ R1fpPropsAb Y Φ` under `MumfordRigidity`
   (`r1fpProps_iff_ab`).

No `sorry`, no `axiom`. See `docs/research/r1univ-rigid.md`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace R1UnivRigid

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-! ## §1 Fibres of a family that are abelian varieties -/

/-- **`A` is the fibre of `F → S` at the field point `s : Spec K → S`, with identity `e(s)`**:
`g : A → F` makes `A → Spec K` the pullback of `F → S` along `s`, and carries the identity
`K`-point of `A` to the section `e` (the shape of `IsBaseChangeOfPair` and of
`IsFibreOf` at `a = 0`). -/
def IsAbVarFibre {S : Scheme.{0}} (F : Over S) (e : S ⟶ F.left) {K : Type} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K) (g : A.X.left ⟶ F.left) : Prop :=
  IsPullback g A.X.hom F.hom s ∧ (1 : A.Pt K).left ≫ g = s ≫ e

/-- **`g` is a group homomorphism onto the fibre** (for a group object `F` of `Over S`): the
multiplication of `A` followed by `g` is `g × g` followed by the multiplication of `F`; `φ` is the
map `A ×_K A → F ×_S F` induced by `g` (unique, the target being a pullback). -/
def IsGrpFibre {S : Scheme.{0}} (F : Over S) [GrpObj F] {K : Type} [Field K] (A : AbVar K)
    (g : A.X.left ⟶ F.left) : Prop :=
  ∃ φ : (A.X ⊗ A.X).left ⟶ (F ⊗ F).left,
    φ ≫ (fst F F).left = (fst A.X A.X).left ≫ g ∧ φ ≫ (snd F F).left = (snd A.X A.X).left ≫ g ∧
    μ[A.X].left ≫ g = φ ≫ μ[F].left

/-! ## §2 The rigidity leaf -/

/-- **LEAF (Mumford's rigidity; abelian-scheme structure on a smooth proper family with a section).**
Let `S` be a locally noetherian scheme, `F → S` proper, smooth, with geometrically connected fibres,
and `e : S → F` a section, such that every field fibre `F_s` (`s : Spec K → S`) is an abelian variety
with identity `e(s)`. Then `F` carries a group-object structure over `S` (an abelian scheme) with
identity `e` such that
* (a) every `S`-endomorphism `f` of `F` with `f ∘ e = e` is a homomorphism;
* (b) every identification `g : A ≅ F_s` of an abelian variety with a fibre, carrying the identity of
  `A` to `e(s)`, is a group homomorphism.

Sources (theorem numbers from memory, UNVERIFIED): Mumford, *Geometric Invariant Theory*, Ch. 6, §1:
Def. 6.1 (abelian scheme: smooth proper group scheme with geometrically connected fibres), Prop. 6.1
(rigidity lemma), Cor. 6.4 (an `S`-morphism of abelian schemes carrying identity to identity is a
homomorphism), Cor. 6.5 (abelian schemes are commutative), Cor. 6.6 (the group structure is determined
by the identity section), Thm. 6.14 (`S` connected and locally noetherian, `F → S` smooth proper with a
section `e`, one fibre an abelian variety with identity `e(s)`: then `F` is an abelian scheme with
identity `e`; due to Grothendieck, via the rigidity of deformations, §6.3).

*Form*: a consequence of these printed statements. Existence: Thm 6.14 on each connected component of
`S` (open, since `S` is locally noetherian), the group laws glued over the disjoint union. (a) is
Cor. 6.4 for `X = Y = F`. (b): the base change `F_s` is an abelian scheme over `Spec K` with identity
`e(s)`, i.e. an abelian variety, and `g : A ≅ F_s` carries identity to identity, so it is a
homomorphism by Cor. 6.4 over `Spec K` (equivalently Mumford, *Abelian varieties*, §4 Cor. 1, which the
kernel proves: `G0FibreSimple.rigidityHom`). The hypotheses are stronger than printed (every fibre, at
every field, is an abelian variety, and `S` need not be connected), so the leaf is not stronger than its
sources. -/
def MumfordRigidity : Prop :=
  ∀ (S : Scheme.{0}) (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → IsProper F.hom →
    Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e ∧
      (∀ f : F ⟶ F, e ≫ f.left = e → IsMonHom f) ∧
      (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K)
        (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g → IsGrpFibre F A g)

/-! ## §3 Abelian schemes with `𝒪`-action and level-3 structure: the published moduli problem -/

/-- **An abelian surface scheme over `S` with QM by `𝒪` and a level-3 structure** (the objects of
the published moduli problem; Shimura 1967, Deligne 1971 in its PEL form, Buzzard 1997 §1 in the
unpolarized form): a `QMFamily` (proper, smooth of relative dimension 2, `ι(a)`, `η(a)`) that is an
abelian scheme (`GrpObj` over `S`, geometrically connected fibres; Mumford GIT Def. 6.1, as the
kernel's `IsAbelianScheme`) with identity `η(0)`, such that `ι : 𝒪 → End_S(A)` is a unital ring
homomorphism into the homomorphisms (`ι(ab) = ι(a) ∘ ι(b)`, `ι(a+b) = ι(a)·ι(b)` in the group
`Hom_S(A, A)`), and `η : 𝒪 → A(S)` is an `𝒪`-linear group homomorphism whose kernel on every field
fibre is exactly `3𝒪`.

The level clauses are the relative form of the kernel's `Level3`: `eta_three` says `η` kills `3𝒪`
globally, so it is a map `(𝒪/3𝒪)_S → A[3]`; `eta_ker` says it is injective on every field fibre. In
characteristic 0 such a map is an isomorphism, both sides being finite étale of degree 81
(`#A_s[3] = 3⁴`, the kernel's `TorsionStructure`), and conversely (STANDARD; the same argument as
`Structures.lean` §2 over a field). Without `eta_three` the class would be too large over a
non-reduced `S` (independent review: `S = Spec ℚ[ε]`, `η = η₀ + ε·δ`). Injectivity of `ι` is not required: for `S ≠ ∅`
a unital ring map `𝒪 → End_S(A)` is injective (its kernel is a two-sided ideal with torsion-free
quotient, `B` is simple), and for `S = ∅` there is nothing to classify. The polarization of the PEL
form is not part of the datum (Lemma P / rv-qm-polar: for the fixed `μ` it exists and is unique;
see the report §4 for its relative form). -/
structure QMAbScheme (S : Scheme.{0}) extends QMFamily S where
  [grp : GrpObj F]
  geomConn : GeometricallyConnected F.hom
  one_eq : η[F].left = eta 0
  iota_hom : ∀ a : O, IsMonHom (Over.homMk (iota a) (iota_over a) : F ⟶ F)
  iota_one : iota 1 = 𝟙 _
  iota_mul : ∀ a b : O, iota (a * b) = iota b ≫ iota a
  iota_add : ∀ a b : O, (Over.homMk (iota (a + b)) (iota_over _) : F ⟶ F) =
    Over.homMk (iota a) (iota_over a) * Over.homMk (iota b) (iota_over b)
  eta_add : ∀ a b : O, (Over.homMk (U := 𝟙_ (Over S)) (eta (a + b)) (eta_sec _) : 𝟙_ (Over S) ⟶ F) =
    Over.homMk (U := 𝟙_ (Over S)) (eta a) (eta_sec a) *
      Over.homMk (U := 𝟙_ (Over S)) (eta b) (eta_sec b)
  eta_linear : ∀ a b : O, eta (a * b) = eta b ≫ iota a
  eta_three : ∀ b : O, eta (3 * b) = eta 0
  eta_ker : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (a : O),
    s ≫ eta a = s ≫ eta 0 ↔ ∃ b : O, a = 3 * b

/-- **R1univ, abelian-scheme clause** (the existence half of the universal property of the published
fine moduli scheme, on abelian-scheme families over proper smooth curves `S/ℚ` whose field fibres are
objects): `R1univProps` restricted to the families that are abelian schemes with `𝒪`-action and
level-3 structure. -/
def R1univAbProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ 𝒜' : QMAbScheme S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
        IsFibreOf 𝒜'.toQMFamily s.left P) →
      ∃ g : S ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S) (P : QML3 K),
        IsFibreOf 𝒜'.toQMFamily s.left P → Φ K (s ≫ g) = M3.mk P

/-- **R1fam, abelian-scheme clause**: `Φ` is induced by an abelian scheme over `Y` with `𝒪`-action
and level-3 structure (the universal object of the published moduli problem). -/
def R1famAbProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ 𝒜 : QMAbScheme Y.left, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
    Φ K y = M3.mk P → IsFibreOf 𝒜.toQMFamily y.left P

/-- **R1fp, abelian-scheme clause list**: the kernel's `R1fpProps` with `R1famProps` and
`R1univProps` replaced by their abelian-scheme versions (the form in which the published fine-moduli
theorems are stated). -/
def R1fpPropsAb (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famAbProps Y Φ ∧ R1univAbProps Y Φ

/-! ## §4 The easy directions -/

theorem r1univAbProps_of_r1univProps {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1univProps Y Φ) : R1univAbProps Y Φ :=
  fun S hp hs 𝒜' hfib => h S hp hs 𝒜'.toQMFamily hfib

theorem r1famProps_of_r1famAbProps {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1famAbProps Y Φ) : R1famProps Y Φ := by
  obtain ⟨𝒜, h𝒜⟩ := h
  exact ⟨𝒜.toQMFamily, h𝒜⟩


/-! ## §5 Glue lemmas (proved) -/

/-- A smooth scheme over a field is reduced (copied verbatim from `scratch/curve-split/CurveBij.lean`,
`isReduced_of_smooth`, with `SpecK k` written out). -/
theorem isReduced_of_smooth {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
    have hVU : V ≤ f ⁻¹ᵁ ⊤ := by simp
    have hsm := f.smooth_appLE hU hV hVU
    let _ : Field Γ(Spec (CommRingCat.of k), ⊤) :=
      (ZInQ.Contrib.Dim.isField_sections_spec k ⊤ Set.univ_nonempty).toField
    let _ : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := (f.appLE ⊤ V hVU).hom.toAlgebra
    have : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := hsm
    have : _root_.IsReduced Γ(X, V) :=
      ZInQ.SmoothFibre.isReduced_of_smooth_of_field Γ(Spec (CommRingCat.of k), ⊤) _
    let x' : V := ⟨x, hxV⟩
    have hloc := hV.isLocalization_stalk x'
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
    exact isReduced_localizationPreserves (hV.primeIdealOf x').asIdeal.primeCompl
      (X.presheaf.stalk x') ‹_›
  exact isReduced_of_isReduced_stalk X

/-- Two morphisms from a reduced scheme to a scheme separated over `W`, equal over `W`, are equal
if they agree on all field points (Mathlib's `ext_of_fromSpecResidueField_eq` at residue fields). -/
theorem hom_ext_pts {X Z W : Scheme.{0}} [IsReduced X] (i : Z ⟶ W) [IsSeparated i] (u v : X ⟶ Z)
    (hu : u ≫ i = v ≫ i)
    (h : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ X), t ≫ u = t ≫ v) : u = v :=
  ext_of_fromSpecResidueField_eq u v i Set.univ dense_univ
    (fun x _ => h _ (X.fromSpecResidueField x)) hu

/-- A field point `t : Spec K → S` of a `ℚ`-scheme is a point of `fieldPt K` for the induced
`ℚ`-algebra structure on `K`; so the fibre hypothesis of `R1univProps` (stated for `ℚ`-algebras)
gives fibres at all field points. -/
theorem fibre_of_fieldPt {S : Over (Spec (CommRingCat.of ℚ))} (𝒜 : QMFamily S.left)
    (hfib : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 s.left P)
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S.left) : ∃ P : QML3 K, IsFibreOf 𝒜 t P := by
  let : Algebra ℚ K := (Spec.preimage (t ≫ S.hom)).hom.toAlgebra
  have ht : t ≫ S.hom = (fieldPt K).hom := (Spec.map_preimage (t ≫ S.hom)).symm
  exact hfib K (Over.homMk t ht)

/-- The fibres of a family whose field fibres are objects are connected: `F → S` is geometrically
connected (the fibre at `Spec K → S` is `P.A`, geometrically integral over `K`). -/
theorem geomConn_of_fibres {S : Scheme.{0}} (𝒜 : QMFamily S)
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 t P) : GeometricallyConnected 𝒜.F.hom := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  obtain ⟨P, g, hpb, -, -⟩ := hfib K y
  have e : P.A.X.left ≅ Z := IsPullback.isoIsPullback _ _ hpb h
  have : IrreducibleSpace P.A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton P.A.X.hom
  exact (Scheme.homeoOfIso e).surjective.connectedSpace (Scheme.homeoOfIso e).continuous

/-- The identity point of the fibre goes to `η(0)`. -/
theorem one_left_comp {S : Scheme.{0}} {𝒜 : QMFamily S} {K : Type} [Field K]
    {t : Spec (CommRingCat.of K) ⟶ S} {P : QML3 K} {g : P.A.X.left ⟶ 𝒜.F.left}
    (he : ∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = t ≫ 𝒜.eta a) :
    (1 : P.A.Pt K).left ≫ g = t ≫ 𝒜.eta 0 := by
  have h0 := he 0
  rw [map_zero] at h0
  exact h0

/-- Morphisms `F → F` over `S` are determined on the fibres, when `F` is reduced. -/
theorem F_ext {S : Scheme.{0}} (𝒜 : QMFamily S) [IsReduced 𝒜.F.left]
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 t P)
    (u v : 𝒜.F.left ⟶ 𝒜.F.left) (hu : u ≫ 𝒜.F.hom = v ≫ 𝒜.F.hom)
    (h : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S) (P : QML3 K)
      (g : P.A.X.left ⟶ 𝒜.F.left), IsPullback g P.A.X.hom 𝒜.F.hom t →
      (∀ a : O, (P.q.iota a).hom.left ≫ g = g ≫ 𝒜.iota a) →
      (∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = t ≫ 𝒜.eta a) → g ≫ u = g ≫ v) :
    u = v := by
  have := 𝒜.proper
  refine hom_ext_pts 𝒜.F.hom u v hu (fun K _ x => ?_)
  obtain ⟨P, g, hpb, hι, he⟩ := hfib K (x ≫ 𝒜.F.hom)
  have hx := hpb.lift_fst x (𝟙 _) (by simp)
  rw [← hx, Category.assoc, Category.assoc, h K _ P g hpb hι he]

/-- Sections of `F → S` are determined on the fibres, when `S` is reduced. -/
theorem sec_ext {S : Scheme.{0}} [IsReduced S] (𝒜 : QMFamily S)
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 t P)
    (u v : S ⟶ 𝒜.F.left) (hu : u ≫ 𝒜.F.hom = v ≫ 𝒜.F.hom)
    (h : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S) (P : QML3 K)
      (g : P.A.X.left ⟶ 𝒜.F.left), IsPullback g P.A.X.hom 𝒜.F.hom t →
      (∀ a : O, (P.q.iota a).hom.left ≫ g = g ≫ 𝒜.iota a) →
      (∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = t ≫ 𝒜.eta a) → t ≫ u = t ≫ v) :
    u = v := by
  have := 𝒜.proper
  refine hom_ext_pts 𝒜.F.hom u v hu (fun K _ t => ?_)
  obtain ⟨P, g, hpb, hι, he⟩ := hfib K t
  exact h K t P g hpb hι he


/-- `lift` into the fibre product commutes with the fibre identification `g` (bookkeeping for the
group laws). -/
theorem lift_comp_φ {S : Scheme.{0}} {F : Over S} {K : Type} [Field K] {A : AbVar K}
    {g : A.X.left ⟶ F.left} {X : Over (Spec (CommRingCat.of K))} {Z : Over S}
    (f₁ f₂ : X ⟶ A.X) (h₁ h₂ : Z ⟶ F) (u : X.left ⟶ Z.left)
    (φ : (A.X ⊗ A.X).left ⟶ (F ⊗ F).left)
    (hφ₁ : φ ≫ (fst F F).left = (fst A.X A.X).left ≫ g)
    (hφ₂ : φ ≫ (snd F F).left = (snd A.X A.X).left ≫ g)
    (e₁ : f₁.left ≫ g = u ≫ h₁.left) (e₂ : f₂.left ≫ g = u ≫ h₂.left) :
    (lift f₁ f₂).left ≫ φ = u ≫ (lift h₁ h₂).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    change (lift f₁ f₂).left ≫ φ ≫ (fst F F).left = u ≫ (lift h₁ h₂).left ≫ (fst F F).left
    rw [hφ₁, ← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst, e₁]
  · simp only [Category.assoc]
    change (lift f₁ f₂).left ≫ φ ≫ (snd F F).left = u ≫ (lift h₁ h₂).left ≫ (snd F F).left
    rw [hφ₂, ← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd, e₂]

/-! ## §6 A family with object fibres is an abelian scheme with `𝒪`-action (from the rigidity leaf) -/

/-- **Main construction.** Over a reduced locally noetherian `S`, a `QMFamily` with reduced total
space all of whose field fibres are objects (`QML3`) underlies a `QMAbScheme`. The group law and
(a), (b) come from `MumfordRigidity`; the ring-homomorphism and level identities are checked on
field points (`hom_ext_pts`). -/
theorem exists_qmAbScheme (hR : MumfordRigidity) {S : Scheme.{0}} [IsReduced S]
    [IsLocallyNoetherian S] (𝒜 : QMFamily S) [IsReduced 𝒜.F.left]
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 t P) :
    ∃ 𝒜' : QMAbScheme S, 𝒜'.toQMFamily = 𝒜 := by
  have := 𝒜.proper
  have := 𝒜.smooth
  have hsm : Smooth 𝒜.F.hom := SmoothOfRelativeDimension.smooth 2 _
  have hgc := geomConn_of_fibres 𝒜 hfib
  obtain ⟨G, hη, ha, hb⟩ := hR S 𝒜.F (𝒜.eta 0) inferInstance 𝒜.proper hsm hgc (𝒜.eta_sec 0)
    (fun K _ s => by
      obtain ⟨P, g, hpb, -, he⟩ := hfib K s
      exact ⟨P.A, g, hpb, one_left_comp he⟩)
  -- `η(0)` is fixed by every `ι(a)`
  have hιe : ∀ a : O, 𝒜.eta 0 ≫ 𝒜.iota a = 𝒜.eta 0 := fun a => by
    refine sec_ext 𝒜 hfib _ _ (by rw [Category.assoc, 𝒜.iota_over])
      (fun K _ t P g hpb hι he => ?_)
    have h0 : t ≫ 𝒜.eta 0 = (1 : P.A.Pt K).left ≫ g := (one_left_comp he).symm
    rw [← Category.assoc t, h0]
    erw [Category.assoc, ← hι a, ← Over.comp_left_assoc, MonObj.one_comp]
  have hone : 𝒜.iota 1 = 𝟙 _ := F_ext 𝒜 hfib _ _ (by rw [𝒜.iota_over, Category.id_comp])
    (fun K _ t P g hpb hι he => by
      rw [← hι 1, map_one, Category.comp_id]
      show (𝟙 P.A.X : P.A.X ⟶ P.A.X).left ≫ g = g
      simp)
  have hmul : ∀ a b : O, 𝒜.iota (a * b) = 𝒜.iota b ≫ 𝒜.iota a := fun a b =>
    F_ext 𝒜 hfib _ _ (by rw [𝒜.iota_over, Category.assoc, 𝒜.iota_over, 𝒜.iota_over])
      (fun K _ t P g hpb hι he => by
        rw [← Category.assoc g (𝒜.iota b), ← hι b, Category.assoc, ← hι a, ← hι (a * b), map_mul]
        show ((P.q.iota b).hom ≫ (P.q.iota a).hom).left ≫ g = _
        rw [Over.comp_left, Category.assoc])
  have hadd : ∀ a b : O, (Over.homMk (𝒜.iota (a + b)) (𝒜.iota_over _) : 𝒜.F ⟶ 𝒜.F) =
      Over.homMk (𝒜.iota a) (𝒜.iota_over a) * Over.homMk (𝒜.iota b) (𝒜.iota_over b) :=
    fun a b => by
      apply Over.OverMorphism.ext
      refine F_ext 𝒜 hfib _ _ (by rw [Over.w, Over.w])
        (fun K _ t P g hpb hι he => ?_)
      obtain ⟨φ, hφ₁, hφ₂, hφμ⟩ := hb K t P.A g ⟨hpb, one_left_comp he⟩
      change g ≫ 𝒜.iota (a + b) = _
      rw [← hι (a + b), map_add, AbVar.Hom.hom_add,
        CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def, Over.comp_left, Over.comp_left,
        Category.assoc, hφμ,
        reassoc_of% (lift_comp_φ _ _ (Over.homMk (𝒜.iota a) (𝒜.iota_over a) : 𝒜.F ⟶ 𝒜.F)
          (Over.homMk (𝒜.iota b) (𝒜.iota_over b)) g φ hφ₁ hφ₂ (hι a) (hι b))]
  have headd : ∀ a b : O,
      (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta (a + b)) (𝒜.eta_sec _) : 𝟙_ (Over S) ⟶ 𝒜.F) =
      Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a) *
        Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta b) (𝒜.eta_sec b) := fun a b => by
    apply Over.OverMorphism.ext
    refine sec_ext 𝒜 hfib _ _ (by rw [Over.w, Over.w])
      (fun K _ t P g hpb hι he => ?_)
    obtain ⟨φ, hφ₁, hφ₂, hφμ⟩ := hb K t P.A g ⟨hpb, one_left_comp he⟩
    change t ≫ 𝒜.eta (a + b) = _
    rw [← he (a + b), map_add, toMul_add,
      CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def, Over.comp_left, Over.comp_left,
      Category.assoc, hφμ,
      reassoc_of% (lift_comp_φ _ _ (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a))
        (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta b) (𝒜.eta_sec b)) t φ hφ₁ hφ₂ (he a) (he b))]
    rfl
  have helin : ∀ a b : O, 𝒜.eta (a * b) = 𝒜.eta b ≫ 𝒜.iota a := fun a b => by
    refine sec_ext 𝒜 hfib _ _
      (by rw [𝒜.eta_sec, Category.assoc, 𝒜.iota_over, 𝒜.eta_sec])
      (fun K _ t P g hpb hι he => ?_)
    have hl : Additive.toMul (P.e.eta (a * b)) =
        Additive.toMul (P.e.eta b) ≫ (P.q.iota a).hom := by
      rw [P.e.linear]; rfl
    rw [← he (a * b), hl, Over.comp_left, Category.assoc, hι a, reassoc_of% (he b)]
    rfl
  have hthree : ∀ b : O, 𝒜.eta (3 * b) = 𝒜.eta 0 := fun b =>
    sec_ext 𝒜 hfib _ _ (by rw [𝒜.eta_sec, 𝒜.eta_sec]) (fun K _ t P g hpb hι he => by
      rw [← he (3 * b), ← he 0, (P.e.eq_iff (3 * b) 0).2 ⟨b, by simp⟩])
  have hker : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (a : O),
      s ≫ 𝒜.eta a = s ≫ 𝒜.eta 0 ↔ ∃ b : O, a = 3 * b := by
    intro K _ s a
    obtain ⟨P, g, hpb, hι, he⟩ := hfib K s
    rw [← he a, ← he 0]
    constructor
    · intro h
      have h' : Additive.toMul (P.e.eta a) = Additive.toMul (P.e.eta 0) := by
        apply Over.OverMorphism.ext
        apply hpb.hom_ext h
        rw [Over.w, Over.w]
      obtain ⟨c, hc⟩ := (P.e.eq_iff a 0).1 (Additive.toMul.injective h')
      exact ⟨c, by simpa using hc⟩
    · rintro ⟨b, rfl⟩
      rw [(P.e.eq_iff (3 * b) 0).2 ⟨b, by simp⟩]
  refine ⟨{ 𝒜 with
    grp := G
    geomConn := hgc
    one_eq := hη
    iota_hom := fun a => ha _ (hιe a)
    iota_one := hone
    iota_mul := hmul
    iota_add := hadd
    eta_add := headd
    eta_linear := helin
    eta_three := hthree
    eta_ker := hker }, rfl⟩

/-! ## §7 `R1univProps` from rigidity and the abelian-scheme clause; the clause lists agree -/

/-- Instances for a proper smooth curve `S/ℚ` and a family over it. -/
theorem reduced_of_smooth_curve {S : Over (Spec (CommRingCat.of ℚ))}
    (hs : SmoothOfRelativeDimension 1 S.hom) (𝒜 : QMFamily S.left) :
    IsReduced S.left ∧ IsLocallyNoetherian S.left ∧ IsReduced 𝒜.F.left := by
  have : Smooth S.hom := SmoothOfRelativeDimension.smooth 1 _
  have := 𝒜.smooth
  have : Smooth 𝒜.F.hom := SmoothOfRelativeDimension.smooth 2 _
  exact ⟨isReduced_of_smooth S.hom, LocallyOfFiniteType.isLocallyNoetherian S.hom,
    isReduced_of_smooth (𝒜.F.hom ≫ S.hom)⟩

/-- **(3) `R1univProps` from Mumford's rigidity and the abelian-scheme clause.** -/
theorem r1univProps_of_ab (hR : MumfordRigidity) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (h : R1univAbProps Y Φ) : R1univProps Y Φ := by
  intro S hp hs 𝒜' hfib
  obtain ⟨h1, h2, h3⟩ := reduced_of_smooth_curve hs 𝒜'
  obtain ⟨𝒜, h𝒜⟩ := exists_qmAbScheme hR 𝒜' (fun K _ t => fibre_of_fieldPt 𝒜' hfib t)
  subst h𝒜
  exact h S hp hs 𝒜 hfib

/-- The family of `R1famProps` is an abelian scheme with `𝒪`-action (rigidity). -/
theorem r1famAbProps_of_r1famProps (hR : MumfordRigidity) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (hs : SmoothOfRelativeDimension 1 Y.hom) (h : R1famProps Y Φ) :
    R1famAbProps Y Φ := by
  obtain ⟨𝒜, h𝒜⟩ := h
  obtain ⟨h1, h2, h3⟩ := reduced_of_smooth_curve hs 𝒜
  have hfib : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y), ∃ P : QML3 K,
      IsFibreOf 𝒜 s.left P := by
    intro K _ _ s
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K s)
    exact ⟨P, h𝒜 K s P hP.symm⟩
  obtain ⟨𝒜', rfl⟩ := exists_qmAbScheme hR 𝒜 (fun K _ t => fibre_of_fieldPt 𝒜 hfib t)
  exact ⟨𝒜', h𝒜⟩

/-- **The two clause lists agree under rigidity**: `R1fpProps Y Φ ↔ R1fpPropsAb Y Φ`. -/
theorem r1fpProps_iff_ab (hR : MumfordRigidity) (Y : Over (Spec (CommRingCat.of ℚ)))
    (Φ : PtEquiv Y) : R1fpProps Y Φ ↔ R1fpPropsAb Y Φ :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, r1famAbProps_of_r1famProps hR h2 h5,
      r1univAbProps_of_r1univProps h6⟩,
    fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, r1famProps_of_r1famAbProps h5,
      r1univProps_of_ab hR h6⟩⟩


/-- **`R1fpProps = R1fpPropsAb` under rigidity** (as predicates on `(Y, Φ)`): every Prop stated on
`R1fpProps`, in any position, is equivalent to the same text with `R1fpPropsAb`. -/
theorem r1fpProps_eq_ab' (hR : MumfordRigidity) :
    (R1fpProps : (Y : Over (Spec (CommRingCat.of ℚ))) → PtEquiv Y → Prop) = R1fpPropsAb :=
  funext fun Y => funext fun Φ => propext (r1fpProps_iff_ab hR Y Φ)

/-- **Abelian-scheme form of `LeafQM.AV.R1fp`** (leaf R1fp of leaf-qm-fp): its text with `R1fpProps`
replaced by `R1fpPropsAb`. -/
def R1fpAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpPropsAb Y Φ

/-- **Abelian-scheme form of `LeafQM.AV.R1R2fp`**: its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def R1R2fpAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpPropsAb Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧
      CMExists X Ψ ∧ R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

theorem r1fp_iff_ab (hR : MumfordRigidity) : R1fp ↔ R1fpAb := by
  unfold R1fp R1fpAb
  rw [r1fpProps_eq_ab' hR]

theorem r1R2fp_iff_ab (hR : MumfordRigidity) : R1R2fp ↔ R1R2fpAb := by
  unfold R1R2fp R1R2fpAb
  rw [r1fpProps_eq_ab' hR]


/-! ## §8 Clause (b) of the leaf from its printed core and the kernel's field rigidity -/

/-- **LEAF (Mumford's rigidity, printed core)**: `MumfordRigidity` without clause (b), i.e. *GIT*
Thm. 6.14 (the abelian-scheme structure with identity `e`, on each connected component) and Cor. 6.4
over `S` (clause (a)). Numbers UNVERIFIED, see `MumfordRigidity`. -/
def MumfordRigidityCore : Prop :=
  ∀ (S : Scheme.{0}) (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → IsProper F.hom →
    Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e ∧ (∀ f : F ⟶ F, e ≫ f.left = e → IsMonHom f)

open scoped CategoryTheory.Obj in
/-- **Clause (b), proved**: for a group object `F` of `Over S`, proper and smooth, every
identification `g : A ≅ F_s` of an abelian variety with a fibre carrying identity to identity is a group
homomorphism. The base change `F_s = (Over.pullback s).obj F` is an abelian variety (its group law is
Mathlib's `Functor.grpObjObj`), `A ≅ F_s` over `K` (`IsPullback.isoPullback`) preserves identities, so
it is a homomorphism by the kernel's `G0FibreSimple.rigidityHom` (Mumford, *Abelian varieties*, §4
Cor. 1, proved from Mathlib). -/
theorem isGrpFibre_of_rigidity {S : Scheme.{0}} (F : Over S) [GrpObj F] [IsProper F.hom]
    [Smooth F.hom] {K : Type} [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K)
    (g : A.X.left ⟶ F.left) (h : IsAbVarFibre F η[F].left s A g) : IsGrpFibre F A g := by
  obtain ⟨hpb, h1⟩ := h
  let Fs : Over (Spec (CommRingCat.of K)) := (Over.pullback s).obj F
  have : IsProper Fs.hom := by dsimp [Fs]; infer_instance
  have : Smooth Fs.hom := by dsimp [Fs]; infer_instance
  let eA : A.X ≅ Fs := Over.isoMk hpb.isoPullback (by simp [Fs])
  have : GeometricallyIntegral Fs.hom := by
    have e : eA.inv.left ≫ A.X.hom = Fs.hom := Over.w eA.inv
    have : MorphismProperty.RespectsIso (C := Scheme) @GeometricallyIntegral := by
      rw [GeometricallyIntegral.eq_geometrically]; infer_instance
    rw [← e]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral eA.inv.left
      A.X.hom).2 inferInstance
  let AF : AbVar K := ⟨Fs⟩
  have hg : eA.hom.left ≫ pullback.fst F.hom s = g := hpb.isoPullback_hom_fst
  have h1' : η[A.X].left ≫ g = s ≫ η[F].left := by
    rw [← h1]
    change _ = ((toUnit (AbVar.ptObj (K := K) K)) ≫ η[A.X]).left ≫ g
    rw [Over.comp_left, Over.toUnit_left]
    simp [AbVar.ptObj, Algebra.algebraMap_self]
  have hη : η[A.X] ≫ eA.hom = η[AF.X] := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [Over.comp_left, Category.assoc, hg, h1']
      change s ≫ η[F].left = (Functor.LaxMonoidal.ε (Over.pullback s) ≫
        (Over.pullback s).map η[F]).left ≫ pullback.fst F.hom s
      have hs : inv (pullback.snd (𝟙 S) s) ≫ pullback.fst (𝟙 S) s = s := by
        rw [IsIso.inv_comp_eq, ← pullback.condition, Category.comp_id]
      simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst,
        Over.ε_pullback_left]
      rw [← Category.assoc]
      erw [hs]
    · exact (Over.w (η[A.X] ≫ eA.hom)).trans (Over.w η[AF.X]).symm
  have hmon : IsMonHom eA.hom := G0FibreSimple.rigidityHom K A AF eA.hom hη
  refine ⟨(eA.hom ⊗ₘ eA.hom).left ≫ (Functor.LaxMonoidal.μ (Over.pullback s) F F).left ≫
    pullback.fst _ _, ?_, ?_, ?_⟩
  · change _ ≫ pullback.fst F.hom F.hom = _
    rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst, ← Category.assoc]
    change ((eA.hom ⊗ₘ eA.hom).left ≫ (fst Fs Fs).left) ≫ pullback.fst F.hom s = _
    rw [← Over.comp_left, tensorHom_fst, Over.comp_left, Category.assoc, hg]
  · change _ ≫ pullback.snd F.hom F.hom = _
    rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd, ← Category.assoc]
    change ((eA.hom ⊗ₘ eA.hom).left ≫ (snd Fs Fs).left) ≫ pullback.fst F.hom s = _
    rw [← Over.comp_left, tensorHom_snd, Over.comp_left, Category.assoc, hg]
  · have hm : μ[A.X] ≫ eA.hom = (eA.hom ⊗ₘ eA.hom) ≫ μ[AF.X] := IsMonHom.mul_hom eA.hom
    rw [← hg, ← Over.comp_left_assoc, hm]
    change ((eA.hom ⊗ₘ eA.hom) ≫ Functor.LaxMonoidal.μ (Over.pullback s) F F ≫
      (Over.pullback s).map μ[F]).left ≫ pullback.fst F.hom s = _
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]

/-- **`MumfordRigidity` from its printed core** (clause (b) by `isGrpFibre_of_rigidity`). -/
theorem mumfordRigidity_of_core (hC : MumfordRigidityCore) : MumfordRigidity := by
  intro S F e hN hP hS hG he hfib
  obtain ⟨G, hη, ha⟩ := hC S F e hN hP hS hG he hfib
  refine ⟨G, hη, ha, fun K _ s A g hg => ?_⟩
  rw [← hη] at hg
  exact isGrpFibre_of_rigidity F s A g hg

/-- **(3) with the printed core of the leaf**: `R1univProps` from *GIT* Thm. 6.14 + Cor. 6.4
(`MumfordRigidityCore`) and the abelian-scheme clause. -/
theorem r1univProps_of_core_ab (hC : MumfordRigidityCore) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (h : R1univAbProps Y Φ) : R1univProps Y Φ :=
  r1univProps_of_ab (mumfordRigidity_of_core hC) h

/-- The clause lists agree under the printed core of the leaf. -/
theorem r1fpProps_iff_ab_core (hC : MumfordRigidityCore) (Y : Over (Spec (CommRingCat.of ℚ)))
    (Φ : PtEquiv Y) : R1fpProps Y Φ ↔ R1fpPropsAb Y Φ :=
  r1fpProps_iff_ab (mumfordRigidity_of_core hC) Y Φ

end R1UnivRigid

end AV

end LeafQM

/-! # Part A2: verbatim copy of scratch/c-to-printed/Shimura.lean (without its import line) -/


/-!
# shimura-split, Part 4: `ShimuraFamily` (row shimuraFamily) from Shimura's holomorphic family

The row `HDec.QMSplit.Moduli.ShimuraFamily` asks, on one fine witness `(Y, Φ)`, for every algebraic
`π : Y → P¹` a family `τ ↦ y_τ ∈ Y(ℂ)` with the moduli clause (the object at `y_τ` is `ℂ²/ι(𝒪)(τ,1)ᵀ`) and
`τ ↦ π(y_τ)` continuous and holomorphic into `P¹(ℂ)`. qm-split flagged it as Shimura's Main Theorem I
**plus** a GAGA-level step (an algebraic map composed with a holomorphic family is holomorphic).

Here Shimura's statement is a leaf in its own form: **one** family `τ ↦ y_τ` (independent of `π`) with the
moduli clause which is *holomorphic*, where "holomorphic map `ℍ → Y(ℂ)`" is the standard notion written
with the regular functions of `Y`: preimages of Zariski opens are open, and every regular function on a
Zariski open pulls back to a holomorphic function (`IsHolFamily`). The step to every `π : Y → P¹` is proved
in Lean (`ShimuraSplit.holP1_of_isHolFamily`): it only uses the two charts of `π`.
-/

set_option linter.all false

noncomputable section

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits Filter Topology
open LeafQM.AV

variable {X : Scheme.{0}}

/-- The point of `X` under a `ℂ`-point. -/
abbrev ptC (y : Spec (CommRingCat.of ℂ) ⟶ X) : X := (Scheme.SpecToEquivOfField ℂ X y).1

open Classical in
/-- The value `f(y) ∈ ℂ` of a regular function `f ∈ Γ(X, U)` at a `ℂ`-point `y` whose point lies in `U`
(the image of `f(x) ∈ κ(x)` under the embedding `κ(x) → ℂ` of `y`), and `0` otherwise. -/
def regVal (U : X.Opens) (f : Γ(X, U)) (y : Spec (CommRingCat.of ℂ) ⟶ X) : ℂ :=
  if h : ptC y ∈ U then (Scheme.SpecToEquivOfField ℂ X y).2 (X.evaluation U _ h f) else 0

/-- **A holomorphic map `ℍ → X(ℂ)`**, written with the regular functions of `X`: the preimage of every
Zariski open is open, and every regular function on a Zariski open `U` pulls back to a function holomorphic
(analytic) on the preimage of `U`. For a variety this is the usual notion (an affine open embeds in `ℂ^n`
by finitely many regular functions, and the analytic topology is the one induced from `ℂ^n`). -/
def IsHolFamily (φ : UpperHalfPlane → (Spec (CommRingCat.of ℂ) ⟶ X)) : Prop :=
  (∀ U : X.Opens, IsOpen {τ | ptC (φ τ) ∈ U}) ∧
  ∀ (U : X.Opens) (f : Γ(X, U)) (τ : UpperHalfPlane), ptC (φ τ) ∈ U →
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, regVal U f (φ ⟨z, hz⟩) = g z

/-! ## The two charts of `π` -/

theorem val_of_mem (π : ToP1 X) (y : Spec (CommRingCat.of ℂ) ⟶ X) (h : ptC y ∈ π.U) :
    π.val y = ((regVal π.U π.f y : ℂ) : OnePoint ℂ) := by
  unfold ToP1.val regVal
  rw [dif_pos h, dif_pos h]

theorem eval_res {U U' : X.Opens} (i : U' ⟶ U) (x : X) (hx : x ∈ U') (f : Γ(X, U)) :
    X.evaluation U' x hx (X.presheaf.map i.op f) = X.evaluation U x (i.le hx) f := by
  simp only [Scheme.evaluation, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

theorem val_of_memV (π : ToP1 X) (y : Spec (CommRingCat.of ℂ) ⟶ X) (hV : ptC y ∈ π.V) :
    π.val y = if regVal π.V π.g y = 0 then OnePoint.infty
      else (((regVal π.V π.g y)⁻¹ : ℂ) : OnePoint ℂ) := by
  have hreg : regVal π.V π.g y =
      (Scheme.SpecToEquivOfField ℂ X y).2 (X.evaluation π.V (ptC y) hV π.g) := by
    unfold regVal; rw [dif_pos hV]
  rw [hreg]
  by_cases hg : X.evaluation π.V (ptC y) hV π.g = 0
  · have hxU : ptC y ∉ π.U := by
      intro hU
      have := (Scheme.evaluation_eq_zero_iff_notMem_basicOpen X (ptC y) hV π.g).1 hg
      rw [π.basicOpen_g] at this
      exact this ⟨hU, hV⟩
    rw [hg, map_zero, if_pos rfl]
    unfold ToP1.val
    rw [dif_neg hxU]
  · have hmem : ptC y ∈ X.basicOpen π.g :=
      (Scheme.evaluation_ne_zero_iff_mem_basicOpen X (ptC y) hV π.g).1 hg
    rw [π.basicOpen_g] at hmem
    have hU : ptC y ∈ π.U := hmem.1
    have hι0 : (Scheme.SpecToEquivOfField ℂ X y).2 (X.evaluation π.V (ptC y) hV π.g) ≠ 0 := by
      intro h0
      exact hg ((Scheme.SpecToEquivOfField ℂ X y).2.hom.injective (h0.trans (map_zero _).symm))
    rw [if_neg hι0]
    unfold ToP1.val
    rw [dif_pos hU]
    congr 1
    have hinv := congrArg (X.evaluation (π.U ⊓ π.V) (ptC y) hmem) π.inv
    rw [map_mul, map_one, eval_res, eval_res] at hinv
    have h2 := congrArg (Scheme.SpecToEquivOfField ℂ X y).2 hinv
    rw [map_mul, map_one] at h2
    exact eq_inv_of_mul_eq_one_left h2

/-! ## Topology on `ℍ` versus `ℂ` -/

theorem eventually_of_complex {P : UpperHalfPlane → Prop} {τ : UpperHalfPlane}
    (h : ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, P ⟨z, hz⟩) : ∀ᶠ σ in 𝓝 τ, P σ :=
  ((UpperHalfPlane.continuous_coe.tendsto τ).eventually h).mono fun σ hσ => hσ σ.im_pos

theorem complex_of_eventually {P : UpperHalfPlane → Prop} {τ : UpperHalfPlane}
    (h : ∀ᶠ σ in 𝓝 τ, P σ) : ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, P ⟨z, hz⟩ := by
  rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq τ, Filter.eventually_map]
  exact h.mono fun σ hσ hz => hσ

/-- `w ↦ 1/w` as a map `ℂ → P¹(ℂ)` (`0 ↦ ∞`) is continuous at `0`. -/
theorem tendsto_invP1 :
    Tendsto (fun w : ℂ => if w = 0 then (OnePoint.infty : OnePoint ℂ) else ((w⁻¹ : ℂ) : OnePoint ℂ))
      (𝓝 0) (𝓝 OnePoint.infty) := by
  rw [← nhdsNE_sup_pure (0 : ℂ)]
  refine Tendsto.sup ?_ ?_
  · have h1 : Tendsto (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 OnePoint.infty) := by
      have hc := OnePoint.tendsto_coe_infty (X := ℂ)
      rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at hc
      exact hc.comp tendsto_inv₀_nhdsNE_zero
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (if_neg hw).symm
  · rw [tendsto_pure_left]
    intro s hs
    rw [if_pos rfl]
    exact mem_of_mem_nhds hs

/-! ## The GAGA-level step: every `π : X → P¹` composed with a holomorphic family -/

/-- **For a holomorphic family `φ` and every `π : X → P¹` (by charts), `τ ↦ π(φ τ)` is continuous and
holomorphic into `P¹(ℂ)` at every point.** -/
theorem holP1_of_isHolFamily (π : ToP1 X) {φ : UpperHalfPlane → (Spec (CommRingCat.of ℂ) ⟶ X)}
    (hφ : IsHolFamily φ) :
    Continuous (fun τ => π.val (φ τ)) ∧
      ∀ τ, HDec.HSyn.G0Split.FibreQM.IsHolP1At (fun τ => π.val (φ τ)) τ := by
  obtain ⟨hopen, hhol⟩ := hφ
  -- the local description at each `τ`
  have key : ∀ τ : UpperHalfPlane,
      (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, π.val (φ ⟨z, hz⟩) = ((g z : ℂ) : OnePoint ℂ)) ∨
      (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧ g τ = 0 ∧
        ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im,
          π.val (φ ⟨z, hz⟩) = if g z = 0 then OnePoint.infty else (((g z)⁻¹ : ℂ) : OnePoint ℂ)) := by
    intro τ
    by_cases hU : ptC (φ τ) ∈ π.U
    · left
      obtain ⟨g, hg, hev⟩ := hhol π.U π.f τ hU
      have hU' := complex_of_eventually (P := fun σ => ptC (φ σ) ∈ π.U)
        ((hopen π.U).mem_nhds hU)
      refine ⟨g, hg, ?_⟩
      filter_upwards [hev, hU'] with z h1 h2 hz
      rw [val_of_mem π _ (h2 hz), h1 hz]
    · right
      have hV : ptC (φ τ) ∈ π.V := by
        have : ptC (φ τ) ∈ π.U ⊔ π.V := by rw [π.cover]; trivial
        rcases (TopologicalSpace.Opens.mem_sup).1 this with h | h
        · exact absurd h hU
        · exact h
      obtain ⟨g, hg, hev⟩ := hhol π.V π.g τ hV
      have hV' := complex_of_eventually (P := fun σ => ptC (φ σ) ∈ π.V)
        ((hopen π.V).mem_nhds hV)
      refine ⟨g, hg, ?_, ?_⟩
      · have h0 := hev.self_of_nhds τ.im_pos
        rw [← h0]
        have hτ : (⟨(τ : ℂ), τ.im_pos⟩ : UpperHalfPlane) = τ := rfl
        rw [hτ]
        unfold regVal
        rw [dif_pos hV]
        have hnot : ptC (φ τ) ∉ X.basicOpen π.g := by
          rw [π.basicOpen_g]; exact fun h => hU h.1
        rw [(Scheme.evaluation_eq_zero_iff_notMem_basicOpen X _ hV π.g).2 hnot, map_zero]
      · filter_upwards [hev, hV'] with z h1 h2 hz
        rw [val_of_memV π _ (h2 hz), h1 hz]
  refine ⟨continuous_iff_continuousAt.2 fun τ => ?_, fun τ => key τ⟩
  rcases key τ with ⟨g, hg, hev⟩ | ⟨g, hg, hg0, hev⟩
  · have hc : ContinuousAt (fun σ : UpperHalfPlane => ((g σ : ℂ) : OnePoint ℂ)) τ :=
      OnePoint.continuous_coe.continuousAt.comp
        (hg.continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt)
    exact hc.congr (eventually_of_complex (P := fun σ => ((g σ : ℂ) : OnePoint ℂ) = π.val (φ σ))
      (hev.mono fun z hz hz' => (hz hz').symm))
  · have hc : ContinuousAt (fun σ : UpperHalfPlane =>
        if g σ = 0 then (OnePoint.infty : OnePoint ℂ) else (((g σ)⁻¹ : ℂ) : OnePoint ℂ)) τ := by
      have ht := hg.continuousAt.comp (UpperHalfPlane.continuous_coe.continuousAt (x := τ))
      unfold ContinuousAt at ht ⊢
      have hgτ : (g ∘ (fun σ : UpperHalfPlane => (σ : ℂ))) τ = 0 := hg0
      rw [hgτ] at ht
      have hval : (if g τ = 0 then (OnePoint.infty : OnePoint ℂ) else (((g τ)⁻¹ : ℂ) : OnePoint ℂ)) =
          OnePoint.infty := by rw [if_pos hg0]
      dsimp only
      rw [hval]
      exact tendsto_invP1.comp ht
    exact hc.congr (eventually_of_complex
      (P := fun σ => (if g σ = 0 then (OnePoint.infty : OnePoint ℂ) else (((g σ)⁻¹ : ℂ) : OnePoint ℂ)) =
        π.val (φ σ))
      (hev.mono fun z hz hz' => (hz hz').symm))

end ShimuraSplit

namespace HDec

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

namespace FibreQM

open _root_.ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open Complex

/-- **Shimura's holomorphic family on a witness** (the moduli clause of `IsR1bFamily`, copied verbatim, and
holomorphy of `τ ↦ y_τ` in the sense of `ShimuraSplit.IsHolFamily`; no map to `P¹` involved). -/
def IsShimuraHolFamily (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y)) : Prop :=
  (∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (yτ τ) = M3.mk P ∧
    ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      IotaCompatible P Φu) ∧
  ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (yτ τ).left)

/-- **The GAGA-level step, proved**: a holomorphic family with the moduli clause is an `R1bFamily` family for
every `π : Y → P¹`. -/
theorem isR1bFamily_of_hol {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y)} (h : IsShimuraHolFamily Y Φ yτ) (π : ToP1 Y.left) :
    IsR1bFamily Y Φ π yτ :=
  ⟨h.1, ShimuraSplit.holP1_of_isHolFamily π h.2⟩

end FibreQM

end G0Split

end HSyn

end HDec

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF (Shimura's complex uniformization of the canonical model, Main Theorem I).**

*Published statement* (Shimura, Ann. of Math. 85 (1967), Main Theorem I; Deligne, Sém. Bourbaki 389 (1971),
§4.15; locators UNVERIFIED, no network): the canonical model `V` of `Γ\ℍ` carries a holomorphic map
`φ : ℍ → V(ℂ)` whose value at `τ` is the moduli point of `ℂ²/ι(𝒪)(τ, 1)ᵀ` (with its `ι` and level
structure).

*Lean form*: some fine witness `(Y, Φ)` (the canonical model `Y₃`) has `τ ↦ y_τ ∈ Y(ℂ)` with the object at
`y_τ` equal (by an `ι`-compatible analytic uniformization with kernel `Λ_τ = ι(𝒪)(τ,1)ᵀ`) to `ℂ²/Λ_τ`, and
`τ ↦ y_τ` holomorphic (`ShimuraSplit.IsHolFamily`: preimages of Zariski opens are open and regular
functions pull back to holomorphic functions, the standard notion for maps into the complex points of a
variety).

*Form*: a **consequence** of Main Thm I (one holomorphic `φ`, as here), not its printed form: Shimura's
`V` for the level-3 group is one geometric component, defined over `ℚ(ζ₃)`, while `Y₃` over `ℚ` has two; the
moduli clause on `Y₃` comes through Deligne's adelic reformulation (§4) with R1 and Lemma QP (independent
review, shimura-split §3.4). The row's "for every `π : Y → P¹`" is derived (`isR1bFamily_of_hol`), so the
flagged GAGA-level composition step is no longer part of the leaf. -/
def ShimuraHolFamily : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ yτ

/-- **Row `shimuraFamily` from Shimura's holomorphic family.** -/
theorem shimuraFamily_of_hol (h : ShimuraHolFamily) : ShimuraFamily := by
  obtain ⟨Y, Φ, h1, yτ, hy⟩ := h
  exact ⟨Y, Φ, h1, fun π => ⟨yτ, HSyn.G0Split.FibreQM.isR1bFamily_of_hol hy π⟩⟩

end HDec.QMSplit.Moduli

#print axioms ShimuraSplit.holP1_of_isHolFamily
#print axioms HDec.QMSplit.Moduli.shimuraFamily_of_hol

example : HDec.QMSplit.Moduli.ShimuraHolFamily → HDec.QMSplit.Moduli.ShimuraFamily :=
  HDec.QMSplit.Moduli.shimuraFamily_of_hol

/-! # c-to-printed, Part H: `shimuraFamily`

Everything above is a verbatim copy of `scratch/shimura-split/ShimuraFam.lean` (shimura-split; it still
compiles against the e38375b3 kernel). Below: the fullest form of Shimura's Main Theorem I that can be stated
over the kernel's and Mathlib's definitions, and the field from it. -/

namespace CToPrinted.Shimura

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- Verbatim copy of the field statement `HDec.QMSplit.Moduli.ShimuraFamily`
(`ZInQKernel/OneProof/H/TailU.lean`). -/
def ShimuraFamily : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1fpProps Y Φ ∧
    ∀ π : ToP1 Y.left, HDec.HSyn.G0Split.FibreQM.R1bFamily Y Φ π

example : ShimuraFamily = HDec.QMSplit.Moduli.ShimuraFamily := rfl

/-- `x ∈ Γ(3) = {x ∈ 𝒪 : nrd x = 1, x ≡ 1 mod 3𝒪}`, the group `Γ_S = B^×_+ ∩ K₃` of the level-3 structure
(`nrd x = x x̄`; units of `𝒪` have `nrd = ±1`, and the positive ones act on `ℍ`). -/
def InGamma3 (x : LeafQM.B) : Prop :=
  LeafQM.InO x ∧ x * star x = 1 ∧ ∃ y : LeafQM.B, LeafQM.InO y ∧ x = 1 + 3 * y

/-- **LEAF `ShimuraMainThmIY3`** (Shimura, Ann. of Math. 85 (1967), Main Theorem I, without its
reciprocity law; with the moduli interpretation of `φ_S` (Shimura 1967 §§2-3 and Ann. of Math. 78 (1963);
Deligne, Sém. Bourbaki 389 (1971), §4); locators recalled, UNVERIFIED).

*Printed* (as recalled): for `S = K₃`, the canonical model `(V_S, φ_S)` over `k_S` (for `K₃`, `ℚ(ζ₃)`):
`V_S` a smooth projective curve, `φ_S : ℍ → V_S(ℂ)` holomorphic, inducing a biholomorphic
`Γ_S\ℍ ≅ V_S(ℂ)`, and Shimura's reciprocity law at the CM points. In the moduli construction, `φ_S(τ)` is the
moduli point of `(ℂ²/Λ_τ, ι, η_τ)`, `Λ_τ = ι(𝒪)(τ,1)ᵀ`, `η_τ(a) = ι(a)(τ,1)ᵀ/3`.

*Lean form*: on a fine witness `(Y, Φ)` (`R1fpProps`; `V_S` is one geometric component of `Y₃`), a map
`τ ↦ y_τ ∈ Y(ℂ)` with the moduli clause and holomorphic (`IsShimuraHolFamily`, shimura-split), whose fibres
are exactly the `Γ(3)`-orbits (injectivity of `Γ_S\ℍ → V_S(ℂ)`; invariance: `Λ_{γτ} = Λ_τ/(cτ+d)` and
`η_{γτ} = η_τ` up to that scalar iff `γ ≡ 1 mod 3𝒪`). Dropped (not statable over Mathlib 4.35): the
reciprocity law, which needs the Artin map `[s, K] : 𝔸_K^× → Gal(K^ab/K)` of an imaginary quadratic `K`
(Mathlib has no global class field theory), and the surjectivity onto `V_S(ℂ)`, which needs the canonical
model `V_S` over `k_S` as a separate object together with Deligne's comparison `Y₃ ⊗ ℚ(ζ₃) = V_S ⊔ V_S^σ`. -/
def ShimuraMainThmIY3 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1fpProps Y Φ ∧
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), HDec.HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ yτ ∧
      ∀ τ τ' : UpperHalfPlane, (yτ τ = yτ τ' ↔ ∃ x : LeafQM.B, InGamma3 x ∧
        ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = BPAnalytic.QM.iota x ∧ g • τ = τ')

/-- shimura-split's leaf from the fuller form (drop the orbit clause). -/
theorem shimuraHolFamily_of_mainThmI (h : ShimuraMainThmIY3) : HDec.QMSplit.Moduli.ShimuraHolFamily := by
  obtain ⟨Y, Φ, h1, yτ, hy, -⟩ := h
  exact ⟨Y, Φ, h1, yτ, hy⟩

/-- **The field `shimuraFamily` from `ShimuraMainThmIY3`** (compiled; the composition with every
`π : Y → P¹` is shimura-split's `holP1_of_isHolFamily`). -/
theorem shimuraFamily_of_mainThmI (h : ShimuraMainThmIY3) : HDec.QMSplit.Moduli.ShimuraFamily :=
  HDec.QMSplit.Moduli.shimuraFamily_of_hol (shimuraHolFamily_of_mainThmI h)

end CToPrinted.Shimura

#print axioms CToPrinted.Shimura.shimuraFamily_of_mainThmI

/-! # Part A3: verbatim from scratch/r1univ-rigid/R1UnivLeaves.lean -/


namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.ShimuraFamily`** (row shimuraFamily H-139): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def ShimuraFamilyAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧
    ∀ π : ToP1 Y.left, HSyn.G0Split.FibreQM.R1bFamily Y Φ π

end HDec.QMSplit.Moduli
