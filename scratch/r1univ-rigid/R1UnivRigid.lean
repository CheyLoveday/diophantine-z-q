import ZInQKernel.HDecomp.QM.Leaves
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.SmoothFibre.Basic

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

The level clause is the relative form of the kernel's `Level3`: in characteristic 0 an `𝒪`-linear
`η : (𝒪/3𝒪)_S → A[3]` injective on every geometric fibre is an isomorphism, both sides being finite
étale of degree 81 (`#A_s[3] = 3⁴`, the kernel's `TorsionStructure`), and conversely (STANDARD; the
same argument as `Structures.lean` §2 over a field). Injectivity of `ι` is not required: for `S ≠ ∅`
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

end R1UnivRigid

end AV

end LeafQM
