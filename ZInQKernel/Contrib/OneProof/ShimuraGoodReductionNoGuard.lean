import ZInQKernel.OneProof.H.TailW
import ZInQKernel.OneProof.H.TailZ16

/-!
# sgr-split: `ShimuraGoodReductionNoGuard` from the printed integral model of the Shimura curve

`HDec.CurveSplitGR.ShimuraGoodReductionNoGuard` (field `shimuraGoodReductionNoGuard` of the added bundle,
`ZInQKernel/OneProof/H/TailW.lean`) asserts, for every prime `p > 324`, a proper smooth curve `𝒴/ℤ_(p)` with a
`QMFamily` `𝒜 → 𝒴` whose field fibres are the objects `QML3`, bijective on `ℚ̄`-points onto their classes, with
the Hecke automorphisms for `Aut 𝒪` and `𝒪^×`. curve-split (docs/research/curve-split.md §3.6) found the printed
source (representability of the integral moduli problem) not statable for want of abelian schemes over a base.
The kernel now has them: r1univ-rigid's `LeafQM.AV.R1UnivRigid.QMAbScheme S` (an abelian scheme over `S` with
`𝒪 → End_S` and level 3). Over it the printed theorem is stated here as `ShimuraIntegralModelRep`, and

* `shimuraGoodReductionNoGuard_of_rep : ShimuraIntegralModelRep → QMAbFieldFibre → QML3AsQMAb →
  FibreClassUnique → ShimuraGoodReductionNoGuard` (the clause-by-clause glue: Yoneda for the Hecke clauses,
  uniqueness for injectivity, existence for surjectivity);
* `fibreClassUnique : FibreClassUnique` (proved: the pullback isomorphism of two fibres is a homomorphism by
  the kernel's `G0FibreSimple.rigidityHom`);
* `qml3AsQMAb_of : AbVarSurfaceRelDim → QML3AsQMAb` (proved: an object over a field is a `QMAbScheme` over
  `Spec K` with the same data) and `abVarSurfaceRelDim : AbVarSurfaceRelDim` (proved from the kernel's smooth
  dimension theory: an abelian surface is smooth of relative dimension 2);
* `shimuraGoodReductionNoGuard_of_printed : ShimuraIntegralModelRep → QMAbFieldFibre →
  ShimuraGoodReductionNoGuard`, the discharge.

New hypotheses: the printed leaf `ShimuraIntegralModelRep` (Kottwitz/Buzzard/Morita) and the glue
`QMAbFieldFibre` (fibres of a `QMAbScheme` at field points are objects). Report: docs/research/sgr-split.md.
-/

noncomputable section

namespace SGRSplit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid HDec.VertWitness HDec.CurveSplitGR

/-- **`𝒜'` is the pullback of `𝒜` along `g`, with its `𝒪`-action and level sections**: a morphism
`h : 𝒜' → 𝒜` making `𝒜' → S` the base change of `𝒜 → T` along `g`, carrying `ι'(a)` to `ι(a)` and
`η'(a)` to `η(a)`; i.e. an isomorphism `𝒜' ≅ g^*𝒜` of the data (the relative form of the kernel's
`IsFibreOf`). For `QMAbScheme`s such an isomorphism carries the identity `η'(0)` to `η(0)`, so it is an
isomorphism of abelian schemes (Mumford, *GIT*, Cor. 6.4; number UNVERIFIED): this is the isomorphism relation
of the moduli problem. -/
def QMFamFibre {S T : Scheme.{0}} (𝒜 : QMFamily T) (g : S ⟶ T) (𝒜' : QMFamily S) : Prop :=
  ∃ h : 𝒜'.F.left ⟶ 𝒜.F.left, IsPullback h 𝒜'.F.hom 𝒜.F.hom g ∧
    (∀ a : O, 𝒜'.iota a ≫ h = h ≫ 𝒜.iota a) ∧ (∀ a : O, 𝒜'.eta a ≫ h = g ≫ 𝒜.eta a)

/-- The assertion of `ShimuraIntegralModelRep` at one prime `p`: a proper smooth curve `𝒴/ℤ_(p)` with a
`QMAbScheme` `𝒜` over it that represents the moduli problem on locally noetherian `ℤ_(p)`-schemes. -/
def ShimuraIntegralModelRepAt (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMAbScheme 𝒴.left),
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    ∀ (S : Over (Spec (CommRingCat.of (Zloc p)))), IsLocallyNoetherian S.left →
      ∀ 𝒜' : QMAbScheme S.left, ∃! g : S ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily

/-- **LEAF (printed form; pending reading): the integral model of the level-3 Shimura curve of
discriminant 6.** For each prime `p > 324` the moduli problem `S ↦ {(A, ι, η)}/≅` on locally noetherian
`ℤ_(p)`-schemes `S` (in universe 0) is representable by a proper smooth curve `𝒴/ℤ_(p)`: there is a universal
`𝒜 : QMAbScheme 𝒴` such that every object `𝒜'` over `S` is the pullback of `𝒜` along exactly one
`ℤ_(p)`-morphism `S → 𝒴`. Here `(A, ι, η)` is the kernel's `QMAbScheme S`: `A/S` an abelian scheme of relative
dimension 2 (proper, smooth, geometrically connected, a group object of `Over S`), `ι : 𝒪 → End_S(A)` a unital
ring homomorphism for the maximal order `𝒪` of `B = (2, −3)` (discriminant 6), and `η : 𝒪 → A(S)` an
`𝒪`-linear map killing `3𝒪` and injective mod `3𝒪` on every field fibre.

*Printed sources* (all locators UNVERIFIED; no network; docs/research/locators.md row R1 for Kottwitz):
- R. Kottwitz, *Points on some Shimura varieties over finite fields*, J. AMS 5 (1992), 373–444, §5: the PEL
  moduli problem with neat `K^p` and hyperspecial `K_p` is representable by a smooth quasi-projective scheme over
  `𝒪_E ⊗ ℤ_(p)`, proper when `B` is a division algebra. Here `E = ℚ`, `K_p = 𝒪_p^× ≅ GL₂(ℤ_p)` for `p ∤ 6`,
  `K^p = K₃ × ∏_{ℓ ≠ 3, p} 𝒪_ℓ^×` (full level 3, neat), which covers the level at `3 ∣ D` since `3 ≠ p`.
- K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), 591–612, §1–§4: the
  polarization-free moduli problem of abelian surfaces with `𝒪`-action and level structure, representable by
  a smooth proper curve over `ℤ[1/(D·level)]`.
- Y. Morita, *Reduction modulo 𝔓 of Shimura curves*, Hokkaido Math. J. 10 (1981), 209–238: good reduction of
  the Shimura curve and its universal QM abelian surfaces at `p ∤ D·level`.
- H. Carayol, *Sur la mauvaise réduction des courbes de Shimura*, Compositio Math. 59 (1986), 151–230 (its
  main construction is for totally real `F ≠ ℚ`; secondary).

*Form.* The printed functor has, in Kottwitz's PEL form, a polarization and rational level structures; it is
identified with this one by (i) the relative Lemma P (for the fixed Rosati type the principal polarization of
`(A, ι)` exists and is unique; Boutot–Carayol, Astérisque 196–197 (1991), III §1, UNVERIFIED), (ii) the standard
comparison of `K^p`-orbits of rational level structures with integral ones, (iii) `η` with `eta_three` and
`eta_ker` is the same as an `𝒪`-linear isomorphism `(𝒪/3𝒪)_S ≅ A[3]` because `3` is invertible on `S` (a
fibrewise injective map of finite étale group schemes of the same degree 81 is an isomorphism), (iv) Kottwitz's
determinant condition is automatic for `𝒪 ⊗ ℤ_p ≅ M₂(ℤ_p)`, (v) `QMFamFibre` is the isomorphism relation
(see its docstring). Only `p > 324` is asserted (the printed range is `p ∤ 6`), only locally noetherian `S` in
universe 0. Flagged pending reading: whether Buzzard's or Morita's printed level structures include a prime
dividing `D` (Kottwitz's do), and the comparison (i)–(ii) for the PEL form. -/
def ShimuraIntegralModelRep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p → ShimuraIntegralModelRepAt p

/-- **GLUE G1 (project glue): the fibre of a QM abelian scheme at a field point is an object.** For a
`QMAbScheme` `𝒜` over any `S` and a point `y : Spec K → S` with `K ⊇ ℚ`, some `P : QML3 K` is the fibre of `𝒜`
at `y`. Proof outline (not compiled): the base change `A_y = (Over.pullback y).obj A` is a group object
(Mathlib's `Functor.grpObjObj`), proper and smooth of relative dimension 2 over `K` (base change), geometrically
integral (smooth and geometrically connected over a field; the Mathlib gap: smooth ⇒ geometrically normal, so
connected ⇒ irreducible), of dimension 2 (the kernel's smooth dimension theory), with `ι` restricted to a unital
ring map `𝒪 → End_K(A_y)` (injective as `A_y ≠ 0` and `B` is simple) and `η` restricted to `𝒪 → A_y(K)` with
kernel `3𝒪` (`eta_ker` at `y`). -/
def QMAbFieldFibre : Prop :=
  ∀ (S : Scheme.{0}) (𝒜 : QMAbScheme S) (K : Type) [Field K] [Algebra ℚ K]
    (y : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K, IsFibreOf 𝒜.toQMFamily y P

/-- **GLUE G2: an object over a field is a `QMAbScheme` over `Spec K` with the same data** (so `IsFibreOf`
at `y` is `QMFamFibre` along `y`). Proved from `AbVarSurfaceRelDim` (`qml3AsQMAb_of`). -/
def QML3AsQMAb : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] (P : QML3 K), ∃ 𝒜' : QMAbScheme (Spec (CommRingCat.of K)),
    ∀ (T : Scheme.{0}) (𝒜 : QMFamily T) (y : Spec (CommRingCat.of K) ⟶ T),
      IsFibreOf 𝒜 y P ↔ QMFamFibre 𝒜 y 𝒜'.toQMFamily

/-- **GLUE G3: fibres are unique up to isomorphism**: two objects that are fibres of the same family at the
same field point are isomorphic. Proved (`fibreClassUnique`). -/
def FibreClassUnique : Prop :=
  ∀ (S : Scheme.{0}) (𝒜 : QMFamily S) (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ S)
    (P P' : QML3 K), IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P'

/-! ## Lemmas -/

/-- Morphisms `Spec R → Spec ℤ_(p)` are unique. -/
theorem spec_to_Zloc_ext (p : ℕ) [Fact p.Prime] {R : CommRingCat.{0}}
    (f g : Spec R ⟶ Spec (CommRingCat.of (Zloc p))) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact IsLocalization.ringHom_ext (pIdeal p).primeCompl (RingHom.ext_int _ _)

/-- The ring map `ℤ_(p) → K` to a field of characteristic `0`. -/
def zlocTo (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] : Zloc p →+* K :=
  IsLocalization.lift (M := (pIdeal p).primeCompl) (g := Int.castRingHom K) (fun x => by
    have hx : (x : ℤ) ≠ 0 := fun h => x.2 (by rw [h]; exact Ideal.zero_mem _)
    exact isUnit_iff_ne_zero.2 (by simpa using hx))

/-- Fibres are invariant under isomorphism of objects. -/
theorem isFibreOf_of_iso {S : Scheme.{0}} (𝒜 : QMFamily S) {K : Type} [Field K]
    {y : Spec (CommRingCat.of K) ⟶ S} {P P' : QML3 K} (f : P.Iso P') (h : IsFibreOf 𝒜 y P') :
    IsFibreOf 𝒜 y P := by
  obtain ⟨k, hpb, hι, he⟩ := h
  have hiso : IsIso f.φ.hom.left := ⟨f.ψ.hom.left, by rw [← Over.comp_left, f.left]; rfl,
    by rw [← Over.comp_left, f.right]; rfl⟩
  have sq : IsPullback f.φ.hom.left P.A.X.hom P'.A.X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨f.φ.hom.left ≫ k, by simpa using sq.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
  · have := congrArg CommaMorphism.left (f.equivariant a)
    simp only [Over.comp_left] at this
    simp only [Category.assoc]
    rw [reassoc_of% this, hι]
  · have hl := congrArg Additive.toMul (f.level a)
    simp only [toMul_ofMul] at hl
    rw [← he a, ← hl, Over.comp_left, Category.assoc]


/-! ## Hecke relabelings of a QM abelian scheme -/

/-- `ι ↦ ι ∘ α`, `η ↦ η ∘ α` on a `QMAbScheme`. -/
def twistAb {S : Scheme.{0}} (𝒜 : QMAbScheme S) (α : O ≃+* O) : QMAbScheme S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota a := 𝒜.iota (α a)
  iota_over a := 𝒜.iota_over (α a)
  eta a := 𝒜.eta (α a)
  eta_sec a := 𝒜.eta_sec (α a)
  grp := 𝒜.grp
  geomConn := 𝒜.geomConn
  one_eq := by rw [map_zero]; exact 𝒜.one_eq
  iota_hom a := 𝒜.iota_hom (α a)
  iota_one := by simp only [map_one]; exact 𝒜.iota_one
  iota_mul a b := by simp only [map_mul]; exact 𝒜.iota_mul _ _
  iota_add a b := by
    have h := 𝒜.iota_add (α a) (α b)
    rw [← map_add] at h
    exact h
  eta_add a b := by
    have h := 𝒜.eta_add (α a) (α b)
    rw [← map_add] at h
    exact h
  eta_linear a b := by simp only [map_mul]; exact 𝒜.eta_linear _ _
  eta_three b := by
    simp only [map_mul, map_ofNat, map_zero]
    exact 𝒜.eta_three _
  eta_ker K _ s a := by
    simp only [map_zero]
    rw [𝒜.eta_ker K s (α a)]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨α.symm c, by
        apply α.injective
        rw [hc, map_mul, RingEquiv.apply_symm_apply, map_ofNat]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨α c, by rw [map_mul, map_ofNat]⟩

/-- `η ↦ η(· u)` on a `QMAbScheme`. -/
def rightMulAb {S : Scheme.{0}} (𝒜 : QMAbScheme S) (u : Oˣ) : QMAbScheme S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota := 𝒜.iota
  iota_over := 𝒜.iota_over
  eta a := 𝒜.eta (a * u)
  eta_sec a := 𝒜.eta_sec (a * u)
  grp := 𝒜.grp
  geomConn := 𝒜.geomConn
  one_eq := by rw [zero_mul]; exact 𝒜.one_eq
  iota_hom := 𝒜.iota_hom
  iota_one := 𝒜.iota_one
  iota_mul := 𝒜.iota_mul
  iota_add := 𝒜.iota_add
  eta_add a b := by
    have h := 𝒜.eta_add (a * u) (b * u)
    rw [← add_mul] at h
    exact h
  eta_linear a b := by rw [_root_.mul_assoc]; exact 𝒜.eta_linear _ _
  eta_three b := by rw [_root_.mul_assoc, zero_mul]; exact 𝒜.eta_three _
  eta_ker K _ s a := by
    rw [zero_mul, 𝒜.eta_ker K s (a * u)]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c * ↑u⁻¹, by
        rw [← _root_.mul_assoc, ← hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c * u, by rw [_root_.mul_assoc]⟩

/-- Identity pullback. -/
theorem qmFamFibre_id {S : Scheme.{0}} (𝒜 : QMFamily S) : QMFamFibre 𝒜 (𝟙 S) 𝒜 :=
  ⟨𝟙 _, IsPullback.of_horiz_isIso ⟨by simp⟩, fun a => by simp, fun a => by simp⟩

/-- Composition of relabeled pullbacks. -/
theorem qmFamFibre_comp {S : Scheme.{0}} (𝒜 : QMAbScheme S) (i j i' j' : O → O)
    (g g' : S ⟶ S) (h h' : 𝒜.F.left ⟶ 𝒜.F.left)
    (hpb : IsPullback h 𝒜.F.hom 𝒜.F.hom g) (hpb' : IsPullback h' 𝒜.F.hom 𝒜.F.hom g')
    (hi : ∀ a, 𝒜.iota (i a) ≫ h = h ≫ 𝒜.iota a) (he : ∀ a, 𝒜.eta (j a) ≫ h = g ≫ 𝒜.eta a)
    (hi' : ∀ a, 𝒜.iota (i' a) ≫ h' = h' ≫ 𝒜.iota a) (he' : ∀ a, 𝒜.eta (j' a) ≫ h' = g' ≫ 𝒜.eta a)
    (hii : ∀ a, i (i' a) = a) (hjj : ∀ a, j (j' a) = a) :
    QMFamFibre 𝒜.toQMFamily (g ≫ g') 𝒜.toQMFamily := by
  refine ⟨h ≫ h', hpb.paste_horiz hpb', fun a => ?_, fun a => ?_⟩
  · have := hi (i' a)
    rw [hii] at this
    rw [reassoc_of% this, hi', Category.assoc]
  · have := he (j' a)
    rw [hjj] at this
    rw [reassoc_of% this, he', Category.assoc]


instance zloc_noetherian (p : ℕ) [Fact p.Prime] : IsNoetherianRing (Zloc p) :=
  IsLocalization.isNoetherianRing (pIdeal p).primeCompl _ inferInstance

theorem isLocallyNoetherian_of_smooth (p : ℕ) [Fact p.Prime]
    (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (hsm : SmoothOfRelativeDimension 1 𝒴.hom) :
    IsLocallyNoetherian 𝒴.left := by
  have : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 _
  exact LocallyOfFiniteType.isLocallyNoetherian 𝒴.hom

theorem paste_iota {X Y Z : Scheme.{0}} (e : X ⟶ X) (k : X ⟶ Y) (h : Y ⟶ Z) (ι : Y ⟶ Y)
    (ι' : Z ⟶ Z) (h1 : e ≫ k = k ≫ ι) (h2 : ι ≫ h = h ≫ ι') : e ≫ k ≫ h = (k ≫ h) ≫ ι' := by
  rw [reassoc_of% h1, h2, Category.assoc]

theorem paste_eta {X S Y Z W : Scheme.{0}} (e : X ⟶ Y) (k : Y ⟶ Z) (h : Z ⟶ W) (y : X ⟶ S)
    (η : S ⟶ Z) (g : S ⟶ S') (η' : S' ⟶ W) (h1 : e ≫ k = y ≫ η) (h2 : η ≫ h = g ≫ η') :
    e ≫ k ≫ h = (y ≫ g) ≫ η' := by
  rw [reassoc_of% h1, h2, Category.assoc]

/-! ## The reduction -/

/-- **`ShimuraGoodReductionNoGuard` from the printed representability and three pieces of glue**. -/
theorem shimuraGoodReductionNoGuard_of_rep (hRep : ShimuraIntegralModelRep)
    (g1 : QMAbFieldFibre) (g2 : QML3AsQMAb) (g3 : FibreClassUnique) :
    ShimuraGoodReductionNoGuard := by
  intro p _ hp
  obtain ⟨𝒴, 𝒜, hpr, hsm, hU⟩ := hRep p hp
  have hN := isLocallyNoetherian_of_smooth p 𝒴 hsm
  -- the Hecke automorphism attached to a relabeling with an inverse relabeling
  have hecke : ∀ (𝒜₁ 𝒜₂ : QMAbScheme 𝒴.left) (i j i' j' : O → O),
      𝒜₁.F = 𝒜.F → 𝒜₂.F = 𝒜.F → True := fun _ _ _ _ _ _ _ _ => trivial
  clear hecke
  refine ⟨𝒴, 𝒜.toQMFamily, hpr, hsm, fun K _ _ y => g1 _ 𝒜 K y, ?_, ?_, ?_, ?_⟩
  · -- injectivity on `ℚ̄`-points
    intro y y' P P' hP hP' hPP'
    obtain ⟨𝒜P, h𝒜P⟩ := g2 Qbar P
    obtain ⟨f⟩ := Quotient.exact hPP'
    have hP'' : IsFibreOf 𝒜.toQMFamily y' P := isFibreOf_of_iso _ f hP'
    have hyy : y' ≫ 𝒴.hom = y ≫ 𝒴.hom := spec_to_Zloc_ext p _ _
    obtain ⟨g, -, hg⟩ := hU (Over.mk (y ≫ 𝒴.hom)) (by dsimp; infer_instance) 𝒜P
    have e1 := hg (Over.homMk y rfl) ((h𝒜P _ _ y).mp hP)
    have e2 := hg (Over.homMk y' hyy) ((h𝒜P _ _ y').mp hP'')
    have := congrArg CommaMorphism.left (e1.trans e2.symm)
    simpa using this
  · -- surjectivity on `ℚ̄`-points
    intro P
    obtain ⟨𝒜P, h𝒜P⟩ := g2 Qbar P
    obtain ⟨g, hg, -⟩ := hU (Over.mk (Spec.map (CommRingCat.ofHom (zlocTo p Qbar))))
      (by dsimp; infer_instance) 𝒜P
    exact ⟨g.left, (h𝒜P _ _ g.left).mpr hg⟩
  · -- `Aut(𝒪)`
    intro α
    obtain ⟨g, ⟨h, hpb, hi, he⟩, -⟩ := hU 𝒴 hN (twistAb 𝒜 α)
    obtain ⟨g', ⟨h', hpb', hi', he'⟩, -⟩ := hU 𝒴 hN (twistAb 𝒜 α.symm)
    obtain ⟨g0, -, h0⟩ := hU 𝒴 hN 𝒜
    have hid : QMFamFibre 𝒜.toQMFamily (CommaMorphism.left (𝟙 𝒴)) 𝒜.toQMFamily :=
      qmFamFibre_id _
    have c1 : g ≫ g' = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a => α a) (fun a => α a) (fun a => α.symm a) (fun a => α.symm a)
        g.left g'.left h h' hpb hpb' hi he hi' he' (fun a => by simp) (fun a => by simp)
    have c2 : g' ≫ g = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a => α.symm a) (fun a => α.symm a) (fun a => α a) (fun a => α a)
        g'.left g.left h' h hpb' hpb hi' he' hi he (fun a => by simp) (fun a => by simp)
    refine ⟨⟨g, g', c1, c2⟩, fun y P P' hP hP' => ?_⟩
    rw [M3.twist_mk]
    refine g3 _ _ _ _ _ _ hP' ?_
    obtain ⟨k, hkpb, hki, hke⟩ := hP
    refine ⟨k ≫ h, hkpb.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
    · exact paste_iota _ _ _ _ _ (hki (α a)) (hi a)
    · exact paste_eta _ _ _ _ _ _ _ (hke (α a)) (he a)
  · -- `𝒪^×`
    intro u
    obtain ⟨g, ⟨h, hpb, hi, he⟩, -⟩ := hU 𝒴 hN (rightMulAb 𝒜 u)
    obtain ⟨g', ⟨h', hpb', hi', he'⟩, -⟩ := hU 𝒴 hN (rightMulAb 𝒜 u⁻¹)
    obtain ⟨g0, -, h0⟩ := hU 𝒴 hN 𝒜
    have hid : QMFamFibre 𝒜.toQMFamily (CommaMorphism.left (𝟙 𝒴)) 𝒜.toQMFamily :=
      qmFamFibre_id _
    have c1 : g ≫ g' = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a : O => a) (fun a : O => a * (u : O)) (fun a : O => a)
        (fun a : O => a * ((u⁻¹ : Oˣ) : O)) g.left g'.left h h' hpb hpb' hi he hi' he' (fun a => rfl)
        (fun a => by rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one])
    have c2 : g' ≫ g = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a : O => a) (fun a : O => a * ((u⁻¹ : Oˣ) : O)) (fun a : O => a)
        (fun a : O => a * (u : O)) g'.left g.left h' h hpb' hpb hi' he' hi he (fun a => rfl)
        (fun a => by rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one])
    refine ⟨⟨g, g', c1, c2⟩, fun y P P' hP hP' => ?_⟩
    change M3.mk P' = M3.mk (P.rightMul u)
    refine g3 _ _ _ _ _ _ hP' ?_
    obtain ⟨k, hkpb, hki, hke⟩ := hP
    refine ⟨k ≫ h, hkpb.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
    · exact paste_iota _ _ _ _ _ (hki a) (hi a)
    · exact paste_eta _ _ _ _ _ _ _ (hke (a * u)) (he a)


/-! ## G3 proved: fibres are unique up to isomorphism -/

open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3 in
/-- The identity of a fibre goes to `η(0)` (as in r1univ-rigid's `isGrpFibre_of_rigidity`). -/
theorem eta_left_comp {S : Scheme.{0}} {𝒜 : QMFamily S} {K : Type} [Field K]
    {t : Spec (CommRingCat.of K) ⟶ S} {P : QML3 K} {g : P.A.X.left ⟶ 𝒜.F.left}
    (he : ∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = t ≫ 𝒜.eta a) :
    η[P.A.X].left ≫ g = t ≫ 𝒜.eta 0 := by
  rw [← one_left_comp he]
  change _ = ((toUnit (AbVar.ptObj (K := K) K)) ≫ η[P.A.X]).left ≫ g
  rw [Over.comp_left, Over.toUnit_left]
  simp [AbVar.ptObj, Algebra.algebraMap_self]

open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3 in
/-- **G3 holds** (proved: the pullback isomorphism of two fibres is `𝒪`-equivariant, respects the
level sections, and is a homomorphism by the kernel's `G0FibreSimple.rigidityHom`). -/
theorem fibreClassUnique : FibreClassUnique := by
  intro S 𝒜 K _ y P P' ⟨k, hpb, hι, he⟩ ⟨k', hpb', hι', he'⟩
  let e : P.A.X.left ⟶ P'.A.X.left := hpb'.lift k P.A.X.hom hpb.w
  let e' : P'.A.X.left ⟶ P.A.X.left := hpb.lift k' P'.A.X.hom hpb'.w
  have ek : e ≫ k' = k := hpb'.lift_fst _ _ _
  have eh : e ≫ P'.A.X.hom = P.A.X.hom := hpb'.lift_snd _ _ _
  have ek' : e' ≫ k = k' := hpb.lift_fst _ _ _
  have eh' : e' ≫ P.A.X.hom = P'.A.X.hom := hpb.lift_snd _ _ _
  have ee : e ≫ e' = 𝟙 _ := hpb.hom_ext (by rw [Category.assoc, ek', ek, Category.id_comp])
    (by rw [Category.assoc, eh', eh, Category.id_comp])
  have ee' : e' ≫ e = 𝟙 _ := hpb'.hom_ext (by rw [Category.assoc, ek, ek', Category.id_comp])
    (by rw [Category.assoc, eh, eh', Category.id_comp])
  let φ0 : P.A.X ⟶ P'.A.X := Over.homMk e eh
  let ψ0 : P'.A.X ⟶ P.A.X := Over.homMk e' eh'
  have h0 := eta_left_comp he
  have h0' := eta_left_comp he'
  have hη : η[P.A.X] ≫ φ0 = η[P'.A.X] := by
    apply Over.OverMorphism.ext
    apply hpb'.hom_ext
    · rw [Over.comp_left, Category.assoc]
      change η[P.A.X].left ≫ e ≫ k' = _
      rw [ek, h0, h0']
    · exact (Over.w (η[P.A.X] ≫ φ0)).trans (Over.w η[P'.A.X]).symm
  have hη' : η[P'.A.X] ≫ ψ0 = η[P.A.X] := by
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [Over.comp_left, Category.assoc]
      change η[P'.A.X].left ≫ e' ≫ k = _
      rw [ek', h0, h0']
    · exact (Over.w (η[P'.A.X] ≫ ψ0)).trans (Over.w η[P.A.X]).symm
  have := G0FibreSimple.rigidityHom K P.A P'.A φ0 hη
  have := G0FibreSimple.rigidityHom K P'.A P.A ψ0 hη'
  refine Quotient.sound ⟨⟨AbVar.Hom.mk' φ0, AbVar.Hom.mk' ψ0, ?_, ?_, fun a => ?_, fun a => ?_⟩⟩
  · apply Over.OverMorphism.ext
    simp only [AbVar.Hom.hom_mk', Over.comp_left, Over.id_left]
    exact ee
  · apply Over.OverMorphism.ext
    simp only [AbVar.Hom.hom_mk', Over.comp_left, Over.id_left]
    exact ee'
  · apply Over.OverMorphism.ext
    simp only [AbVar.Hom.hom_mk', Over.comp_left]
    apply hpb'.hom_ext
    · change (P.q.iota a).hom.left ≫ e ≫ k' = e ≫ (P'.q.iota a).hom.left ≫ k'
      rw [ek, hι, hι', reassoc_of% ek]
    · change (P.q.iota a).hom.left ≫ e ≫ P'.A.X.hom = e ≫ (P'.q.iota a).hom.left ≫ P'.A.X.hom
      rw [eh, Over.w, Over.w, eh]
  · apply congrArg Additive.ofMul ?_ |>.trans (ofMul_toMul _)
    apply Over.OverMorphism.ext
    simp only [AbVar.Hom.hom_mk', Over.comp_left]
    apply hpb'.hom_ext
    · change (Additive.toMul (P.e.eta a)).left ≫ e ≫ k' = (Additive.toMul (P'.e.eta a)).left ≫ k'
      rw [ek, he, he']
    · change (Additive.toMul (P.e.eta a)).left ≫ e ≫ P'.A.X.hom =
        (Additive.toMul (P'.e.eta a)).left ≫ P'.A.X.hom
      rw [eh, Over.w, Over.w]


/-! ## G2 from the dimension glue -/

/-- **An abelian surface is smooth of relative dimension 2**: for an abelian variety `A/K` (the kernel's
`PkgI3.AbVar`) whose underlying space has Krull dimension 2, the structure morphism is smooth of relative
dimension 2. (`QML3` records `A.dim = 2`; `QMAbScheme` asks for `SmoothOfRelativeDimension 2`.) Proved below
(`abVarSurfaceRelDim`). -/
def AbVarSurfaceRelDim : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K), A.dim = 2 → SmoothOfRelativeDimension 2 A.X.hom

/-- **`AbVarSurfaceRelDim` holds** (proved from the kernel's smooth dimension theory,
`ZInQKernel/Contrib/Dim/SmoothStalk.lean`): take a standard smooth chart at `x` (Mathlib's
`Smooth.exists_isStandardSmooth`) of relative dimension `d`, and a closed point `z` of the chart (`A` is
Jacobson); then `d = dim 𝒪_{A,z} = dim A = 2` (`ringKrullDim_stalk_of_chart`,
`topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth`, `A` irreducible). -/
theorem abVarSurfaceRelDim : AbVarSurfaceRelDim := by
  intro K _ A hA
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.X.hom
  have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth A.X.hom x
  let _ := (A.X.hom.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of K), U) Γ(A.X.left, V) := h
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h'.out
  have hP := P.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨z, hzV, hzc⟩ := nonempty_inter_closedPoints (Z := (V : Set A.X.left)) ⟨x, hxV⟩
    V.isOpen.isLocallyClosed
  have h1 := (ZInQ.Contrib.Dim.ringKrullDim_stalk_of_chart A.X.hom hV e P.dimension hP z hzV hzc).1
  have h2 := (ZInQ.Contrib.Dim.topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth A.X.hom z hzc).1
  have hd : P.dimension = 2 := by
    have : ((P.dimension : ℕ) : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by
      rw [← h1, ← h2]; exact hA
    exact_mod_cast this
  exact ⟨U, hU, V, hV, hxV, e, hd ▸ hP⟩

open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3 in
theorem ptObj_hom_self (K : Type) [Field K] : (AbVar.ptObj (K := K) K).hom = 𝟙 _ := by
  simp [AbVar.ptObj, Algebra.algebraMap_self]

/-- A morphism `Spec K' → Spec K` of spectra of fields is an epimorphism. -/
theorem epi_spec_field {K K' : Type} [Field K] [Field K']
    (s : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K)) : Epi s := by
  let _ : Algebra K K' := (Spec.preimage s).hom.toAlgebra
  have hs : s = Spec.map (CommRingCat.ofHom (algebraMap K K')) := (Spec.map_preimage s).symm
  rw [hs]
  exact Flat.epi_of_flat_of_surjective _

open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3 in
/-- **G2 from G2a** (proved). -/
theorem qml3AsQMAb_of (hD : AbVarSurfaceRelDim) : QML3AsQMAb := by
  intro K _ _ P
  have hsec : ∀ x : P.A.Pt K, x.left ≫ P.A.X.hom = 𝟙 _ := fun x => by
    rw [Over.w x, ptObj_hom_self]
  let c : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ AbVar.ptObj (K := K) K :=
    Over.homMk (𝟙 _) (by rw [ptObj_hom_self]; rfl)
  have hc : ∀ x : P.A.Pt K, (Over.homMk (U := 𝟙_ (Over (Spec (CommRingCat.of K)))) x.left (hsec x) :
      𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A.X) = c ≫ x := fun x => by
    apply Over.OverMorphism.ext
    exact (Category.id_comp _).symm
  have hio : ∀ f : P.A.X ⟶ P.A.X, (Over.homMk f.left (Over.w f) : P.A.X ⟶ P.A.X) = f := fun f => by
    apply Over.OverMorphism.ext; simp
  let 𝒜' : QMAbScheme (Spec (CommRingCat.of K)) :=
    { F := P.A.X
      proper := inferInstance
      smooth := hD K P.A P.surface
      iota := fun a => (P.q.iota a).hom.left
      iota_over := fun a => Over.w _
      eta := fun a => (Additive.toMul (P.e.eta a)).left
      eta_sec := fun a => hsec _
      grp := P.A.grp
      geomConn := ⟨fun K' _ y Z fst snd h => by
        have : IrreducibleSpace Z :=
          GeometricallyIrreducible.geometrically_irreducibleSpace (f := P.A.X.hom) y fst snd h
        infer_instance⟩
      one_eq := by
        rw [map_zero, toMul_zero]
        change _ = ((toUnit (AbVar.ptObj (K := K) K)) ≫ η[P.A.X]).left
        rw [Over.comp_left, Over.toUnit_left, ptObj_hom_self]; exact (Category.id_comp _).symm
      iota_hom := fun a => by
        rw [hio]; infer_instance
      iota_one := by
        change (P.q.iota 1).hom.left = 𝟙 _
        rw [map_one]; rfl
      iota_mul := fun a b => by
        change (P.q.iota (a * b)).hom.left = (P.q.iota b).hom.left ≫ (P.q.iota a).hom.left
        rw [map_mul]; rfl
      iota_add := fun a b => by
        rw [hio, hio, hio, map_add]; rfl
      eta_add := fun a b => by
        rw [hc, hc, hc, map_add, toMul_add, MonObj.comp_mul]
      eta_linear := fun a b => by
        change (Additive.toMul (P.e.eta (a * b))).left =
          (Additive.toMul (P.e.eta b)).left ≫ (P.q.iota a).hom.left
        rw [P.e.linear]; rfl
      eta_three := fun b => by
        change (Additive.toMul (P.e.eta (3 * b))).left = (Additive.toMul (P.e.eta 0)).left
        rw [(P.e.ker _).mpr ⟨b, rfl⟩, (P.e.ker 0).mpr ⟨0, by simp⟩]
      eta_ker := fun K' _ s a => by
        rw [← P.e.ker a, show P.e.eta 0 = 0 from map_zero _]
        constructor
        · intro h
          have := epi_spec_field s
          have h2 := cancel_epi s |>.mp h
          have h3 : Additive.toMul (P.e.eta a) = Additive.toMul (0 : Additive (P.A.Pt K)) :=
            Over.OverMorphism.ext h2
          exact Additive.toMul.injective h3
        · intro h; rw [h] }
  exact ⟨𝒜', fun T 𝒜 y => Iff.rfl⟩

/-! ## The discharge -/

/-- **`ShimuraGoodReductionNoGuard` from the printed integral model and the fibre glue G1** (compiled;
standard axioms). -/
theorem shimuraGoodReductionNoGuard_of_printed (hRep : ShimuraIntegralModelRep)
    (g1 : QMAbFieldFibre) : ShimuraGoodReductionNoGuard :=
  shimuraGoodReductionNoGuard_of_rep hRep g1 (qml3AsQMAb_of abVarSurfaceRelDim) fibreClassUnique

end SGRSplit
