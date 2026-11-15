import ZInQKernel.OneProof.H.TailZ14

/-! # c-to-printed, Part N: `ReductGlue.NeronLocalizesDVR` from BLR §1.2 Prop. 4 in its printed form

`NeronLocalizesDVR` (field `neronLocalizesDVR` of `OpenResearchLeaves10`) is proved here from
`BLR_1_2_4`, Bosch–Lütkebohmert–Raynaud's Prop. 1.2/4 stated over an arbitrary Dedekind domain and an
arbitrary smooth, separated `R`-scheme of finite type, with the Néron property of BLR §1.2 Def. 1 over
Mathlib's schemes (`IsNeronModelOver`). No group law, no abelian variety, no number field occur in the
leaf. -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace CToPrinted

/-- Verbatim copy of the field statement (`ZInQKernel/OneProof/H/TailZ14.lean`, `ReductGlue`). -/
def NeronLocalizesDVR : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 : ZInQ.DefFaltings.GroupModel A L), 𝒩.IsNeronModel →
    ∀ (O : ValuationSubring L) [IsDiscreteValuationRing O], (ReductGlue.toO 𝒩 O).IsNeronModel

example : NeronLocalizesDVR = ReductGlue.NeronLocalizesDVR := rfl

/-! ## The printed statement -/

/-- **Néron model** (BLR, *Néron models*, §1.2 Def. 1; UNVERIFIED locator). `R` a Dedekind domain with
field of fractions `K`, `X` an `R`-scheme. `X` is a Néron model of its generic fibre `X_K = X ×_R K` when
`X` is smooth, separated and of finite type over `R` and has the Néron mapping property: for every smooth
`R`-scheme `Y`, every `K`-morphism `Y_K → X_K` extends uniquely to an `R`-morphism `Y → X`, i.e.
`Hom_R(Y, X) → Hom_K(Y_K, X_K)`, `f ↦ f_K`, is bijective. (BLR define a Néron model of a given `X_K`;
"`X` is a Néron model of `X_K`" for an `R`-model `X` with generic fibre `X_K` is this predicate, the
identification `X ×_R K ≅ X_K` being transported by composition.) -/
def IsNeronModelOver (R K : Type) [CommRing R] [Field K] [Algebra R K]
    (X : Over (Spec (CommRingCat.of R))) : Prop :=
  Smooth X.hom ∧ IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
    ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ X =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f

/-- **LEAF `BLR_1_2_4`** (Bosch–Lütkebohmert–Raynaud, *Néron models*, Ergebnisse 21 (1990), §1.2
Prop. 4; number and wording recalled, UNVERIFIED, no network). *Printed* (as recalled): let `R` be a
Dedekind domain with field of fractions `K`, `X_K` a smooth and separated `K`-scheme of finite type, and
`X` a smooth, separated `R`-model of `X_K` of finite type. Then `X` is a Néron model of `X_K` if and only
if, for every closed point `s` of `Spec R`, `X ⊗_R 𝒪_{S,s}` is a Néron model of `X_K` over `𝒪_{S,s}`.

*Lean form*: `𝒪_{S,s} = R_𝔭` is any ring with `IsLocalization.AtPrime R_𝔭 𝔭` (Mathlib's characteristic
predicate; every such ring is uniquely isomorphic to `Localization.AtPrime 𝔭`), with a compatible map to
`K`; `X ⊗_R R_𝔭` is the pullback along `Spec R_𝔭 → Spec R`; its generic fibre is `X_K` because
`R → R_𝔭 → K` is `R → K`. `X_K` is not a separate datum: the model is `X`, with its own generic fibre.
(Reading risk, flagged by reduct-glue §5: the print may use the strict henselizations `𝒪^{sh}_{S,s}`, or
both; the strict-henselization form is not stated here.) -/
def BLR_1_2_4 : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom] [IsSeparated X.hom] [QuasiCompact X.hom],
    IsNeronModelOver R K X ↔
      ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
        [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K],
        IsNeronModelOver R𝔭 K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X)

/-! ## Glue: a discrete valuation ring of a number field is the localization at its center -/

section Loc

variable {L : Type} [Field L] [NumberField L]

/-- The algebra structure `𝓞_L → O` (`ReductGlue.toOL`), as a local definition. -/
@[reducible] noncomputable def algOL (O : ValuationSubring L) : Algebra (𝓞 L) O :=
  (ReductGlue.toOL O).toAlgebra

theorem isScalarTower_OL (O : ValuationSubring L) :
    letI := algOL O
    IsScalarTower (𝓞 L) O L := by
  letI := algOL O
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- **`O = (𝓞_L)_{𝔭_O}`** as a characteristic predicate (from reduct-glue's `mem_iff_exists`). -/
theorem isLocalization_center (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    letI := algOL O
    IsLocalization.AtPrime O (ReductGlue.center O) := by
  letI := algOL O
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact ReductGlue.isUnit_toOL O hs
  · intro x
    obtain ⟨a, s, hs, h⟩ := (ReductGlue.mem_iff_exists O (x : L)).mp x.2
    refine ⟨⟨a, ⟨s, hs⟩⟩, ?_⟩
    apply Subtype.ext
    exact h
  · intro a b h
    refine ⟨1, ?_⟩
    have h' : ((a : L)) = (b : L) := congrArg (fun z : O => (z : L)) h
    have : a = b := RingOfIntegers.ext h'
    rw [this]

end Loc

/-! ## The field from the leaf -/

section Field

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- Postcomposition with an isomorphism does not change bijectivity. -/
theorem bijective_comp_iso {C : Type*} [Category C] {Y X : C} {Z W W' : C} (F : (Y ⟶ X) → (Z ⟶ W))
    (e : W ≅ W') : Function.Bijective (fun f => F f ≫ e.hom) ↔ Function.Bijective F := by
  have : (fun f => F f ≫ e.hom) = (fun g : Z ⟶ W => g ≫ e.hom) ∘ F := rfl
  rw [this]
  have hb : Function.Bijective (fun g : Z ⟶ W => g ≫ e.hom) :=
    ⟨fun g₁ g₂ h => by simpa using congrArg (· ≫ e.inv) h,
      fun g => ⟨g ≫ e.inv, by simp⟩⟩
  exact ⟨fun h => (Function.Bijective.of_comp_iff' hb F).mp h, fun h => hb.comp h⟩

/-- The kernel's Néron property of a group model is the printed one of its underlying scheme. -/
theorem isNeronModelOver_of (𝒩 : ZInQ.DefFaltings.GroupModel A L) (h : 𝒩.IsNeronModel) :
    IsNeronModelOver (𝓞 L) L 𝒩.G := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun Y _ => ?_⟩
  have hb := h Y
  refine ⟨fun a b hab => hb.1 ?_, fun g => ?_⟩
  · simp only at hab ⊢
    rw [hab]
  · obtain ⟨f, hf⟩ := hb.2 (g ≫ 𝒩.gen.hom)
    refine ⟨f, ?_⟩
    simp only at hf ⊢
    exact (cancel_mono 𝒩.gen.hom).mp hf

/-- **The field `neronLocalizesDVR` from the printed BLR 1.2/4.** -/
theorem neronLocalizesDVR_of_printed (hB : BLR_1_2_4) : ReductGlue.NeronLocalizesDVR := by
  intro K _ A L _ _ _ 𝒩 h𝒩 O _
  haveI := ReductGlue.center_isMaximal O
  letI := algOL O
  haveI := isScalarTower_OL O
  haveI := isLocalization_center O
  have h1 := isNeronModelOver_of 𝒩 h𝒩
  have h2 := ((hB (𝓞 L) L 𝒩.G).mp h1) (ReductGlue.center O) O
  obtain ⟨_, _, _, _, h3⟩ := h2
  have h4 : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ (ReductGlue.toO 𝒩 O).G => (Over.pullback (ReductSplit.jO O)).map f :=
    h3
  intro Y _
  have hb := h4 Y
  refine ⟨fun a b hab => hb.1 ?_, fun g => ?_⟩
  · simp only at hab ⊢
    exact (cancel_mono (ReductGlue.toO 𝒩 O).gen.hom).mp hab
  · obtain ⟨f, hf⟩ := hb.2 (g ≫ (ReductGlue.toO 𝒩 O).gen.inv)
    refine ⟨f, ?_⟩
    simp only at hf ⊢
    rw [hf]
    simp

end Field


/-! # Part S: `semistableNeronBaseChange` (SS2)

reduct-glue proved SS2 from four leaves: reduct-split's `IdentityComponentBaseChangeDVR` (SGA 7 IX 3.3,
second assertion, in an open-subgroup form), `IdentityComponentOL` (SGA 3 VI_B 3.10, in a group-model form),
`OpenImmersionOfLocal` (EGA IV₃ 8.10.5, specialized to `Spec (𝓞_L)_𝔭`) and `NeronLocalizesDVR` (BLR 1.2/4).
The last is now a theorem from the printed `BLR_1_2_4` (Part N). For the other three this part states the
printed theorem over Mathlib definitions (`SGA3_VIB_3_10`, `SGA7_IX_3_3`, `EGAIV_8_10_5_openImm`), with the
identity component of a group scheme over a base defined as a set (`idCompSet`; Mathlib has none), and the
step from each printed form to the field's form as a named glue Prop. -/

/-- **SS2 from the printed BLR 1.2/4 and the three other leaves of reduct-glue** (compiled; the proof is
reduct-glue's `semistableNeronBaseChangeLocalGlobal_of` and `semistableLocalGlobal_leaf`). -/
theorem semistableNeronBaseChange_of_printedBLR (hB : BLR_1_2_4)
    (h33b : ReductSplit.IdentityComponentBaseChangeDVR) (hIC : ReductGlue.IdentityComponentOL)
    (hOI : ReductGlue.OpenImmersionOfLocal) : ZInQ.HeightSplit.SemistableNeronBaseChange :=
  ReductSplit.semistableNeronBaseChange_of_leaves h33b
    (ReductGlue.semistableLocalGlobal_leaf (neronLocalizesDVR_of_printed hB))
    (ReductGlue.semistableNeronBaseChangeLocalGlobal_of hIC hOI (neronLocalizesDVR_of_printed hB))

section IdComp

variable {S : Scheme.{0}}

/-- **The identity component `G⁰` of a group scheme `G → S`, as a set** (SGA 3 VI_B 3.1; Mathlib 4.35 has
no identity component of a group scheme over a base): the points `x` of `G` lying in the connected
component of `e(s)` in the fibre `G_s = f⁻¹(s)`, `s = f(x)` (the fibre with the subspace topology; it is
homeomorphic to the underlying space of the scheme `G ×_S κ(s)`, EGA I 3.6.1). -/
def idCompSet (G : Over S) [GrpObj G] : Set G.left :=
  {x | x ∈ connectedComponentIn (G.hom.base ⁻¹' {G.hom.base x})
    ((η[G] : 𝟙_ (Over S) ⟶ G).left.base (G.hom.base x))}

/-- **LEAF `SGA3_VIB_3_10`** (SGA 3 I, Exp. VI_B, Thm. 3.10; number recalled, UNVERIFIED): for a smooth
group scheme `G` over a scheme `S` (the print: locally of finite presentation with smooth connected...
fibres; smooth suffices), `G⁰` is open in `G`. -/
def SGA3_VIB_3_10 : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom], IsOpen (idCompSet G)

end IdComp

open ZInQ.HeightSplit ZInQ.DefFaltings in
/-- **GLUE `IdentityComponentGroupModel`** (from the open set `𝒢⁰` to the field's group model). For a group
model `𝒢` of `A_L` over `𝓞_L` whose identity component is open, the open subscheme on `𝒢⁰` is a group model
`𝒢₀` with an open immersion homomorphism into `𝒢` and connected geometric fibres at the maximal ideals.
Needs: (i) `𝒢⁰` is stable under the group law (each `(𝒢_s)⁰` is a subgroup: SGA 3 VI_A 2.3.1, from
`(𝒢_s)⁰ ×_{κ(s)} (𝒢_s)⁰` connected, Stacks 0385 with the bundle leaf `geomConnOfRationalPoint`), so the open
subscheme is a group object and the inclusion a homomorphism; (ii) quasi-compactness (`𝒢` noetherian);
(iii) the generic fibre: `A_L` is connected, so `(𝒢_L)⁰ = 𝒢_L` and `𝒢.gen` restricts; (iv) `(𝒢_𝔭)⁰` is
connected with a rational point, hence geometrically connected (bundle leaf `geomConnOfRationalPoint`,
Stacks 04KV), and the geometric fibre of `𝒢₀` at `𝔭` is `(𝒢_𝔭)⁰ ×_{κ(𝔭)} κ̄(𝔭)`. Not in Lean. -/
def IdentityComponentGroupModel : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), IsOpen (idCompSet 𝒢.G) →
    ∃ (𝒢₀ : GroupModel A L) (i : 𝒢₀.G ⟶ 𝒢.G), IsOpenImmersion i.left ∧
      IsMonHom i ∧ ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], ConnectedSpace (geomFibre 𝒢₀ 𝔭).left

/-- `IdentityComponentOL` from the printed SGA 3 VI_B 3.10 and the glue. -/
theorem identityComponentOL_of_printed (h : SGA3_VIB_3_10) (g : IdentityComponentGroupModel) :
    ReductGlue.IdentityComponentOL :=
  fun K _ A L _ _ _ 𝒢 => g K A L 𝒢 (h _ 𝒢.G)

section SGA7

open ReductSplit

variable {K K' : Type} [Field K] [Field K'] [Algebra K K']

/-- The base change `𝒩 ×_O O'` along `O → O'` (`O' ∩ K = O`), as a scheme over `O'`. -/
noncomputable abbrev bcO {O : ValuationSubring K} {O' : ValuationSubring K'}
    (hO : O'.comap (algebraMap K K') = O) (G : Over (Spec (CommRingCat.of O))) :
    Over (Spec (CommRingCat.of O')) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (comapHom hO)))).obj G

/-- **LEAF `SGA7_IX_3_3`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.3, second assertion; number and wording
recalled, UNVERIFIED). *Printed* (as recalled): `R → R'` a local homomorphism of discrete valuation rings
with fraction fields `K ⊆ K'`, `A_K` an abelian variety with semistable reduction, `N`, `N'` the Néron models
of `A_K` over `R` and of `A_{K'}` over `R'`; then the canonical morphism `N ×_R R' → N'` induces an
isomorphism `N⁰ ×_R R' ≅ N'⁰` of identity components.

*Lean form*: `K'/K` any extension, `O' ∩ K = O`; `c : 𝒩 ×_O O' → 𝒩'` any homomorphism whose generic fibre is
an isomorphism (the canonical morphism is one; any other is the canonical one followed by an automorphism of
the group scheme `𝒩'`, which preserves `𝒩'⁰`); `N⁰ ×_R R'` is the identity component of `𝒩 ×_O O'` (the
identity component commutes with base change, SGA 3 VI_B 3.3, UNVERIFIED), given as an open `U` with
`U = idCompSet`. Conclusion: `U → 𝒩'` is an open immersion with image `𝒩'⁰`. -/
def SGA7_IX_3_3 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] (O' : ValuationSubring K') [IsDiscreteValuationRing O']
    (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K), HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
    ∀ c : bcO hO 𝒩.G ⟶ 𝒩'.G, IsMonHom c → IsIso ((Over.pullback (jO O')).map c) →
    ∀ U : (bcO hO 𝒩.G).left.Opens, (U : Set (bcO hO 𝒩.G).left) = idCompSet (bcO hO 𝒩.G) →
      IsOpenImmersion (U.ι ≫ c.left) ∧ Set.range (U.ι ≫ c.left).base = idCompSet 𝒩'.G

/-- **GLUE `IdentityComponentFromPrinted`** (from the printed SGA 7 IX 3.3 to reduct-split's
`IdentityComponentBaseChangeDVR`). Needs: (i) the canonical homomorphism `c : 𝒩 ×_O O' → 𝒩'` (Néron mapping
property of `𝒩'` and reduct-glue's `isMonHom_of_ext`; its generic fibre is an isomorphism: `bcbcIso`);
(ii) an open subgroup scheme `U ⊆ 𝒩` with connected generic and geometric special fibres has image `𝒩⁰`
(an open subgroup of a group scheme over a field is closed, so it is a union of components; SGA 3 VI_A
2.3-2.4); (iii) the identity component commutes with base change: `(𝒩 ×_O O')⁰ = 𝒩⁰ ×_O O'` (SGA 3 VI_B 3.3;
fibres of `𝒩⁰` are geometrically connected by (ii) and Stacks 04KV); (iv) openness of `(𝒩 ×_O O')⁰` from
`SGA3_VIB_3_10`; then `U ×_O O' ≅ (𝒩 ×_O O')⁰ → 𝒩'` is an open immersion, a homomorphism because `c` is.
Not in Lean. -/
def IdentityComponentFromPrinted : Prop :=
  SGA3_VIB_3_10 → SGA7_IX_3_3 → IdentityComponentBaseChangeDVR

end SGA7

/-- **LEAF `EGAIV_8_10_5_openImm`** (EGA IV₃ 8.10.5, the open-immersion item; also Stacks 081M-type
statements; locator recalled, UNVERIFIED; the same setting as the kernel's leaf
`ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii`, which is the item for properness). `(D_i)` a directed inverse
system of quasi-compact quasi-separated schemes with affine transition maps, `c` a limit cone, `f_i : X_i → Y_i`
a morphism of schemes of finite presentation over `D_i`. If the base change of `f_i` to `lim D_i` is an open
immersion, so is its base change to some `D_j`. -/
def EGAIV_8_10_5_openImm : Prop :=
  ∀ (J : Type) [Preorder J] [IsDirectedOrder J] [Nonempty J] (D : Jᵒᵖ ⥤ Scheme.{0})
    [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D), IsLimit c →
    ∀ (i : Jᵒᵖ) (Xi Yi : Over (D.obj i)), LocallyOfFinitePresentation Xi.hom → QuasiCompact Xi.hom →
      QuasiSeparated Xi.hom → LocallyOfFinitePresentation Yi.hom → QuasiCompact Yi.hom →
      QuasiSeparated Yi.hom → ∀ fi : Xi ⟶ Yi,
      IsOpenImmersion ((Over.pullback (c.π.app i)).map fi).left →
      ∃ (j : Jᵒᵖ) (a : j ⟶ i), IsOpenImmersion ((Over.pullback (D.map a)).map fi).left

/-- **GLUE `OpenImmersionLocalization`** (from EGA IV 8.10.5 to reduct-glue's `OpenImmersionOfLocal`).
Needs: (i) for a maximal ideal `𝔭` of `𝓞_L` (the center of a DVR `O`, `ReductGlue.dvrAt`), `Spec O` is the
limit of the basic opens `Spec 𝓞_L[1/s]`, `s ∉ 𝔭`, a directed system (by divisibility) of affine schemes with
affine transition maps (`O = colim 𝓞_L[1/s]`, as for `Spec L = lim Spec 𝓞_L[1/n!]` in the kernel's
`ZInQ.Contrib.SpreadOut.specConeIsLimit`); (ii) `X`, `Y` smooth, separated, quasi-compact over `𝓞_L` are of
finite presentation (`𝓞_L` noetherian), hence so are their base changes; (iii) an open immersion over each
`D(s_𝔭)` (and `⋃ D(s_𝔭) = Spec 𝓞_L`, the generic point lying in each) is an open immersion: open immersions
are local on the target (`IsZariskiLocalAtTarget`), and the base change along the open immersion
`D(s) → Spec 𝓞_L` is the restriction over `Y_{D(s)}`. Not in Lean. -/
def OpenImmersionLocalization : Prop :=
  EGAIV_8_10_5_openImm → ReductGlue.OpenImmersionOfLocal

/-- **SS2 from printed-form leaves and three named glue Props** (compiled): BLR 1.2/4, SGA 3 VI_B 3.10,
SGA 7 IX 3.3, EGA IV 8.10.5 (open immersions), with `IdentityComponentGroupModel`,
`IdentityComponentFromPrinted`, `OpenImmersionLocalization`. -/
theorem semistableNeronBaseChange_of_printed (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3) (hE : EGAIV_8_10_5_openImm) (g1 : IdentityComponentGroupModel)
    (g2 : IdentityComponentFromPrinted) (g3 : OpenImmersionLocalization) :
    ZInQ.HeightSplit.SemistableNeronBaseChange :=
  semistableNeronBaseChange_of_printedBLR hB (g2 h3 h7) (identityComponentOL_of_printed h3 g1) (g3 hE)

/-! # Part F: `faltingsLemma5BC` from Faltings' Lemma 5 (printed identity) and Raynaud's bound

reduct-split proved `FaltingsLemma5BC` from the base-field form `HeightSplit.FaltingsLemma5` with no glue
(`ReductSplit.faltingsLemma5BC_final`). `FaltingsLemma5` (`|h(A) − h(B)| ≤ ½ log deg φ`) is a consequence of
two printed results (height-split §8): Faltings' Lemma 5, an identity with the correction term
`[K:ℚ]⁻¹ log #s*Ω¹_{G/𝓞_K}` for `G = ker(𝒩_A → 𝒩_B)`, and Raynaud's bound on that term. Both are stated here
over Mathlib objects: `G` is the fibre product `𝒩_A ×_{φ_𝒩, 𝒩_B, e} S`, its unit section `s`, and
`#s*Ω¹_{G/S}` is computed stalkwise as the conormal module `I/I²` of `s` (`kerOmegaLog`). -/

section Faltings

open ZInQ.HeightSplit ZInQ.DefFaltings

/-- Verbatim copy of `ZInQ.HeightSplit.FaltingsLemma5` (`ZInQKernel/OneProof/H/TailY.lean`). -/
def FaltingsLemma5 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
      IsSemistable 𝒩A → IsSemistable 𝒩B →
      ∀ x y : ℝ, 𝒩A.height = x → 𝒩B.height = y → |x - y| ≤ (1 / 2) * Real.log (isogDeg φ)

example : FaltingsLemma5 = ZInQ.HeightSplit.FaltingsLemma5 := rfl

/-- Verbatim copy of the field statement `ZInQ.HeightSplit.FaltingsLemma5BC`. -/
def FaltingsLemma5BC : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L]
      (𝒩A : GroupModel A L) (𝒩B : GroupModel B L), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
      IsSemistable 𝒩A → IsSemistable 𝒩B →
      ∀ x y : ℝ, 𝒩A.height = x → 𝒩B.height = y → |x - y| ≤ (1 / 2) * Real.log (isogDeg φ)

example : FaltingsLemma5BC = ZInQ.HeightSplit.FaltingsLemma5BC := rfl

variable {S : Scheme.{0}}

/-- The kernel `G = X ×_{f, Y, e} S` of a homomorphism `f : X → Y` of group schemes over `S`. -/
noncomputable abbrev kerScheme {X Y : Over S} [GrpObj Y] (f : X ⟶ Y) : Scheme.{0} :=
  pullback f.left (η[Y] : 𝟙_ (Over S) ⟶ Y).left

/-- The unit section `s : S → G` of the kernel of a homomorphism. -/
noncomputable def kerUnit {X Y : Over S} [GrpObj X] [GrpObj Y] (f : X ⟶ Y) (hf : IsMonHom f) :
    (𝟙_ (Over S)).left ⟶ kerScheme f :=
  pullback.lift (η[X] : 𝟙_ (Over S) ⟶ X).left (𝟙 _) (by
    rw [Category.id_comp, ← Over.comp_left, IsMonHom.one_hom])

/-- **`log #s*Ω¹_{G/S}`** for the kernel `G` of `f` and its unit section `s`: the sum over the points `P` of
`S` of `log #(I_P/I_P²)`, `I_P = ker(𝒪_{G,s(P)} → 𝒪_{S,P})` the stalk of the ideal of the section. For a
section `s` of `G → S`, `s*Ω¹_{G/S}` is the conormal sheaf `s*(I/I²)` (EGA IV 17.2.5, UNVERIFIED locator), whose
stalk at `P` is `I_P/I_P²`; over a Dedekind `S` a torsion coherent module is the sum of its stalks, so its
cardinality is the product of theirs. (An infinite stalk contributes `log 0 = 0`; for a quasi-finite `G` with
étale generic fibre all stalks are finite and almost all trivial.) -/
noncomputable def kerOmegaLog {X Y : Over S} [GrpObj X] [GrpObj Y] (f : X ⟶ Y) (hf : IsMonHom f) : ℝ :=
  ∑ᶠ (P : (𝟙_ (Over S)).left),
    Real.log (Nat.card (RingHom.ker ((kerUnit f hf).stalkMap P).hom).Cotangent)

theorem kerOmegaLog_nonneg {X Y : Over S} [GrpObj X] [GrpObj Y] (f : X ⟶ Y) (hf : IsMonHom f) :
    0 ≤ kerOmegaLog f hf :=
  finsum_nonneg fun _ => Real.log_natCast_nonneg _

/-- The generic-fibre condition: `φ_𝒩` extends `φ_K` through the identifications of the generic fibres. -/
def ExtendsIsogeny {K : Type} [Field K] [NumberField K] {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X)
    (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (φ𝒩 : 𝒩A.G ⟶ 𝒩B.G) : Prop :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)))).map φ𝒩 ≫ 𝒩B.gen.hom =
    𝒩A.gen.hom ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K K)))).map φ

/-- **LEAF `FaltingsLemma5Printed`** (G. Faltings, *Endlichkeitssätze für abelsche Varietäten über
Zahlkörpern*, Invent. Math. 73 (1983), Lemma 5, p. 358; wording recalled, UNVERIFIED: locators.md could not
read it). *Printed* (as recalled): for an isogeny `φ : A → B` of abelian varieties over a number field `K` with
semistable reduction everywhere, `G = ker(φ_𝒩 : 𝒩_A → 𝒩_B)` (a quasi-finite flat group scheme over
`S = Spec 𝓞_K`) and `s` its unit section,
`h(B) = h(A) + ½ log deg φ − [K:ℚ]⁻¹ log #s*Ω¹_{G/S}`.
*Lean form*: `𝒩_A`, `𝒩_B` semistable Néron models over `𝓞_K` (kernel `GroupModel`), `φ_𝒩` the homomorphism
extending `φ` (unique by the Néron property, so "every" is "the"), heights the kernel's `GroupModel.height`
(the identity does not depend on the normalization of the metric, which shifts both sides equally). -/
def FaltingsLemma5Printed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
      IsSemistable 𝒩A → IsSemistable 𝒩B →
      ∀ (φ𝒩 : 𝒩A.G ⟶ 𝒩B.G) (hφ𝒩 : IsMonHom φ𝒩), ExtendsIsogeny φ 𝒩A 𝒩B φ𝒩 →
      ∀ x y : ℝ, 𝒩A.height = x → 𝒩B.height = y →
        y = x + (1 / 2) * Real.log (isogDeg φ) - kerOmegaLog φ𝒩 hφ𝒩 / Module.finrank ℚ K

/-- **LEAF `RaynaudKernelBound`** (M. Raynaud, *Hauteurs et isogénies*, Astérisque 127 (1985), Exp. VII,
Cor. 2.1.3 as cited by height-split §8 and Pazuki 2012 Rem. 2.3; number and wording recalled, UNVERIFIED).
In the setting of `FaltingsLemma5Printed`: `log #s*Ω¹_{G/S} ≤ [K:ℚ] log deg φ` (the lower bound `0 ≤` is
automatic, `kerOmegaLog_nonneg`). -/
def RaynaudKernelBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ (𝒩A : GroupModel A K) (𝒩B : GroupModel B K), 𝒩A.IsNeronModel → 𝒩B.IsNeronModel →
      IsSemistable 𝒩A → IsSemistable 𝒩B →
      ∀ (φ𝒩 : 𝒩A.G ⟶ 𝒩B.G) (hφ𝒩 : IsMonHom φ𝒩), ExtendsIsogeny φ 𝒩A 𝒩B φ𝒩 →
        kerOmegaLog φ𝒩 hφ𝒩 ≤ Module.finrank ℚ K * Real.log (isogDeg φ)

/-- The Néron extension of an isogeny is a homomorphism extending it (glue, proved). -/
theorem exists_extension {K : Type} [Field K] [NumberField K] {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X)
    (hφ : IsIsogeny φ) (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (hB : 𝒩B.IsNeronModel) :
    ∃ (φ𝒩 : 𝒩A.G ⟶ 𝒩B.G), IsMonHom φ𝒩 ∧ ExtendsIsogeny φ 𝒩A 𝒩B φ𝒩 := by
  haveI := hφ.1
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)))
  let fK := Spec.map (CommRingCat.ofHom (algebraMap K K))
  let φK : (A.baseChange K).X ⟶ (B.baseChange K).X := (Over.pullback fK).map φ
  have hK : IsMonHom φK := by
    letI : GrpObj ((Over.pullback fK).obj A.X) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback fK).obj B.X) := Functor.grpObjObj
    exact (inferInstance : IsMonHom ((Over.pullback fK).map φ))
  obtain ⟨φ𝒩, h⟩ := (hB 𝒩A.G).2 (𝒩A.gen.hom ≫ φK)
  refine ⟨φ𝒩, ?_, h⟩
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of (𝓞 K))))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (𝒩A.G ⊗ 𝒩A.G).hom :=
    ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  letI : GrpObj (F.obj 𝒩A.G) := Functor.grpObjObj
  letI : GrpObj (genericFibre K 𝒩A.G) := Functor.grpObjObj
  have hA := 𝒩A.gen_hom
  have h1 : IsMonHom (𝒩A.gen.hom ≫ φK) := @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ hA hK
  exact ReductGlue.isMonHom_of_ext F (𝒩A.gen.hom ≫ φK) 𝒩B.gen.hom h1 𝒩B.gen_hom
    (hB _).1 (hB _).1 φ𝒩 h

/-- **`FaltingsLemma5` from the printed Lemma 5 and Raynaud's bound** (compiled). -/
theorem faltingsLemma5_of_printed (hF : FaltingsLemma5Printed) (hR : RaynaudKernelBound) :
    ZInQ.HeightSplit.FaltingsLemma5 := by
  intro K _ _ A B φ hφ 𝒩A 𝒩B hA hB sA sB x y hx hy
  obtain ⟨φ𝒩, hm, he⟩ := exists_extension φ hφ 𝒩A 𝒩B hB
  have hid := hF K A B φ hφ 𝒩A 𝒩B hA hB sA sB φ𝒩 hm he x y hx hy
  have hub := hR K A B φ hφ 𝒩A 𝒩B hA hB sA sB φ𝒩 hm he
  have hlb := kerOmegaLog_nonneg φ𝒩 hm
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  set c := kerOmegaLog φ𝒩 hm
  set d := Real.log (isogDeg φ)
  have h1 : c / Module.finrank ℚ K ≤ d := by rw [div_le_iff₀ hn]; linarith
  have h2 : 0 ≤ c / Module.finrank ℚ K := div_nonneg hlb hn.le
  rw [hid, abs_le]
  constructor <;> linarith

/-- **The field `faltingsLemma5BC` from the printed Lemma 5 and Raynaud's bound** (compiled, with
reduct-split's `faltingsLemma5BC_final`). -/
theorem faltingsLemma5BC_of_printed (hF : FaltingsLemma5Printed) (hR : RaynaudKernelBound) :
    ZInQ.HeightSplit.FaltingsLemma5BC :=
  ReductSplit.faltingsLemma5BC_final (faltingsLemma5_of_printed hF hR)

end Faltings

/-! # Part S, continued: the glue `OpenImmersionLocalization` proved

`Spec O = lim_{s ∉ 𝔭} Spec 𝓞_L[1/s]` for a DVR `O` of `L` with center `𝔭` (`specConeIsLimitO`, the pattern
of the kernel's `ZInQ.Contrib.SpreadOut.NF.specConeIsLimit`); EGA IV 8.10.5 then gives `s_𝔭 ∉ 𝔭` with the
base change to `𝓞_L[1/s_𝔭]` an open immersion; these opens cover `Spec 𝓞_L`, and open immersions are local
on the target (`IsZariskiLocalAtTarget.of_openCover`). -/

section OIL

/-- Base change along `u` then `v` is conjugate to base change along `u ≫ v` (for open immersions). -/
theorem isOpenImmersion_pb_pb_iff {S₁ S₂ S₃ : Scheme.{0}} (u : S₁ ⟶ S₂) (v : S₂ ⟶ S₃) (w : S₁ ⟶ S₃)
    (h : u ≫ v = w) {X Y : Over S₃} (f : X ⟶ Y) :
    IsOpenImmersion ((Over.pullback u).map ((Over.pullback v).map f)).left ↔
      IsOpenImmersion ((Over.pullback w).map f).left := by
  subst h
  have hn := congrArg CommaMorphism.left ((Over.pullbackComp u v).hom.naturality f)
  simp only [Over.comp_left, Functor.comp_map] at hn
  haveI : IsIso ((Over.pullbackComp u v).hom.app X).left :=
    Functor.map_isIso (Over.forget _) ((Over.pullbackComp u v).hom.app X)
  haveI : IsIso ((Over.pullbackComp u v).hom.app Y).left :=
    Functor.map_isIso (Over.forget _) ((Over.pullbackComp u v).hom.app Y)
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
    ((Over.pullbackComp u v).hom.app X).left, ← hn,
    MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion]

variable {L : Type} [Field L] [NumberField L]

/-- The index set `𝓞_L ∖ 𝔭`, preordered by divisibility. -/
abbrev Idx (P : Ideal (𝓞 L)) [P.IsPrime] : Type := P.primeCompl

instance (P : Ideal (𝓞 L)) [P.IsPrime] : Preorder (Idx P) where
  le a b := (a.1 : 𝓞 L) ∣ b.1
  le_refl _ := dvd_refl _
  le_trans _ _ _ h1 h2 := dvd_trans h1 h2

instance (P : Ideal (𝓞 L)) [P.IsPrime] : IsDirected (Idx P) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 * b.1, P.primeCompl.mul_mem a.2 b.2⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance (P : Ideal (𝓞 L)) [P.IsPrime] : Nonempty (Idx P) := ⟨⟨1, P.primeCompl.one_mem⟩⟩

variable (P : Ideal (𝓞 L)) [P.IsPrime]

/-- The stage `𝓞_L[1/a]`. -/
abbrev RgP (a : Idx P) : Type := Localization.Away (a.1 : 𝓞 L)

theorem ne_zero_idx (a : Idx P) : (a.1 : 𝓞 L) ≠ 0 := fun h => a.2 (h ▸ P.zero_mem)

theorem isUnit_trP {a b : Idx P} (h : a ≤ b) : IsUnit (algebraMap (𝓞 L) (RgP P b) a.1) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit b.1)

/-- `𝓞_L[1/a] → 𝓞_L[1/b]` for `a ∣ b`. -/
noncomputable def trP {a b : Idx P} (h : a ≤ b) : RgP P a →+* RgP P b :=
  IsLocalization.Away.lift a.1 (isUnit_trP P h)

theorem trP_alg {a b : Idx P} (h : a ≤ b) (x : 𝓞 L) :
    trP P h (algebraMap (𝓞 L) (RgP P a) x) = algebraMap (𝓞 L) (RgP P b) x :=
  IsLocalization.Away.lift_eq _ _ _

theorem homP_ext {a : Idx P} {T : Type*} [CommRing T] {f g : RgP P a →+* T}
    (h : ∀ x : 𝓞 L, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a.1) (RingHom.ext h)

/-- The diagram `a ↦ 𝓞_L[1/a]`. -/
noncomputable def ringDiagP : Idx P ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (RgP P a)
  map f := CommRingCat.ofHom (trP P (leOfHom f))
  map_id a := by
    apply CommRingCat.hom_ext
    exact homP_ext P (fun x => by simp [trP_alg])
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact homP_ext P (fun x => by simp [trP_alg])

theorem trP_trP {a b c : Idx P} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    (trP P h₂).comp (trP P h₁) = trP P (h₁.trans h₂) :=
  homP_ext P (fun x => by simp [trP_alg])

theorem trP_refl (a : Idx P) : trP P (le_refl a) = RingHom.id _ :=
  homP_ext P (fun x => by simp [trP_alg])

/-- The diagram `a ↦ Spec 𝓞_L[1/a]`. -/
noncomputable def specDiagP : (Idx P)ᵒᵖ ⥤ Scheme.{0} where
  obj a := Spec (CommRingCat.of (RgP P a.unop))
  map f := Spec.map (CommRingCat.ofHom (trP P (leOfHom f.unop)))
  map_id a := by
    rw [show leOfHom (𝟙 a).unop = le_refl a.unop from rfl, trP_refl, CommRingCat.ofHom_id,
      Spec.map_id]
  map_comp f g := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, trP_trP]

instance specDiagP_isAffineHom {i j : (Idx P)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((specDiagP P).map f) :=
  show IsAffineHom (Spec.map _) from inferInstance

instance specDiagP_compactSpace (i : (Idx P)ᵒᵖ) : CompactSpace ((specDiagP P).obj i) :=
  show CompactSpace (Spec _) from inferInstance

instance specDiagP_quasiSeparatedSpace (i : (Idx P)ᵒᵖ) : QuasiSeparatedSpace ((specDiagP P).obj i) :=
  show QuasiSeparatedSpace (Spec _) from inferInstance

variable (O : ValuationSubring L) [IsDiscreteValuationRing O]

/-- `𝓞_L[1/a] → O` for `a ∉ 𝔭_O`. -/
noncomputable def toOP (a : Idx (ReductGlue.center O)) : RgP (ReductGlue.center O) a →+* O :=
  IsLocalization.Away.lift a.1 (g := ReductGlue.toOL O) (ReductGlue.isUnit_toOL O a.2)

theorem toOP_alg (a : Idx (ReductGlue.center O)) (x : 𝓞 L) :
    toOP O a (algebraMap (𝓞 L) _ x) = ReductGlue.toOL O x :=
  IsLocalization.Away.lift_eq _ _ _

theorem toOL_injective : Function.Injective (ReductGlue.toOL O) := by
  intro a b h
  have h' : ((ReductGlue.toOL O a : O) : L) = ((ReductGlue.toOL O b : O) : L) := by rw [h]
  exact RingOfIntegers.ext h'

theorem toOP_injective (a : Idx (ReductGlue.center O)) : Function.Injective (toOP O a) := by
  unfold toOP IsLocalization.Away.lift
  rw [IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    rw [IsLocalization.injective (RgP _ a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (ne_zero_idx _ a)) h]
  · intro h
    rw [toOL_injective O h]

/-- `O` as a cocone over `a ↦ 𝓞_L[1/a]`. -/
noncomputable def ringCoconeO : Cocone (ringDiagP (ReductGlue.center O)) :=
  Cocone.mk (CommRingCat.of O)
    { app := fun a => CommRingCat.ofHom (toOP O a)
      naturality := fun a b f => by
        apply CommRingCat.hom_ext
        exact homP_ext _ (fun x => by simp [ringDiagP, trP_alg, toOP_alg]) }

/-- **`O = colim_{a ∉ 𝔭} 𝓞_L[1/a]`.** -/
noncomputable def ringCoconeOIsColimit : IsColimit (ringCoconeO O) := by
  haveI : ReflectsColimit (ringDiagP (ReductGlue.center O)) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : O)
    obtain ⟨r, s, hs, h⟩ := (ReductGlue.mem_iff_exists O (x : L)).mp x.2
    let j : Idx (ReductGlue.center O) := ⟨s, hs⟩
    refine ⟨j, (IsLocalization.mk' (RgP _ j) r (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s) :
      RgP _ j), ?_⟩
    show x = toOP O j _
    unfold toOP IsLocalization.Away.lift
    symm
    rw [IsLocalization.lift_mk'_spec]
    apply Subtype.ext
    change (r : L) = (s : L) * (x : L)
    rw [← h, mul_comm]
  · intro j x y h
    have h' : toOP O j x = toOP O j y := h
    exact ⟨j, 𝟙 j, by rw [toOP_injective O j h']⟩

theorem toOP_trP {a b : Idx (ReductGlue.center O)} (h : a ≤ b) :
    (toOP O b).comp (trP _ h) = toOP O a :=
  homP_ext _ (fun x => by simp [trP_alg, toOP_alg])

/-- `Spec O` as a cone over `a ↦ Spec 𝓞_L[1/a]`. -/
noncomputable def specConeO : Cone (specDiagP (ReductGlue.center O)) :=
  Cone.mk (Spec (CommRingCat.of O))
    { app := fun a => Spec.map (CommRingCat.ofHom (toOP O a.unop))
      naturality := fun a b f => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, specDiagP]
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toOP_trP] }

/-- **`Spec O = lim_{a ∉ 𝔭} Spec 𝓞_L[1/a]`.** -/
noncomputable def specConeOIsLimit : IsLimit (specConeO O) := by
  have h := isLimitOfPreserves Scheme.Spec (ringCoconeOIsColimit O).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro m n f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Iso.refl_hom, Category.id_comp]

/-- From EGA IV 8.10.5 at one DVR `O`: some `s ∉ 𝔭_O` with the base change to `𝓞_L[1/s]` an open
immersion. -/
theorem exists_away_of_dvr (hE : EGAIV_8_10_5_openImm) {X Y : Over (Spec (CommRingCat.of (𝓞 L)))}
    [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [Smooth Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y)
    (h : IsOpenImmersion ((Over.pullback (ReductGlue.gO O)).map f).left) :
    ∃ s : 𝓞 L, s ∉ ReductGlue.center O ∧ IsOpenImmersion ((Over.pullback (Spec.map
      (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.Away s))))).map f).left := by
  let P := ReductGlue.center O
  let i0 : (Idx P)ᵒᵖ := Opposite.op ⟨1, P.primeCompl.one_mem⟩
  let g1 := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (RgP P i0.unop)))
  have hc : (specConeO O).π.app i0 ≫ g1 = ReductGlue.gO O := by
    show Spec.map (CommRingCat.ofHom (toOP O i0.unop)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (RgP P i0.unop))) =
      Spec.map (CommRingCat.ofHom (ReductGlue.toOL O))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext (toOP_alg O i0.unop)
  have h1 : IsOpenImmersion ((Over.pullback ((specConeO O).π.app i0)).map
      ((Over.pullback g1).map f)).left :=
    (isOpenImmersion_pb_pb_iff _ _ _ hc f).mpr h
  obtain ⟨j, a, hj⟩ := hE (Idx P) (specDiagP P) (specConeO O) (specConeOIsLimit O) i0
    ((Over.pullback g1).obj X) ((Over.pullback g1).obj Y) (ZInQ.Contrib.SpreadOut.lfp_pb g1 X)
    (ZInQ.Contrib.SpreadOut.qc_pb g1 X) (ZInQ.Contrib.SpreadOut.qs_pb g1 X)
    (ZInQ.Contrib.SpreadOut.lfp_pb g1 Y) (ZInQ.Contrib.SpreadOut.qc_pb g1 Y)
    (ZInQ.Contrib.SpreadOut.qs_pb g1 Y) ((Over.pullback g1).map f) h1
  refine ⟨j.unop.1, j.unop.2, ?_⟩
  have hc2 : (specDiagP P).map a ≫ g1 =
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.Away (j.unop.1 : 𝓞 L)))) := by
    show Spec.map (CommRingCat.ofHom (trP P (leOfHom a.unop))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (RgP P i0.unop))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext (trP_alg P (leOfHom a.unop))
  exact (isOpenImmersion_pb_pb_iff _ _ _ hc2 f).mp hj

end OIL

/-- **The glue `OpenImmersionLocalization`, PROVED**: reduct-glue's `OpenImmersionOfLocal` from the
printed EGA IV 8.10.5 (open immersions). -/
theorem openImmersionLocalization : OpenImmersionLocalization := by
  intro hE L _ _ X Y _ _ _ _ _ _ f hloc
  have key : ∀ t : {𝔭 : Ideal (𝓞 L) // 𝔭.IsMaximal}, ∃ s : 𝓞 L, s ∉ t.1 ∧
      IsOpenImmersion ((Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.Away s))))).map f).left := by
    rintro ⟨𝔭, h𝔭⟩
    obtain ⟨s, hs, h⟩ := exists_away_of_dvr (ReductGlue.dvrAt 𝔭) hE f (hloc _)
    rw [ReductGlue.center_dvrAt] at hs
    exact ⟨s, hs, h⟩
  choose s hs hsO using key
  let gs : ∀ t : {𝔭 : Ideal (𝓞 L) // 𝔭.IsMaximal}, Spec (CommRingCat.of (Localization.Away (s t))) ⟶
      Spec (CommRingCat.of (𝓞 L)) := fun t =>
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.Away (s t))))
  have hcov : ∀ y : Y.left, ∃ t z, (pullback.fst Y.hom (gs t)) z = y := by
    intro y
    let q : PrimeSpectrum (𝓞 L) := Y.hom y
    have hq : ∃ t, s t ∉ q.asIdeal := by
      by_cases hq : q.asIdeal = ⊥
      · obtain ⟨𝔭, h𝔭⟩ := Ideal.exists_maximal (𝓞 L)
        refine ⟨⟨𝔭, h𝔭⟩, ?_⟩
        rw [hq, Ideal.mem_bot]
        intro h0
        exact hs ⟨𝔭, h𝔭⟩ (h0 ▸ 𝔭.zero_mem)
      · exact ⟨⟨q.asIdeal, Ideal.IsPrime.isMaximal q.isPrime hq⟩,
          hs ⟨q.asIdeal, Ideal.IsPrime.isMaximal q.isPrime hq⟩⟩
    obtain ⟨t, ht⟩ := hq
    have hr : y ∈ Set.range (pullback.fst Y.hom (gs t)) := by
      rw [Scheme.Pullback.range_fst]
      have h1 : Y.hom y ∈ ((gs t).opensRange : Set (Spec (CommRingCat.of (𝓞 L)))) := by
        rw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (𝓞 L)) (s t)]
        exact ht
      exact h1
    obtain ⟨z, hz⟩ := hr
    exact ⟨t, z, hz⟩
  let 𝒰 : Y.left.OpenCover := Scheme.Cover.mkOfCovers {𝔭 : Ideal (𝓞 L) // 𝔭.IsMaximal}
    (fun t => pullback Y.hom (gs t)) (fun t => pullback.fst Y.hom (gs t)) hcov
    (fun t => inferInstance)
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 (fun t => ?_)
  show IsOpenImmersion (pullback.snd f.left (pullback.fst Y.hom (gs t)))
  have heq : pullback.snd f.left (pullback.fst Y.hom (gs t)) =
      (pullbackRightPullbackFstIso Y.hom (gs t) f.left ≪≫
        pullback.congrHom (Over.w f) rfl).hom ≫ ((Over.pullback (gs t)).map f).left := by
    apply pullback.hom_ext
    · simp [Over.pullback_map_left, pullbackRightPullbackFstIso_hom_fst_assoc, pullback.condition]
    · simp [Over.pullback_map_left]
  rw [heq]
  haveI := hsO t
  infer_instance

/-- reduct-glue's leaf `OpenImmersionOfLocal` is a theorem from the printed EGA IV 8.10.5. -/
theorem openImmersionOfLocal_of_printed (hE : EGAIV_8_10_5_openImm) :
    ReductGlue.OpenImmersionOfLocal :=
  openImmersionLocalization hE

/-- **SS2 from four printed-form leaves and two named glue Props** (compiled). -/
theorem semistableNeronBaseChange_of_printed' (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3) (hE : EGAIV_8_10_5_openImm) (g1 : IdentityComponentGroupModel)
    (g2 : IdentityComponentFromPrinted) : ZInQ.HeightSplit.SemistableNeronBaseChange :=
  semistableNeronBaseChange_of_printed hB h3 h7 hE g1 g2 openImmersionLocalization

end CToPrinted

#print axioms CToPrinted.neronLocalizesDVR_of_printed
#print axioms CToPrinted.semistableNeronBaseChange_of_printedBLR
#print axioms CToPrinted.semistableNeronBaseChange_of_printed
#print axioms CToPrinted.faltingsLemma5BC_of_printed
#print axioms CToPrinted.openImmersionLocalization
#print axioms CToPrinted.semistableNeronBaseChange_of_printed'
