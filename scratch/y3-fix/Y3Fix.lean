import ZInQKernel.Contrib.OneProof.ShimuraY3Print
import ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard

set_option linter.all false

noncomputable section

namespace Y3Fix

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open ShimuraCFT RayClassCFT

/-! ## 1. A `ℚ̄`-point from a `ℂ`-point -/

/-- **A proper `ℚ`-scheme with a `ℂ`-point has a `ℚ̄`-point**: it is nonempty and quasi-compact, so it has a
closed point, whose residue field is finite over `ℚ` (Jacobson; `HDec.ModelGlue.exists_qbarPt`). -/
theorem nonempty_qbar_of_cpt (Y : Over (Spec (CommRingCat.of ℚ))) (hP : IsProper Y.hom)
    (y : fieldPt ℂ ⟶ Y) : Nonempty (fieldPt Qbar ⟶ Y) := by
  haveI := hP
  haveI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := Y.left) isClosed_univ
    ⟨y.left.base (IsLocalRing.closedPoint ℂ), trivial⟩
  obtain ⟨-, y0, -⟩ := HDec.ModelGlue.exists_qbarPt Y x hx
  exact ⟨y0⟩

/-! ## 2. The level structure in its printed form -/

section Level

open MonoidalCategory CartesianMonoidalCategory MonObj PkgI3
open scoped CategoryTheory.Obj
open SGRSplit

/-- `QMAbScheme` without its level clause `eta_ker` (the data and the group, ring and linearity clauses,
verbatim). -/
structure QMAbSchemeNL (S : Scheme.{0}) extends QMFamily S where
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

/-- The section `η(a)` as a map from the unit of `Over S`. -/
def secF {S : Scheme.{0}} (𝒜 : QMFamily S) (a : O) : 𝟙_ (Over S) ⟶ 𝒜.F :=
  Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a)

/-- **The printed level condition** (Mumford, *GIT*, Def. 7.1, in its `𝒪`-linear form): at every geometric
point `s : Spec k → S` (`k` algebraically closed), the homomorphism `η_s : 𝒪/3𝒪 → A_s(k)[3]`,
`a ↦ η(a)(s)`, is bijective; here `A_s = s^*A` is the geometric fibre (Mathlib's pullback, with the group law
of the pulled-back group object) and `A_s(k)[3]` its group of `k`-points `x` with `x³ = 1`. -/
def LevelPrint {S : Scheme.{0}} (𝒜 : QMAbSchemeNL S) : Prop :=
  letI := 𝒜.grp
  ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
    (∀ a : O, s ≫ 𝒜.eta a = s ≫ 𝒜.eta 0 ↔ ∃ b : O, a = 3 * b) ∧
    ∀ x : AbVar.ptObj (K := k) k ⟶ (Over.pullback s).obj 𝒜.F, x ^ 3 = 1 →
      ∃ a : O, x = cpt s ≫ (Over.pullback s).map (secF 𝒜.toQMFamily a)

/-- **An abelian surface scheme with QM by `𝒪` and a full level-3 structure, in the printed form**: the
level clause is `LevelPrint`. -/
structure QMAbSchemeP (S : Scheme.{0}) extends QMAbSchemeNL S where
  level : LevelPrint toQMAbSchemeNL

/-- The kernel's form forgets to `QMAbSchemeNL`. -/
def toNL {S : Scheme.{0}} (𝒜 : QMAbScheme S) : QMAbSchemeNL S :=
  letI := 𝒜.grp
  { toQMFamily := 𝒜.toQMFamily, grp := 𝒜.grp, geomConn := 𝒜.geomConn, one_eq := 𝒜.one_eq,
    iota_hom := 𝒜.iota_hom, iota_one := 𝒜.iota_one, iota_mul := 𝒜.iota_mul, iota_add := 𝒜.iota_add,
    eta_add := 𝒜.eta_add, eta_linear := 𝒜.eta_linear, eta_three := 𝒜.eta_three }

/-- **Printed form ⇒ the kernel's form**: injectivity at a field point follows from injectivity at the
geometric point over it (`Spec K̄ → Spec K` is an epimorphism). -/
def toKer {S : Scheme.{0}} (𝒜 : QMAbSchemeP S) : QMAbScheme S :=
  letI := 𝒜.grp
  { toQMFamily := 𝒜.toQMFamily, grp := 𝒜.grp, geomConn := 𝒜.geomConn, one_eq := 𝒜.one_eq,
    iota_hom := 𝒜.iota_hom, iota_one := 𝒜.iota_one, iota_mul := 𝒜.iota_mul, iota_add := 𝒜.iota_add,
    eta_add := 𝒜.eta_add, eta_linear := 𝒜.eta_linear, eta_three := 𝒜.eta_three
    eta_ker := fun K _ s a => by
      constructor
      · intro h
        have hp : Epi (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) :=
          Flat.epi_of_flat_of_surjective _
        refine ((𝒜.level (AlgebraicClosure K)
          (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ s)).1 a).1 ?_
        rw [Category.assoc, h, Category.assoc]
      · rintro ⟨b, rfl⟩
        rw [𝒜.eta_three] }

theorem toKer_toQMFamily {S : Scheme.{0}} (𝒜 : QMAbSchemeP S) : (toKer 𝒜).toQMFamily = 𝒜.toQMFamily := rfl

/-- **The fibre of a kernel-form QM abelian scheme at a field point of characteristic 0 is an object, with
level points the pulled-back sections** (SGRSplit's `qmAbFieldFibre_of`, verbatim, with the object exhibited). -/
theorem fibre_level (hI : SmoothGeomConnIntegral) (hT : AbVarEndTorsionFree) {S : Scheme.{0}}
    (𝒜 : QMAbScheme S) {K : Type} [Field K] [CharZero K] (y : Spec (CommRingCat.of K) ⟶ S) :
    ∃ (hdim : (fibreAbVar hI 𝒜 y).dim = 2) (q : QMStr (fibreAbVar hI 𝒜 y)) (e : Level3 q),
      ∀ a : O, Additive.toMul (e.eta a) = cpt y ≫ (Over.pullback y).map (sec 𝒜 a) := by
  letI := 𝒜.grp
  have := 𝒜.proper
  have := 𝒜.smooth
  have := 𝒜.geomConn
  let Fs : Over (Spec (CommRingCat.of K)) := (Over.pullback y).obj 𝒜.F
  have hsm2 : SmoothOfRelativeDimension 2 Fs.hom := by dsimp [Fs]; infer_instance
  have : Smooth Fs.hom := SmoothOfRelativeDimension.smooth 2 _
  set AF : AbVar K := fibreAbVar hI 𝒜 y with hAF
  -- the level points
  let pt : O → AF.Pt K := fun a => cpt y ≫ (Over.pullback y).map (sec 𝒜 a)
  have hpt : ∀ a, (pt a).left ≫ pullback.fst 𝒜.F.hom y = y ≫ 𝒜.eta a := fun a => by
    change ((cpt y).left ≫ ((Over.pullback y).map (sec 𝒜 a)).left) ≫ _ = _
    rw [Category.assoc, map_left_fst, ← Category.assoc, cpt_fst]
    rfl
  have hpt_eq : ∀ a b, pt a = pt b ↔ y ≫ 𝒜.eta a = y ≫ 𝒜.eta b := fun a b => by
    constructor
    · intro h; rw [← hpt, ← hpt, h]
    · intro h
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · exact (hpt a).trans (h.trans (hpt b).symm)
      · exact (Over.w (pt a)).trans (Over.w (pt b)).symm
  -- dimension
  have hdim : AF.dim = 2 := by
    have : GeometricallyIntegral Fs.hom := (fibreAbVar hI 𝒜 y).geomInt
    have : IrreducibleSpace Fs.left := GeometricallyIrreducible.irreducibleSpace_of_subsingleton Fs.hom
    have : JacobsonSpace Fs.left := LocallyOfFiniteType.jacobsonSpace Fs.hom
    obtain ⟨z, -, hzc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set Fs.left))
      ⟨(pt 0).left.base (IsLocalRing.closedPoint K), trivial⟩ isClosed_univ.isLocallyClosed
    have h1 := (ZInQ.Contrib.Dim.ringKrullDim_stalk_of_smoothOfRelativeDimension Fs.hom 2 z hzc).1
    have h2 := (ZInQ.Contrib.Dim.topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth Fs.hom z hzc).1
    change topologicalKrullDim Fs.left = 2
    rw [h2, h1]; rfl
  -- `ι` on the fibre
  have hmon : ∀ a, IsMonHom ((Over.pullback y).map (fa 𝒜 a)) := fun a => by
    have : IsMonHom (fa 𝒜 a) := 𝒜.iota_hom a
    infer_instance
  let jf : O → AbVar.End AF := fun a => @AbVar.Hom.mk' K _ AF AF ((Over.pullback y).map (fa 𝒜 a)) (hmon a)
  have hjf : ∀ a, (jf a).hom = (Over.pullback y).map (fa 𝒜 a) := fun a => rfl
  have hfa1 : fa 𝒜 1 = 𝟙 _ := Over.OverMorphism.ext 𝒜.iota_one
  have hfamul : ∀ a b, fa 𝒜 (a * b) = fa 𝒜 b ≫ fa 𝒜 a := fun a b =>
    Over.OverMorphism.ext (𝒜.iota_mul a b)
  have hfaadd : ∀ a b, fa 𝒜 (a + b) = fa 𝒜 a * fa 𝒜 b := fun a b => 𝒜.iota_add a b
  have hfa0 : fa 𝒜 0 = 1 := by
    have h := hfaadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  let jq : O →+* AbVar.End AF :=
    { toFun := jf
      map_one' := AbVar.Hom.ext' (by rw [hjf, hfa1]; exact CategoryTheory.Functor.map_id _ _)
      map_mul' := fun a b => AbVar.Hom.ext' (by
        rw [hjf, hfamul]; exact CategoryTheory.Functor.map_comp _ _ _)
      map_zero' := AbVar.Hom.ext' (by
        rw [hjf, hfa0]; exact CategoryTheory.Functor.map_one _)
      map_add' := fun a b => AbVar.Hom.ext' (by
        rw [hjf, hfaadd]; exact CategoryTheory.Functor.map_mul _ _ _) }
  have hsec_lin : ∀ a b, sec 𝒜 (a * b) = sec 𝒜 b ≫ fa 𝒜 a := fun a b =>
    Over.OverMorphism.ext (𝒜.eta_linear a b)
  have hpt_lin : ∀ a b, pt (a * b) = pt b ≫ (jq a).hom := fun a b => by
    change cpt y ≫ (Over.pullback y).map (sec 𝒜 (a * b)) = (cpt y ≫ (Over.pullback y).map (sec 𝒜 b)) ≫
      (Over.pullback y).map (fa 𝒜 a)
    rw [hsec_lin, CategoryTheory.Functor.map_comp, Category.assoc]
  -- `jq(d) = 0 ⇒ d ∈ 3𝒪`
  have hker1 : ∀ d : O, jq d = 0 → ∃ e : O, d = 3 * e := fun d hd => by
    rw [← 𝒜.eta_ker K y d, ← hpt_eq]
    have h1 := hpt_lin d 1
    rw [_root_.mul_one, hd, AbVar.Hom.hom_zero, MonObj.comp_one] at h1
    have h0 := hpt_lin 0 1
    rw [_root_.mul_one, map_zero, AbVar.Hom.hom_zero, MonObj.comp_one] at h0
    rw [h1, h0]
  have hinj : Function.Injective jq := by
    have hz : ∀ c, jq c = 0 → c = 0 := fun c hc => by
      apply O_eq_zero_of_forall_dvd
      intro k
      induction k with
      | zero => exact ⟨c, by simp⟩
      | succ k ih =>
        obtain ⟨d, hd⟩ := ih
        have hd0 : jq d = 0 := by
          apply hT K AF (3 ^ k) (jq d) (by positivity)
          rw [nsmul_eq_mul, ← map_natCast jq, ← map_mul]
          push_cast
          rw [← hd, hc]
        obtain ⟨e, he⟩ := hker1 d hd0
        exact ⟨e, by rw [hd, he, pow_succ, _root_.mul_assoc]⟩
    intro a b hab
    have := hz (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp this
  let q : QMStr AF := ⟨jq, hinj⟩
  -- the level structure
  have hsec0 : sec 𝒜 0 = 1 := by
    apply Over.OverMorphism.ext
    change 𝒜.eta 0 = (toUnit (𝟙_ (Over S)) ≫ η[𝒜.F]).left
    rw [toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp, 𝒜.one_eq]
  have hpt0 : pt 0 = 1 := by
    change cpt y ≫ (Over.pullback y).map (sec 𝒜 0) = 1
    rw [hsec0, CategoryTheory.Functor.map_one, MonObj.comp_one]
  have hptadd : ∀ a b, pt (a + b) = pt a * pt b := fun a b => by
    change cpt y ≫ (Over.pullback y).map (sec 𝒜 (a + b)) = _
    rw [show sec 𝒜 (a + b) = sec 𝒜 a * sec 𝒜 b from 𝒜.eta_add a b,
      CategoryTheory.Functor.map_mul, MonObj.comp_mul]
    rfl
  let e0 : O →+ Additive (AF.Pt K) :=
    { toFun := fun a => Additive.ofMul (pt a)
      map_zero' := by rw [hpt0]; rfl
      map_add' := fun a b => by rw [hptadd]; rfl }
  let e : Level3 q :=
    { eta := e0
      linear := fun a b => by
        change Additive.ofMul (pt (a * b)) = Additive.ofMul (pt b ≫ (jq a).hom)
        rw [hpt_lin]
      ker := fun a => by
        change Additive.ofMul (pt a) = Additive.ofMul (1 : AF.Pt K) ↔ _
        rw [EmbeddingLike.apply_eq_iff_eq, ← hpt0, hpt_eq, 𝒜.eta_ker] }
  exact ⟨hdim, q, e, fun a => rfl⟩

/-- `CharZero` of a field with a point of a `ℚ`-scheme. -/
theorem charZero_of_pt {S : Over (Spec (CommRingCat.of ℚ))} {k : Type} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ S.left) : CharZero k := by
  let f : ℚ →+* k := (Spec.preimage (s ≫ S.hom)).hom
  letI := f.toAlgebra
  exact charZero_of_injective_algebraMap f.injective

/-- **The kernel's form ⇒ printed form, over a `ℚ`-scheme** (given `TorsionStructure`): injectivity at
geometric points is `eta_ker`; ontoness onto `A_s(k)[3]` is `Level3.onto` on the fibre object. -/
theorem levelPrint_of_ker (hT : ObjBridge.TorsionStructure) {S : Over (Spec (CommRingCat.of ℚ))}
    (𝒜 : QMAbScheme S.left) : LevelPrint (toNL 𝒜) := by
  intro k _ _ s
  haveI := charZero_of_pt s
  refine ⟨fun a => 𝒜.eta_ker k s a, fun x hx => ?_⟩
  obtain ⟨hdim, q, e, he⟩ := fibre_level smoothGeomConnIntegral abVarEndTorsionFree 𝒜 s
  let P : QML3 k := ⟨fibreAbVar smoothGeomConnIntegral 𝒜 s, hdim, q, e⟩
  let x' : P.A.Pt k := x
  have hx' : x' ^ 3 = 1 := hx
  obtain ⟨a, ha⟩ := Level3.onto hT P (bcPt P.A x') (by
    rw [bcPt, ← MonObj.comp_pow, hx']
    exact MonObj.comp_one _)
  refine ⟨a, ?_⟩
  have := bcPt_injective P.A ha
  exact (this.symm.trans (he a))

/-- The kernel's form gives the printed form (over a `ℚ`-scheme, given `TorsionStructure`). -/
def ofKer (hT : ObjBridge.TorsionStructure) {S : Over (Spec (CommRingCat.of ℚ))} (𝒜 : QMAbScheme S.left) :
    QMAbSchemeP S.left :=
  { toNL 𝒜 with level := levelPrint_of_ker hT 𝒜 }

theorem ofKer_toQMFamily (hT : ObjBridge.TorsionStructure) {S : Over (Spec (CommRingCat.of ℚ))}
    (𝒜 : QMAbScheme S.left) : (ofKer hT 𝒜).toQMFamily = 𝒜.toQMFamily := rfl

end Level

/-! ## 3. The clause lists in printed form -/

/-- **R1univ, printed form**: `R1univAbProps` with the printed level structure (`QMAbSchemeP`). -/
def R1univAbPropsP (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ 𝒜' : QMAbSchemeP S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
        IsFibreOf 𝒜'.toQMFamily s.left P) →
      ∃ g : S ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S) (P : QML3 K),
        IsFibreOf 𝒜'.toQMFamily s.left P → Φ K (s ≫ g) = M3.mk P

/-- **R1fam, printed form**: the universal object has the printed level structure. -/
def R1famAbPropsP (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ 𝒜 : QMAbSchemeP Y.left, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
    Φ K y = M3.mk P → IsFibreOf 𝒜.toQMFamily y.left P

/-- **The fine-moduli clause list in printed form**: `R1fpPropsAb` with the printed level structure and
**without** the clause `Nonempty (fieldPt Qbar ⟶ Y)` (which no representability theorem states). -/
def R1fpPropsAbP (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famAbPropsP Y Φ ∧ R1univAbPropsP Y Φ

/-- The kernel's clause list without the `ℚ̄`-point. -/
def R1fpPropsAbNP (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famAbProps Y Φ ∧ R1univAbProps Y Φ

/-- **Printed list ⇒ the kernel's list without the point** (given `TorsionStructure`). -/
theorem np_of_P (hT : ObjBridge.TorsionStructure) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsAbP Y Φ) : R1fpPropsAbNP Y Φ := by
  obtain ⟨hp, hs, hn, ⟨𝒜, h𝒜⟩, hU⟩ := h
  exact ⟨hp, hs, hn, ⟨toKer 𝒜, h𝒜⟩, fun S hpS hsS 𝒜' hall => hU S hpS hsS (ofKer hT 𝒜') hall⟩

/-- **The kernel's list ⇒ printed list** (given `TorsionStructure`). -/
theorem P_of_np (hT : ObjBridge.TorsionStructure) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsAbNP Y Φ) : R1fpPropsAbP Y Φ := by
  obtain ⟨hp, hs, hn, ⟨𝒜, h𝒜⟩, hU⟩ := h
  exact ⟨hp, hs, hn, ⟨ofKer hT (S := Y) 𝒜, h𝒜⟩, fun S hpS hsS 𝒜' hall => hU S hpS hsS (toKer 𝒜') hall⟩

theorem np_of_ab {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (h : R1fpPropsAb Y Φ) :
    R1fpPropsAbNP Y Φ :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem ab_of_np {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (h : R1fpPropsAbNP Y Φ)
    (hpt : Nonempty (fieldPt Qbar ⟶ Y)) : R1fpPropsAb Y Φ :=
  ⟨h.1, h.2.1, hpt, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-! ## 4. Pinning without the point (elkies-print's `compare_iso_ab`, the point clause unused) -/

theorem phi_part_np {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (hU : R1univAbProps Y Φ) (h1' : R1fpPropsAbNP Y' Φ') :
    ∃ g : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g) := by
  obtain ⟨hp', hs', -, ⟨𝒜', h𝒜'⟩, -⟩ := h1'
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), ∃ P : QML3 K,
      IsFibreOf 𝒜'.toQMFamily s.left P :=
    fun K _ _ s => ⟨Quotient.out (Φ' K s), h𝒜' K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g, hg⟩ := hU Y' hp' hs' 𝒜' hall
  refine ⟨g, fun K _ _ y => ?_⟩
  rw [hg K y _ (h𝒜' K y _ (Quotient.out_eq _).symm)]
  exact (Quotient.out_eq _).symm

theorem compare_iso_np {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (h : R1fpPropsAbNP Y Φ) (h' : R1fpPropsAbNP Y' Φ') :
    ∃ g : Y' ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g.hom) := by
  obtain ⟨g, hg⟩ := phi_part_np h.2.2.2.2 h'
  obtain ⟨g', hg'⟩ := phi_part_np h'.2.2.2.2 h
  have e1 : g' ≫ g = 𝟙 Y := HDec.QMSplit.Moduli.eq_id_of_fieldPts h.1 h.2.1 _ fun K _ _ y =>
    (Φ K).injective (by rw [← Category.assoc, ← hg K (y ≫ g'), ← hg' K y])
  have e2 : g ≫ g' = 𝟙 Y' := HDec.QMSplit.Moduli.eq_id_of_fieldPts h'.1 h'.2.1 _ fun K _ _ y =>
    (Φ' K).injective (by rw [← Category.assoc, ← hg' K (y ≫ g), ← hg K y])
  exact ⟨⟨g, g', e2, e1⟩, hg⟩

/-! ## 5. The leaves (lattice form) and the discharge -/

/-- **LEAF `Y3FineModuliAbP`** (printed form; see the module docstring). -/
def Y3FineModuliAbP : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpPropsAbP Y Φ

/-- The canonical-model leaf over the printed clause list (lattice form of the moduli clause). -/
def DeligneCanonicalModelY3EveryP : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpPropsAbP Y Φ →
    ∃ Ψ, DeligneBodyAt Y Φ Ψ ∧ ModuliAtUnits Y Φ Ψ

/-- **The discharge (lattice form)**: the point comes from `Ψ(i, 1)`. -/
theorem field_of_printP (hT : ObjBridge.TorsionStructure) (h1 : Y3FineModuliAbP)
    (h2 : DeligneCanonicalModelY3EveryP) : ShimuraMainThmIDeligneY3AbU := by
  obtain ⟨Y, Φ, h⟩ := h1
  obtain ⟨Ψ, hb, hU⟩ := h2 Y Φ h
  exact ⟨Y, Φ, ab_of_np (np_of_P hT h) (nonempty_qbar_of_cpt Y h.1 (Ψ UpperHalfPlane.I 1)), Ψ, hb, hU⟩

theorem y3FineModuliAbP_of_field (hT : ObjBridge.TorsionStructure) (h : ShimuraMainThmIDeligneY3AbU) :
    Y3FineModuliAbP := by
  obtain ⟨Y, Φ, h1, -⟩ := h
  exact ⟨Y, Φ, P_of_np hT (np_of_ab h1)⟩

theorem deligneP_of_field (hT : ObjBridge.TorsionStructure) (h : ShimuraMainThmIDeligneY3AbU) :
    DeligneCanonicalModelY3EveryP := by
  obtain ⟨Y, Φ, h1, Ψ, hb, hU⟩ := h
  intro Y' Φ' h'
  obtain ⟨k, hk⟩ := compare_iso_np (np_of_ab h1) (np_of_P hT h')
  exact ⟨_, Y3ABUPrint.body_transport k hk hb hU⟩

end Y3Fix
#print axioms Y3Fix.field_of_printP
#print axioms Y3Fix.deligneP_of_field
