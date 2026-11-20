import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.PrimitivePole
import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.AffineComparison

/-! The projective chart at the identity of the elliptic curve.
On-the-spot (c), tex 1785–1787. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Topology Function UpperHalfPlane WeierstrassCurve
open ModularCurve ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.ParamAtScale
open ZInQ.Manuscript.RC.ModFnField

namespace ZInQ.Manuscript.RC.ModFnClassify

theorem qParam_one_zpow (z : ℂ) (n : ℤ) :
    Periodic.qParam 1 z ^ n = Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z) := by
  rw [Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_int_mul]
  congr 1
  ring

private theorem eq_germ_of_eq_tail {f g : ℂ → ℂ}
    (hf : MeromorphicOn f {z | 0 < z.im}) (hg : MeromorphicOn g {z | 0 < z.im})
    (he : ∀ᶠ τ : ℍ in atImInfty, f τ = g τ) (τ : ℍ) :
    f =ᶠ[𝓝[≠] (τ : ℂ)] g := by
  obtain ⟨T, hT⟩ := (atImInfty_mem _).mp he
  let z : ℂ := ⟨0, max T 0 + 1⟩
  have hz : max T 0 < z.im := by dsimp [z]; linarith
  have hf' : MeromorphicOn (fun w => f w - g w) {z | 0 < z.im} :=
    fun w hw => (hf w hw).sub (hg w hw)
  have ho : meromorphicOrderAt (fun w => f w - g w) z = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)] with w hw
    have hw' : (0 : ℝ) < w.im := (le_max_right _ _).trans_lt hw
    exact sub_eq_zero.mpr (hT ⟨w, hw'⟩ ((le_max_left _ _).trans hw.le))
  have h := hf'.meromorphicOrderAt_eq_top_of_isPreconnected
    (convex_halfSpace_im_gt 0).isPreconnected ((le_max_right _ _).trans_lt hz) τ.im_pos ho
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp h] with w hw
  exact sub_eq_zero.mp hw

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evalSection_eq_stalk {Y : Scheme.{0}} {q : Y ⟶ Spec (.of ℚ)}
    (u : FieldPoint q ℂ) (V : Y.Opens) (hV : u.val default ∈ V)
    (hc : u.val (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ V) (r : Γ(Y, V)) :
    u.evalSection V hV r =
      (Scheme.stalkClosedPointTo u.val).hom (Y.presheaf.germ V _ hc r) := by
  have h := Scheme.germ_stalkClosedPointTo u.val V hc
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom] at h
  exact (congrArg (fun a : Γ(Y, V) ⟶ CommRingCat.of ℂ => a r) h).symm

theorem evalSection_ZOverY_at_identity (E : WeierstrassCurve ℚ)
    (u : FieldPoint (projectiveOverQ E) ℂ) (hO : u.val default = pointO E)
    (hV : u.val default ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 1)) :
    u.evalSection _ hV (sectionZOverY E) = 0 := by
  have he : IsLocalRing.closedPoint (CommRingCat.of ℂ) = (default : Spec (.of ℂ)) :=
    Subsingleton.elim _ _
  have hOc : u.val (IsLocalRing.closedPoint (CommRingCat.of ℂ)) = pointO E :=
    (congrArg (fun x : Spec (.of ℂ) => u.val x) he).trans hO
  have hVc : u.val (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ _ :=
    hOc.symm ▸ pointO_mem_basicOpen E
  rw [evalSection_eq_stalk u _ _ hVc]
  have h (p : Proj E.toProjective.grading) (hp : p = pointO E)
      (hm : p ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 1)) :
      (Proj E.toProjective.grading).presheaf.germ _ p hm (sectionZOverY E) ∈
        IsLocalRing.maximalIdeal ((Proj E.toProjective.grading).presheaf.stalk p) := by
    subst p
    exact germ_sectionZOverY_mem_maximalIdeal E
  have hz := map_nonunit (Scheme.stalkClosedPointTo u.val).hom _ (h _ hOc hVc)
  change ¬IsUnit ((Scheme.stalkClosedPointTo u.val).hom
    ((Proj E.toProjective.grading).presheaf.germ _ _ hVc (sectionZOverY E))) at hz
  exact not_ne_iff.mp (fun hne => hz (isUnit_iff_ne_zero.mpr hne))

/-- Pullback of any regular projective section has the meromorphic function
and Laurent expansion determined by its image under the generic map. -/
theorem pullback_expansion {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {N : ℕ} [NeZero N] (X : X0Model N)
    (π : X.X ⟶ Proj E.toProjective.grading) (hQ : π ≫ projectiveOverQ E = X.overQ)
    (ι : E.toAffine.FunctionField →+* modularFunctionField N)
    (hgen : letI := X.integral; X.X.fromSpecFunctionField ≫ π =
      Spec.map (CommRingCat.ofHom (X.functionField.symm.toRingHom.comp
        (ι.comp (projFunctionFieldEquiv E).toRingHom))) ≫
          (Proj E.toProjective.grading).fromSpecFunctionField)
    (V : (Proj E.toProjective.grading).Opens) [Nonempty V]
    (r : Γ(Proj E.toProjective.grading, V)) (τ : ℍ)
    (hτ : ((X.complexPoint τ).comp π hQ).val default ∈ V) :
    let a := ι (projFunctionFieldEquiv E ((Proj E.toProjective.grading).germToFunctionField V r))
    ∃ G : ℂ → ℂ, MeromorphicOn G {z | 0 < z.im} ∧
      AnalyticAt ℂ G (τ : ℂ) ∧
      Realizes (complexify (a : LaurentSeries ℚ)) (fun σ => G σ) ∧
      ((X.complexPoint τ).comp π hQ).evalSection V hτ r = G τ := by
  let := X.integral
  have hv : (X.complexPoint τ).val default ∈ π ⁻¹ᵁ V := hτ
  let : Nonempty (π ⁻¹ᵁ V) := ⟨⟨_, hv⟩⟩
  obtain ⟨G, T, hG, hT, hval⟩ := X.sectionExpansion (π ⁻¹ᵁ V) (π.app V r)
  have he : X.functionField (X.X.germToFunctionField (π ⁻¹ᵁ V) (π.app V r)) =
      ι (projFunctionFieldEquiv E ((Proj E.toProjective.grading).germToFunctionField V r)) := by
    rw [germToFunctionField_pullback _ _ hgen]
    exact X.functionField.apply_symm_apply _
  refine ⟨G, hG, (hval τ hv).1, ?_, ?_⟩
  · refine ((eventually_gt_atTop T).comap UpperHalfPlane.im).mono fun σ hσ => ?_
    simpa only [complexify_coeff, qParam_one_zpow, ← he] using hT σ hσ
  · rw [evalSection_comp]
    exact (hval τ hv).2

private theorem same_series_same_germ {a : LaurentSeries ℂ} {f g : ℂ → ℂ}
    (hf : MeromorphicOn f {z | 0 < z.im}) (hg : MeromorphicOn g {z | 0 < z.im})
    (ha : Realizes a (fun τ => f τ)) (hb : Realizes a (fun τ => g τ)) (τ : ℍ) :
    f =ᶠ[𝓝[≠] (τ : ℂ)] g := by
  apply eq_germ_of_eq_tail hf hg _ τ
  filter_upwards [ha, hb] with σ hσ hσ'
  exact hσ.unique hσ'

/-- The identity of the projective Weierstrass model occurs exactly at
interior lattice values of the analytic primitive. -/
theorem projective_identity_iff_lattice (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {N : ℕ} [NeZero N] (X : X0Model N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℚ} (hκ : κ ≠ 0)
    (π : X.X ⟶ Proj E.toProjective.grading) (hQ : π ≫ projectiveOverQ E = X.overQ)
    (ι : E.toAffine.FunctionField →+* modularFunctionField N)
    (hgen : letI := X.integral; X.X.fromSpecFunctionField ≫ π =
      Spec.map (CommRingCat.ofHom (X.functionField.symm.toRingHom.comp
        (ι.comp (projFunctionFieldEquiv E).toRingHom))) ≫
          (Proj E.toProjective.grading).fromSpecFunctionField)
    (hx : Realizes (complexify (ι E.toAffine.genericX)) (fun τ => xCoordinate E f L κ τ))
    (hy : Realizes (complexify (ι E.toAffine.genericY)) (fun τ => yCoordinate E f L κ τ))
    (τ : ℍ) :
    ((X.complexPoint τ).comp π hQ).val default = pointO E ↔ scaledPrimitive f κ τ ∈ L.lattice := by
  obtain ⟨hmX, hmY⟩ := coordinates_meromorphic E f L κ
  let u := (X.complexPoint τ).comp π hQ
  constructor
  · intro hO
    by_contra hl
    have hV : u.val default ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 1) :=
      hO.symm ▸ pointO_mem_basicOpen E
    obtain ⟨G, hG, hGa, hGr, hval⟩ :=
      pullback_expansion X π hQ ι hgen _ (sectionZOverY E) τ hV
    rw [projFunctionFieldEquiv_sectionZOverY] at hGr
    have hformal : complexify (ι E.toAffine.genericY : LaurentSeries ℚ) *
        complexify (ι E.toAffine.genericY⁻¹ : LaurentSeries ℚ) = 1 := by
      let t : E.toAffine.FunctionField →+* LaurentSeries ℂ :=
        complexify.comp ((modularFunctionField N).toSubfield.subtype.comp ι)
      change t E.toAffine.genericY * t E.toAffine.genericY⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ (genericY_ne_zero E), map_one]
    have hs := hy.mul hGr
    rw [hformal] at hs
    have hm : MeromorphicOn (fun z => yCoordinate E f L κ z * G z) {z | 0 < z.im} :=
      fun z hz => (hmY z hz).mul (hG z hz)
    have he := same_series_same_germ hm (fun _ _ => MeromorphicAt.const _ _) hs
      (by simpa using Realizes.const 1) τ
    have hp : AnalyticAt ℂ (scaledPrimitive f κ) (τ : ℂ) := scaledPrimitive_analytic f κ τ.im_pos
    have hw := (L.analyticOnNhd_weierstrassP _ hl).comp hp
    have hw' := (L.analyticOnNhd_derivWeierstrassP _ hl).comp hp
    have hay : AnalyticAt ℂ (yCoordinate E f L κ) (τ : ℂ) :=
      ((hw'.sub (analyticAt_const.mul (hw.sub analyticAt_const))).sub
        analyticAt_const).div_const
    have hc := hay.continuousAt.mul hGa.continuousAt
    have h := ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hc continuousAt_const).mp he).eq_of_nhds
    have hz := evalSection_ZOverY_at_identity E u hO hV
    have hgzero : G τ = 0 := hval.symm.trans hz
    change yCoordinate E f L κ τ * G τ = 1 at h
    rw [hgzero, mul_zero] at h
    exact zero_ne_one h
  · intro hl
    by_contra hO
    have hV : u.val default ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2) := by
      rw [Proj.mem_basicOpen]
      intro hZ
      exact hO (eq_pointO_of_coord_mem E _ (coord_zero_mem_of_coord_two_mem E _ hZ) hZ)
    obtain ⟨G, hG, hGa, hGr, _⟩ :=
      pullback_expansion X π hQ ι hgen _ (sectionXOverZ E) τ hV
    rw [projFunctionFieldEquiv_sectionXOverZ] at hGr
    exact xCoordinate_no_analytic_germ_at_lattice E f hf hL hκ τ hl
      ⟨G, hGa, same_series_same_germ hG hmX hGr hx τ⟩

set_option backward.isDefEq.respectTransparency false in
private theorem appLE_of_lift {Y : Scheme.{0}} {V : Y.Opens} {F : Type} [Field F]
    (u : Spec (.of F) ⟶ Y) (h : u default ∈ V)
    (l : Spec (.of F) ⟶ V.toScheme) (hl : l ≫ V.ι = u) :
    V.topIso.inv ≫ l.appTop = u.appLE V ⊤ (by
      intro p _
      show u p ∈ V
      rwa [Subsingleton.elim p (default : Spec (.of F))]) := by
  have he : V.ι.appLE V ⊤ V.ι_preimage_self.ge = V.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  rw [← he]
  have hcomp := Scheme.Hom.appLE_comp_appLE l V.ι V ⊤ ⊤ V.ι_preimage_self.ge le_rfl
  subst u
  exact hcomp

set_option backward.isDefEq.respectTransparency false in
private theorem evalSection_on_zChart (E : WeierstrassCurve ℚ)
    (u : FieldPoint (projectiveOverQ E) ℂ)
    (h : u.val default ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2))
    (l : Spec (.of ℂ) ⟶ (Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)).toScheme)
    (hl : l ≫ (Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)).ι = u.val)
    (r : E.toAffine.CoordinateRing) :
    let a := l ≫ (Proj.basicOpenIsoSpec E.toProjective.grading (E.toProjective.coord 2)
      (E.toProjective.coord_mem_grading 2) (by norm_num)).hom ≫
        Spec.map (affineEquivZChart E).toCommRingCatIso.hom
    ((Scheme.ΓSpecIso _).inv ≫ a.appTop ≫ (Scheme.ΓSpecIso _).hom) r =
      u.evalSection _ h ((Proj.awayToSection E.toProjective.grading (E.toProjective.coord 2)).hom
        ((affineEquivZChart E) r)) := by
  dsimp only
  simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality_assoc,
    Iso.inv_hom_id_assoc, Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top]
  have hh := appLE_of_lift u.val h l hl
  simp only [hh, ← Category.assoc]
  rfl

/-- On the affine chart, `projectiveValue` uses the evaluations of the
regular sections `X/Z` and `Y/Z`. -/
theorem projectiveValue_on_affine (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (u : FieldPoint (projectiveOverQ E) ℂ) (hO : u.val default ≠ pointO E)
    (h : u.val default ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)) :
    ∃ hxy : (E.baseChange ℂ).toAffine.Nonsingular
        (u.evalSection _ h (sectionXOverZ E)) (u.evalSection _ h (sectionYOverZ E)),
      projectiveValue u.val = .some _ _ hxy := by
  classical
  let V := Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)
  have hr : Set.range u.val ⊆ Set.range V.ι := by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a (default : Spec (.of ℂ))]
    exact ⟨⟨_, h⟩, rfl⟩
  let l := IsOpenImmersion.lift V.ι u.val hr
  let a := l ≫ (Proj.basicOpenIsoSpec E.toProjective.grading (E.toProjective.coord 2)
    (E.toProjective.coord_mem_grading 2) (by norm_num)).hom ≫
      Spec.map (affineEquivZChart E).toCommRingCatIso.hom
  let eval : E.toAffine.CoordinateRing → ℂ := fun r =>
    ((Scheme.ΓSpecIso _).inv ≫ a.appTop ≫ (Scheme.ΓSpecIso _).hom) r
  have hval := evalSection_on_zChart E u h l (IsOpenImmersion.lift_fac _ _ hr)
  have hx : eval (AdjoinRoot.of E.toAffine.polynomial Polynomial.X) =
      u.evalSection _ h (sectionXOverZ E) := by
    have hh := hval (AdjoinRoot.of E.toAffine.polynomial Polynomial.X)
    simpa only [eval, sectionXOverZ, show (affineEquivZChart E)
      (AdjoinRoot.of E.toAffine.polynomial Polynomial.X) = zChartX E from affineToZChart_of_X E] using hh
  have hy : eval (AdjoinRoot.root E.toAffine.polynomial) =
      u.evalSection _ h (sectionYOverZ E) := by
    have hh := hval (AdjoinRoot.root E.toAffine.polynomial)
    simpa only [eval, sectionYOverZ, show (affineEquivZChart E)
      (AdjoinRoot.root E.toAffine.polynomial) = zChartY E from affineToZChart_root E] using hh
  let b : E.toAffine.CoordinateRing →ₐ[ℚ] ℂ := {
    __ := ((Scheme.ΓSpecIso _).inv ≫ a.appTop ≫ (Scheme.ΓSpecIso _).hom).hom
    commutes' r := DFunLike.congr_fun (Subsingleton.elim
      (((Scheme.ΓSpecIso _).inv ≫ a.appTop ≫ (Scheme.ΓSpecIso _).hom).hom.comp
        (algebraMap ℚ E.toAffine.CoordinateRing)) (algebraMap ℚ ℂ)) r }
  have hb := Affine.equation_iff_nonsingular.mp (Affine.CoordinateRing.equation_of_algHom b)
  rw [projectiveValue, dite_eq_right hO]
  have hsol : ∃ hxy : (E.baseChange ℂ).toAffine.Nonsingular
      (eval (AdjoinRoot.of E.toAffine.polynomial Polynomial.X))
      (eval (AdjoinRoot.root E.toAffine.polynomial)),
      Affine.Point.some _ _ hb = Affine.Point.some _ _ hxy := ⟨hb, rfl⟩
  rw [hx, hy] at hsol
  exact hsol

/-- The extended morphism has the prescribed analytic projective value
at every upper half-plane point, including the identity. -/
theorem projective_value_of_expansions (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {N : ℕ} [NeZero N] (X : X0Model N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℚ} (hκ : κ ≠ 0)
    (π : X.X ⟶ Proj E.toProjective.grading) (hQ : π ≫ projectiveOverQ E = X.overQ)
    (ι : E.toAffine.FunctionField →+* modularFunctionField N)
    (hgen : letI := X.integral; X.X.fromSpecFunctionField ≫ π =
      Spec.map (CommRingCat.ofHom (X.functionField.symm.toRingHom.comp
        (ι.comp (projFunctionFieldEquiv E).toRingHom))) ≫
          (Proj E.toProjective.grading).fromSpecFunctionField)
    (hx : Realizes (complexify (ι E.toAffine.genericX)) (fun τ => xCoordinate E f L κ τ))
    (hy : Realizes (complexify (ι E.toAffine.genericY)) (fun τ => yCoordinate E f L κ τ))
    (τ : ℍ) :
    projectiveValue ((X.complexPoint τ).comp π hQ).val = phiAn E f L κ τ := by
  classical
  let u := (X.complexPoint τ).comp π hQ
  have he := projective_identity_iff_lattice E X f hf hL hκ π hQ ι hgen hx hy τ
  have hp : κ * eichlerPotential f τ = scaledPrimitive f κ τ := by simp [scaledPrimitive]
  by_cases hl : scaledPrimitive f κ τ ∈ L.lattice
  · simp only [phiAn, hp, weierPt, dite_eq_left, ite_eq_left, hl, projectiveValue, he.mpr hl]
  have hO : u.val default ≠ pointO E := fun h => hl (he.mp h)
  have hV : u.val default ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2) := by
    rw [Proj.mem_basicOpen]
    intro hZ
    exact hO (eq_pointO_of_coord_mem E _ (coord_zero_mem_of_coord_two_mem E _ hZ) hZ)
  obtain ⟨hmX, hmY⟩ := coordinates_meromorphic E f L κ
  obtain ⟨Gx, hmx, hax, hrx, hvx⟩ := pullback_expansion X π hQ ι hgen _ (sectionXOverZ E) τ hV
  obtain ⟨Gy, hmy, hay, hry, hvy⟩ := pullback_expansion X π hQ ι hgen _ (sectionYOverZ E) τ hV
  rw [projFunctionFieldEquiv_sectionXOverZ] at hrx
  rw [projFunctionFieldEquiv_sectionYOverZ] at hry
  have han := scaledPrimitive_analytic f (κ : ℂ) τ.im_pos
  have hw := (L.analyticOnNhd_weierstrassP _ hl).comp han
  have hw' := (L.analyticOnNhd_derivWeierstrassP _ hl).comp han
  have haX : AnalyticAt ℂ (xCoordinate E f L κ) (τ : ℂ) := hw.sub analyticAt_const
  have haY : AnalyticAt ℂ (yCoordinate E f L κ) (τ : ℂ) :=
    ((hw'.sub (analyticAt_const.mul haX)).sub analyticAt_const).div_const
  have hex := same_series_same_germ hmx hmX hrx hx τ
  have hey := same_series_same_germ hmy hmY hry hy τ
  have hX : u.evalSection _ hV (sectionXOverZ E) = xCoordinate E f L κ τ :=
    hvx.trans ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      hax.continuousAt haX.continuousAt).mp hex).eq_of_nhds
  have hY : u.evalSection _ hV (sectionYOverZ E) = yCoordinate E f L κ τ :=
    hvy.trans ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      hay.continuousAt haY.continuousAt).mp hey).eq_of_nhds
  obtain ⟨hs, hval⟩ := projectiveValue_on_affine E u hO hV
  change projectiveValue u.val = _
  revert hs hval
  rw [hX, hY]
  intro hs hval
  change (E.baseChange ℂ).toAffine.Nonsingular
    (xCoordinate E f L κ τ) (yCoordinate E f L κ τ) at hs
  rw [hval, phiAn, hp, weierPt, ite_eq_right hl]
  change Affine.Point.some _ _ _ = (if hh : (E.baseChange ℂ).toAffine.Nonsingular
    (xCoordinate E f L κ τ) (yCoordinate E f L κ τ) then .some _ _ hh else 0)
  rw [dite_eq_left hs]

#print axioms qParam_one_zpow
#print axioms eq_germ_of_eq_tail
#print axioms evalSection_eq_stalk
#print axioms evalSection_ZOverY_at_identity
#print axioms pullback_expansion
#print axioms same_series_same_germ
#print axioms projective_identity_iff_lattice
#print axioms appLE_of_lift
#print axioms evalSection_on_zChart
#print axioms projectiveValue_on_affine
#print axioms projective_value_of_expansions

end ZInQ.Manuscript.RC.ModFnClassify
