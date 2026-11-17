import ZInQKernel.Contrib.OneProof.TYZThm33
import ZInQKernel.Contrib.OneProof.Gamma0QExpansion
import ZInQKernel.Contrib.OneProof.TYZThm33Alg.ThetaJ

noncomputable section

set_option maxRecDepth 8000

namespace ZInQ.H33Fix

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.PropN NumberField TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Rank5b
  ZInQ.Contrib.TYZGenus.CMBridge ZInQ.Contrib.TYZGenus.TYZ35 ZInQ.Contrib.TYZDecomp
  ZInQ.RouteK.Redei ZInQ.Literature ZInQ.Contrib.TYZGenus.TYZSplit ZInQ.Contrib.TYZGenus.H33Dict

open ZInQ.GZAlg (HasQExp X0Field genX genY qPar laurentOf)
open ZInQ.Gamma0QExp (Rz)
open ModularCurve (coeffEmb jq jqN)
open UpperHalfPlane hiding I
open Complex Filter Topology
open scoped Manifold
attribute [local instance high] HahnSeries.powerSeriesAlgebra

/-! # §1. The leaf -/

/-- **`i₀ : (X₀(32), ∞) ≅ (A, O)` over `ℚ`, given by its pull-back on function fields.** -/
def IsX0IsoAlg (φ : curveA.toAffine.FunctionField →ₐ[ℚ] X0Field 32) : Prop :=
  Function.Bijective φ ∧ ((φ (genX curveA) : LaurentSeries ℚ)).order < 0

/-- **Leaf TYZ-3.3 (printed form, algebraic identification).** -/
def TYZThm33Alg : Prop :=
  ∀ φ : curveA.toAffine.FunctionField →ₐ[ℚ] X0Field 32, IsX0IsoAlg φ →
  ∀ X Y : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) X → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Y →
    HasQExp X (φ (genX curveA)) → HasQExp Y (φ (genY curveA)) →
  ∀ w : ℕ → PtA,
    (∀ n : ℕ, ∀ hn : n % 8 = 5, Squarefree n → toC (w n) = ptOf X Y (tyzForm n hn).tauH) →
    (∀ n : ℕ, ∀ hn : n % 8 = 7, Squarefree n → toC (w n) = ptOf X Y (tyzForm7 n hn).tauH) →
    TYZThm33EpsAfter (zOfLift w)

/-! # §2. `q`-expansions of the eta model -/

theorem hasSum_laurentOf {g : ℍ → ℂ} {k : ℕ} {a : ℕ → ℚ}
    (h : ∀ τ : ℍ, HasSum (fun n => (a n : ℂ) * qPar τ ^ n) (qPar τ ^ k * g τ)) (τ : ℍ) :
    HasSum (fun m : ℤ => (((laurentOf k a).coeff m : ℚ) : ℂ) * qPar τ ^ m) (g τ) := by
  have hq := ZInQ.GZAlg.qPar_ne_zero τ
  set g' : ℕ → ℤ := fun n => (n : ℤ) - k
  have hg : Function.Injective g' := fun n n' e => by simp only [g'] at e; omega
  rw [← hg.hasSum_iff]
  · have h2 := (h τ).mul_right ((qPar τ ^ k)⁻¹)
    rw [mul_comm (qPar τ ^ k), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), mul_one] at h2
    convert h2 using 1
    funext n
    simp only [Function.comp_apply, g', ZInQ.GZAlg.coeff_laurentOf]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show ((n : ℤ) - k + k) = (n : ℤ) by ring,
      Int.natAbs_natCast, zpow_sub₀ hq, zpow_natCast, zpow_natCast, div_eq_mul_inv, mul_assoc]
  · intro m hm
    have hmk : m + k < 0 := by
      by_contra hc
      exact hm ⟨(m + k).toNat, by simp only [g']; omega⟩
    simp [ZInQ.GZAlg.coeff_laurentOf, hmk]

theorem rz_of_hasSum {g : ℍ → ℂ} {x : LaurentSeries ℚ}
    (h : ∀ τ : ℍ, HasSum (fun m : ℤ => ((x.coeff m : ℚ) : ℂ) * qPar τ ^ m) (g τ)) :
    Rz (coeffEmb ℂ x) g := fun τ => by
  have := h τ
  rw [ZInQ.Contrib.Gamma0QExp.qPar_eq_qParam] at this
  simpa only [ZInQ.Gamma0QExp.coeffEmb_coeff_eq] using this

theorem hasQExp_of_hasSum {g : ℍ → ℂ} {x : LaurentSeries ℚ}
    (h : ∀ τ : ℍ, HasSum (fun m : ℤ => ((x.coeff m : ℚ) : ℂ) * qPar τ ^ m) (g τ)) :
    HasQExp g x := ⟨0, fun τ _ => h τ⟩

/-! # §3. Polynomial expressions -/

theorem rz_poly2 (P : ∀ (R : Type) [CommRing R], R → R → R)
    (hP : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (x y : R),
      f (P R x y) = P S (f x) (f y))
    {L M : LaurentSeries ℂ} {F G : ℍ → ℂ} (hL : Rz L F) (hM : Rz M G) :
    Rz (P _ L M) (fun τ => P ℂ (F τ) (G τ)) := by
  have h := Rz.aeval ![L, M] ![F, G] (fun i => by fin_cases i <;> simpa)
    (P _ (MvPolynomial.X 0) (MvPolynomial.X 1))
  have e1 := hP _ _ (MvPolynomial.aeval (R := ℂ) ![L, M]).toRingHom (MvPolynomial.X 0) (MvPolynomial.X 1)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X] at e1
  rw [e1] at h
  refine Rz.congr_fun h (fun τ => ?_)
  have e2 := hP _ _ (MvPolynomial.eval (fun i => ![F, G] i τ)) (MvPolynomial.X 0) (MvPolynomial.X 1)
  simp only [MvPolynomial.eval_X] at e2
  simpa using e2

theorem poly2_mem (P : ∀ (R : Type) [CommRing R], R → R → R)
    (hP : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (x y : R),
      f (P R x y) = P S (f x) (f y))
    {K : Subfield (LaurentSeries ℚ)} {x y : LaurentSeries ℚ} (hx : x ∈ K) (hy : y ∈ K) :
    P _ x y ∈ K := by
  have e := hP K (LaurentSeries ℚ) K.subtype ⟨x, hx⟩ ⟨y, hy⟩
  simp only [Subfield.coe_subtype] at e
  rw [← e]
  exact (P K ⟨x, hx⟩ ⟨y, hy⟩).2

theorem jDen_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x y : R) :
    f (jDen x y) = jDen (f x) (f y) := by
  simp only [jDen, e4E, e6E, a2E, b2E, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]

theorem jNum_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x y : R) :
    f (jNum x y) = jNum (f x) (f y) := by
  simp only [jNum, e4E, e6E, a2E, b2E, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]

theorem j32Den_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    f (j32Den x) = j32Den (f x) := by
  simp only [j32Den, f4E, f6E, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]

theorem j32Num_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    f (j32Num x) = j32Num (f x) := by
  simp only [j32Num, f4E, f6E, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]

/-! # §4. `jq` and `jq(q³²)` lie in `ℚ(x, y)` -/

theorem eq_zero_of_rz_zero {F : ℍ → ℂ} (h : Rz 0 F) (τ : ℍ) : F τ = 0 := by
  have := h τ
  simp only [HahnSeries.coeff_zero, zero_mul] at this
  exact (hasSum_zero.unique this).symm

set_option maxHeartbeats 4000000 in
theorem jq_rel {xq yq : LaurentSeries ℚ} (hx : Rz (coeffEmb ℂ xq) (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ))
    (hy : Rz (coeffEmb ℂ yq) (fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ)) :
    jq * jDen xq yq = jNum xq yq ∧ jDen xq yq ≠ 0 := by
  have hD := rz_poly2 (fun R _ => @jDen R _) (fun R S _ _ f x y => jDen_map f x y) hx hy
  have hN := rz_poly2 (fun R _ => @jNum R _) (fun R S _ _ f x y => jNum_map f x y) hx hy
  have hz := (ZInQ.Gamma0QExp.rz_jq.mul hD).sub hN
  have h0 : coeffEmb ℂ jq * jDen (coeffEmb ℂ xq) (coeffEmb ℂ yq) -
      jNum (coeffEmb ℂ xq) (coeffEmb ℂ yq) = 0 := Rz.eq_zero hz (fun τ => by
    simp only [ZInQ.Gamma0QExp.jf]
    rw [sub_eq_zero]; exact (j_eta τ).1)
  constructor
  · apply (coeffEmb ℂ).injective
    beta_reduce at h0
    rw [map_mul, jDen_map, jNum_map]; exact sub_eq_zero.mp h0
  · intro h
    have h1 : jDen (coeffEmb ℂ xq) (coeffEmb ℂ yq) = 0 := by rw [← jDen_map, h, map_zero]
    beta_reduce at hD
    rw [h1] at hD
    exact (j_eta UpperHalfPlane.I).2 (eq_zero_of_rz_zero hD _)

set_option maxHeartbeats 4000000 in
theorem jq32_rel {xq : LaurentSeries ℚ} (hx : Rz (coeffEmb ℂ xq) (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ)) :
    jqN 32 * j32Den xq = j32Num xq ∧ j32Den xq ≠ 0 := by
  have hD := rz_poly2 (fun R _ x _ => @j32Den R _ x) (fun R S _ _ f x y => j32Den_map f x) hx hx
  have hN := rz_poly2 (fun R _ x _ => @j32Num R _ x) (fun R S _ _ f x y => j32Num_map f x) hx hx
  beta_reduce at hD hN
  have hz := ((ZInQ.Gamma0QExp.rz_jqN 32).mul hD).sub hN
  have h0 := Rz.eq_zero hz (fun τ => by
    simp only [ZInQ.Gamma0QExp.jN, ZInQ.Gamma0QExp.jf]
    rw [sub_eq_zero]; exact (j32_eta τ _ (by simp)).1)
  constructor
  · apply (coeffEmb ℂ).injective
    beta_reduce at h0
    rw [map_mul, j32Den_map, j32Num_map]; exact sub_eq_zero.mp h0
  · intro h
    have h1 : j32Den (coeffEmb ℂ xq) = 0 := by rw [← j32Den_map, h, map_zero]
    rw [h1] at hD
    exact (j32_eta UpperHalfPlane.I (ZInQ.Gamma0QExp.scaleN 32 UpperHalfPlane.I) (by simp)).2
      (eq_zero_of_rz_zero hD _)

theorem mem_of_rel {K : Subfield (LaurentSeries ℚ)} {j n d : LaurentSeries ℚ}
    (h : j * d = n) (hd : d ≠ 0) (hn : n ∈ K) (hdK : d ∈ K) : j ∈ K := by
  have : j = n * d⁻¹ := by rw [← h, mul_assoc, mul_inv_cancel₀ hd, mul_one]
  rw [this]; exact mul_mem hn (inv_mem hdK)

/-- **`ℚ(X₀(32)) = ℚ(j, j₃₂) ⊆ ℚ(x, y)`**: every subfield of `ℚ((q))` containing the `q`-expansions of the
eta model's `x` and `y` contains `ℚ(X₀(32))`. -/
theorem x0Field_le {xq yq : LaurentSeries ℚ} (hx : Rz (coeffEmb ℂ xq) (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ))
    (hy : Rz (coeffEmb ℂ yq) (fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ))
    (T : Subfield (LaurentSeries ℚ)) (hxT : xq ∈ T) (hyT : yq ∈ T) :
    ∀ z ∈ X0Field 32, z ∈ T := by
  obtain ⟨r1, d1⟩ := jq_rel hx hy
  obtain ⟨r2, d2⟩ := jq32_rel hx
  have m1 : jq ∈ T := mem_of_rel r1 d1
    (poly2_mem (fun R _ => @jNum R _) (fun R S _ _ f x y => jNum_map f x y) hxT hyT)
    (poly2_mem (fun R _ => @jDen R _) (fun R S _ _ f x y => jDen_map f x y) hxT hyT)
  have m2 : jqN 32 ∈ T := mem_of_rel r2 d2
    (poly2_mem (fun R _ x _ => @j32Num R _ x) (fun R S _ _ f x y => j32Num_map f x) hxT hyT)
    (poly2_mem (fun R _ x _ => @j32Den R _ x) (fun R S _ _ f x y => j32Den_map f x) hxT hyT)
  let K : IntermediateField ℚ (LaurentSeries ℚ) := T.toIntermediateField (fun c => by
    rw [eq_ratCast]; exact SubfieldClass.ratCast_mem T c)
  have hle : X0Field 32 ≤ K := by
    show IntermediateField.adjoin ℚ _ ≤ K
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact m1
    · exact m2
  exact fun z hz => hle hz

/-! # §5. The eta model is an algebraic identification -/

/-- If `X` is unbounded at `∞`, its `q`-expansion has negative order (from gzopt-dict's `order_neg_of`). -/
theorem order_neg_of_unbounded {X : ℍ → ℂ} {x : LaurentSeries ℚ}
    (hq : ∀ τ : ℍ, HasSum (fun m : ℤ => ((x.coeff m : ℚ) : ℂ) * qPar τ ^ m) (X τ))
    (hb : ¬ UpperHalfPlane.IsBoundedAtImInfty X) : x.order < 0 := by
  by_contra hc
  rw [not_lt] at hc
  have hT' : ∀ τ : ℍ, (0 : ℝ) < τ.im →
      HasSum (fun n : ℕ => (x.coeff n : ℂ) * qPar τ ^ n) (X τ) := by
    intro τ _
    have h1 := hq τ
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff] at h1
    · convert h1 using 1
      funext n
      simp [zpow_natCast]
    · intro m hm
      have hm0 : m < 0 := by
        by_contra h; exact hm ⟨m.toNat, by omega⟩
      rw [HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hm0 hc)]
      simp
  set p := FormalMultilinearSeries.ofScalars ℂ fun n => (x.coeff n : ℂ)
  have hrad := ZInQ.GZAlg.le_radius (le_refl 0) hT'
  have hcont : ContinuousAt p.sum 0 :=
    (ZInQ.GZAlg.analyticAt_sum hrad (by simpa using ZInQ.GZAlg.R0_pos 0)).continuousAt
  obtain ⟨δ, hδ, hbd⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
  apply hb
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨‖p.sum 0‖ + 1, max 1 (-Real.log δ / (2 * Real.pi) + 1), fun τ hτ => ?_⟩
  have hτ1 : (0 : ℝ) < τ.im := τ.im_pos
  have hτ2 : -Real.log δ / (2 * Real.pi) < τ.im := by
    linarith [le_max_right (1 : ℝ) (-Real.log δ / (2 * Real.pi) + 1)]
  have hqδ : ‖qPar τ‖ < δ := by
    rw [qPar, ZInQ.GZAlg.norm_exp_two_pi_I]
    have hπ := Real.pi_pos
    have : -(2 * Real.pi * (τ : ℂ).im) < Real.log δ := by
      rw [UpperHalfPlane.coe_im]
      rw [div_lt_iff₀ (by positivity)] at hτ2
      linarith
    calc Real.exp (-(2 * Real.pi * (τ : ℂ).im)) < Real.exp (Real.log δ) := Real.exp_lt_exp.2 this
      _ = δ := Real.exp_log hδ
  have hd := hbd (by simpa using hqδ)
  rw [ZInQ.GZAlg.sum_eq hT' τ hτ1] at hd
  have := norm_sub_norm_le (X τ) (p.sum 0)
  rw [dist_eq_norm] at hd
  linarith

/-- The `q`-expansion data of the eta model. -/
structure EtaQ where
  kx : ℕ
  ax : ℕ → ℚ
  ky : ℕ
  ay : ℕ → ℚ
  hx : ∀ τ : ℍ, HasSum (fun n => (ax n : ℂ) * qPar τ ^ n) (qPar τ ^ kx * ZInQ.Contrib.TYZGenus.X0.xC τ)
  hy : ∀ τ : ℍ, HasSum (fun n => (ay n : ℂ) * qPar τ ^ n) (qPar τ ^ ky * ZInQ.Contrib.TYZGenus.X0.yC τ)

theorem etaQ_nonempty : Nonempty EtaQ := by
  obtain ⟨-, -, kx, ax, hx⟩ := X0ModuliUsed.isRatModFn_x
  obtain ⟨-, -, ky, ay, hy⟩ := X0ModuliUsed.isRatModFn_y
  exact ⟨⟨kx, ax, ky, ay, hx, hy⟩⟩

/-- The eta model's `q`-expansions. -/
def etaQ : EtaQ := Classical.choice etaQ_nonempty
def xq : LaurentSeries ℚ := laurentOf etaQ.kx etaQ.ax
def yq : LaurentSeries ℚ := laurentOf etaQ.ky etaQ.ay

theorem hasSum_xq (τ : ℍ) : HasSum (fun m : ℤ => ((xq.coeff m : ℚ) : ℂ) * qPar τ ^ m) (ZInQ.Contrib.TYZGenus.X0.xC τ) :=
  hasSum_laurentOf etaQ.hx τ
theorem hasSum_yq (τ : ℍ) : HasSum (fun m : ℤ => ((yq.coeff m : ℚ) : ℂ) * qPar τ ^ m) (ZInQ.Contrib.TYZGenus.X0.yC τ) :=
  hasSum_laurentOf etaQ.hy τ

theorem xq_mem : xq ∈ X0Field 32 :=
  ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof 32 _
    (ZInQ.GZHeegner.isRatModFnMero_of 32 X0ModuliUsed.isRatModFn_x) _ (hasQExp_of_hasSum hasSum_xq)
theorem yq_mem : yq ∈ X0Field 32 :=
  ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof 32 _
    (ZInQ.GZHeegner.isRatModFnMero_of 32 X0ModuliUsed.isRatModFn_y) _ (hasQExp_of_hasSum hasSum_yq)

theorem xq_order : xq.order < 0 := order_neg_of_unbounded hasSum_xq not_bounded_xC

theorem wEq_eta : ZInQ.GZAlg.WEq curveA xq yq := by
  refine ZInQ.GZAlg.wEq_of (le_refl 0) (fun τ _ => etaQ.hx τ) (fun τ _ => etaQ.hy τ) ?_
  intro τ _ _
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := ZInQ.Contrib.TYZGenus.Shimura.etaModelEquation τ
  simp [curveA, shortCurve]
  linear_combination h

/-- The eta model's coordinates as elements of `ℚ(X₀(32))`. -/
def xE : X0Field 32 := ⟨xq, xq_mem⟩
def yE : X0Field 32 := ⟨yq, yq_mem⟩

/-- **The pull-back `φ^*_η : ℚ(A) → ℚ(X₀(32))` of the eta model.** -/
def phiEta : curveA.toAffine.FunctionField →ₐ[ℚ] X0Field 32 :=
  ZInQ.GZAlg.phiOf xE yE (ZInQ.GZAlg.eval₂_polynomial_of_wEq xE yE wEq_eta)
    (ZInQ.GZAlg.transcendental_of_order_neg xE xq_order)

theorem phiEta_genX : phiEta (genX curveA) = xE := ZInQ.GZAlg.phiOf_genX _ _ _ _
theorem phiEta_genY : phiEta (genY curveA) = yE := ZInQ.GZAlg.phiOf_genY _ _ _ _

/-- **The eta model is an isomorphism `(X₀(32), ∞) ≅ (A, O)` over `ℚ`** (`φ^*_η` bijective onto
`ℚ(j, j₃₂)`, `x` with a pole at `∞`). -/
theorem isX0IsoAlg_eta : IsX0IsoAlg phiEta := by
  refine ⟨⟨phiEta.toRingHom.injective, fun z => ?_⟩, by rw [phiEta_genX]; exact xq_order⟩
  let ψ : curveA.toAffine.FunctionField →+* LaurentSeries ℚ :=
    (SubsemiringClass.subtype (X0Field 32)).comp (phiEta : curveA.toAffine.FunctionField →+* X0Field 32)
  have hz := x0Field_le (rz_of_hasSum hasSum_xq) (rz_of_hasSum hasSum_yq) ψ.fieldRange
    ⟨genX curveA, by simp [ψ, phiEta_genX, xE]⟩ ⟨genY curveA, by simp [ψ, phiEta_genY, yE]⟩ z z.2
  obtain ⟨a, ha⟩ := hz
  exact ⟨a, Subtype.ext ha⟩

theorem mdiff_xC : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => ZInQ.Contrib.TYZGenus.X0.xC τ) :=
  mdiff_of fun τ hτ => ZInQ.Contrib.TYZGenus.X0.differentiableAt_xC ⟨τ, hτ⟩
theorem mdiff_yC : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => ZInQ.Contrib.TYZGenus.X0.yC τ) :=
  mdiff_of fun τ hτ => ZInQ.Contrib.TYZGenus.X0.differentiableAt_yC ⟨τ, hτ⟩

/-! # §6. The contribution -/

/-- **`TYZSplit.TYZThm33` from TYZ Theorem 3.3 with TYZ's algebraic identification** (and the printed
main theorem of CM `hCM`, already a hypothesis of `frozenTarget`). -/
theorem tyzThm33_of_alg (hCM : T5Glue.ShimuraMainCM) (h : TYZThm33Alg) : TYZThm33 := by
  have hI := cmInputs hCM
  apply tyzThm33_of_epsAfter (tyzProp324Used_of hI)
  let w : ℕ → PtA := fun n => if n % 8 = 5 then tyzHeegnerPt n else tyzZ7 n
  have hz : zOfLift w = basePt := by
    funext n
    by_cases h5 : n % 8 = 5 <;> simp [zOfLift, w, basePt, h5, tyzZn]
  rw [← hz]
  refine h phiEta isX0IsoAlg_eta _ _ mdiff_xC mdiff_yC
    (by rw [phiEta_genX]; exact hasQExp_of_hasSum hasSum_xq)
    (by rw [phiEta_genY]; exact hasQExp_of_hasSum hasSum_yq) w ?_ ?_
  · intro n hn _
    have e : w n = heegnerPt (tyzForm n hn) := by simp [w, hn, tyzHeegnerPt]
    rw [e]
    exact toC_heegnerPt _ (hI.alg _ _)
  · intro n hn _
    have h5 : n % 8 ≠ 5 := by omega
    have e : w n = heegnerPt (tyzForm7 n hn) := by simp [w, tyzZ7, hn]
    rw [e]
    exact toC_heegnerPt _ (hI.alg _ _)

end ZInQ.H33Fix
