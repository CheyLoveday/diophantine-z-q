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

theorem t1 {xq yq : LaurentSeries ℚ} (hx : Rz (coeffEmb ℂ xq) (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ))
    (hy : Rz (coeffEmb ℂ yq) (fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ)) :
    Rz (jDen (coeffEmb ℂ xq) (coeffEmb ℂ yq))
      (fun τ => jDen (ZInQ.Contrib.TYZGenus.X0.xC τ) (ZInQ.Contrib.TYZGenus.X0.yC τ)) :=
  rz_poly2 (fun R _ => @jDen R _) (fun R S _ _ f x y => jDen_map f x y) hx hy

theorem t2 (τ : ℍ) : ZInQ.Gamma0QExp.jf τ * jDen (ZInQ.Contrib.TYZGenus.X0.xC τ) (ZInQ.Contrib.TYZGenus.X0.yC τ)
   = jNum (ZInQ.Contrib.TYZGenus.X0.xC τ) (ZInQ.Contrib.TYZGenus.X0.yC τ) := (j_eta τ).1

theorem t1N {xq yq : LaurentSeries ℚ} (hx : Rz (coeffEmb ℂ xq) (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ))
    (hy : Rz (coeffEmb ℂ yq) (fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ)) :
    Rz (jNum (coeffEmb ℂ xq) (coeffEmb ℂ yq))
      (fun τ => jNum (ZInQ.Contrib.TYZGenus.X0.xC τ) (ZInQ.Contrib.TYZGenus.X0.yC τ)) :=
  rz_poly2 (fun R _ => @jNum R _) (fun R S _ _ f x y => jNum_map f x y) hx hy

set_option maxHeartbeats 4000000 in
theorem t4 {xq yq : LaurentSeries ℚ} (hx : Rz (coeffEmb ℂ xq) (fun τ => ZInQ.Contrib.TYZGenus.X0.xC τ))
    (hy : Rz (coeffEmb ℂ yq) (fun τ => ZInQ.Contrib.TYZGenus.X0.yC τ)) :
    coeffEmb ℂ jq * jDen (coeffEmb ℂ xq) (coeffEmb ℂ yq) -
      jNum (coeffEmb ℂ xq) (coeffEmb ℂ yq) = 0 :=
  Rz.eq_zero ((ZInQ.Gamma0QExp.rz_jq.mul (t1 hx hy)).sub (t1N hx hy)) (fun τ => sub_eq_zero.mpr (t2 τ))

set_option maxHeartbeats 4000000 in
theorem t5 {xq yq : LaurentSeries ℚ} (h0 : coeffEmb ℂ jq * jDen (coeffEmb ℂ xq) (coeffEmb ℂ yq) -
      jNum (coeffEmb ℂ xq) (coeffEmb ℂ yq) = 0) : jq * jDen xq yq = jNum xq yq := by
  have h1 : coeffEmb ℂ (jq * jDen xq yq) = coeffEmb ℂ (jNum xq yq) := by
    rw [map_mul, jDen_map, jNum_map]; exact sub_eq_zero.mp h0
  exact (coeffEmb ℂ).injective h1

end ZInQ.H33Fix
