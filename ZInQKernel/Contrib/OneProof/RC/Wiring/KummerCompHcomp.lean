import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCompArith
import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCompClass
import ZInQKernel.Contrib.CloudB3E2Norm.KappaGen
import ZInQKernel.Contrib.CloudB3E2Norm.KummerInj

/-!
# Theorem 5.3, Lane RC37: the Kummer compatibility `hcomp`

Manuscript `diophantine_zq.tex`, tex 3895–3986 and 4005–4014. For the concrete comparison
`kcKummerCoefficientComparison` the universal-coefficient map sends the `2`-adic Kummer class
`κ(P) ∈ H¹(C_K)` of a rational point, tensored with `d ∈ ℚ₂/ℤ₂`, to the `2`-primary Kummer image
`kummerInf (ι P) d ∈ Sel_{2^∞}(E/K)` of the RC53 group (`KummerInj.lean`), where `ι` is the
identification of `E(K)` with the fixed-geometric-point model `pointsK` along `K ⊂ ℚˢ`
(`kcPointsEquiv`, from the bridge `KummerCompBridge.lean`).

* `kc_pt_frac`: in the Tate module, `(a·T)_μ = a'·T_n` whenever `a/2^μ ≡ a'/2^n mod ℤ₂`;
* `kc_hcomp_tower`: the compatibility for the class `kummerClassOf` of any global tower;
* `kc_hcomp_central`: the compatibility in the exact form of the input `hcomp` of
  `KappaGen.hκ_central`, for the central twist (`centralKummer`, `centralH1Equiv`), with
  `δ P d = kummerInf (ι P) d`, `ι = kcCentralPoints` (the cast along `hcurve` followed by
  `kcPointsEquiv`);
* `kc_hκ_central`: `hκ_central` with `I`, `hcomp` supplied (PROVED from the remaining named
  inputs of `hκ_central` and the finite-level Selmer description `KcArithSelmerLevel`).

Kinds: definitions and PROVED.
-/

noncomputable section

set_option maxHeartbeats 3200000

namespace ZInQ.Manuscript.RC

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ZInQ.Manuscript.RC53Assist.CentralUniversal ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Contrib.RC53Assist.DiskOrders.Limit ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3E2.KummerInj (kummerInf repN repA rep_spec)
open TauCeti TauCeti.ContCohomology
open scoped TensorProduct

attribute [local instance] levTop continuousSMul_lev
attribute [local instance high] kcAlgKS

/-! ### `ψ` on pure tensors -/

section Generic

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M']
  (D : KcLevelData S W G' M')

/-- **`ψ [q ⊗ x] = θ_μ(2^μ q · x)`**, `μ` the least two-power denominator of `q`.
Kind: PROVED. -/
theorem kcPsi_pi_tmul (n : ℤ) (q : ℚ_[2]) (x : (compactKummerComplex S W hFull).X n) :
    ((kcPsi hFull D).f n).hom (kcPi _ n (kcTmul _ q x)) =
      kcTheta hFull D (kcMu q) n (kcNum q (kcMu q) (kcMu_spec q) • x) := by
  rw [kcPsi, kcDesc_apply, kcGamma_tmul]
  rfl

omit [W.IsElliptic] in
/-- Integer multiples commute with the Tate coordinates. Kind: PROVED. -/
theorem kc_pt_zsmul (z : ℤ) (T : TateS K S W) (n : ℕ) : (z • T).pt n = z • T.pt n := by
  change ((projLev n (z • T) : Lev K S W n) : Pt K S W) = z • ((projLev n T : Lev K S W n) :
    Pt K S W)
  rw [map_zsmul, AddSubgroup.coe_zsmul]

omit [W.IsElliptic] in
/-- **Tate coordinates of fractions**: if `a/2^μ ≡ a'/2^n` modulo `ℤ₂`, then
`(a · T)_μ = a' · T_n`. Kind: PROVED. -/
theorem kc_pt_frac (T : TateS K S W) (μ n : ℕ) (a : ℤ_[2]) (a' : ℤ)
    (h : ‖(a : ℚ_[2]) / 2 ^ μ - (a' : ℚ_[2]) / 2 ^ n‖ ≤ 1) :
    (a • T).pt μ = a' • T.pt n := by
  let w : ℤ_[2] := Padic.lift ((a : ℚ_[2]) / 2 ^ μ - (a' : ℚ_[2]) / 2 ^ n) h
  have hw : (2 : ℤ_[2]) ^ n * a - (2 : ℤ_[2]) ^ μ * (a' : ℤ_[2]) = (2 : ℤ_[2]) ^ (μ + n) * w := by
    apply PadicInt.ext
    have hc : ((w : ℤ_[2]) : ℚ_[2]) = (a : ℚ_[2]) / 2 ^ μ - (a' : ℚ_[2]) / 2 ^ n :=
      PadicInt.coe_lift h
    rw [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_pow, PadicInt.coe_pow, PadicInt.coe_intCast, hc,
      show ((2 : ℤ_[2]) : ℚ_[2]) = 2 from rfl]
    have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
    field_simp
    ring
  have e1 : (a • T).pt μ = (((2 : ℤ_[2]) ^ n * a) • T).pt (μ + n) := by
    rw [mul_smul, kc_pt_two_pow_smul]
  have e2 : a' • T.pt n = (((2 : ℤ_[2]) ^ μ * (a' : ℤ_[2])) • T).pt (μ + n) := by
    rw [mul_smul, add_comm μ n, kc_pt_two_pow_smul, Int.cast_smul_eq_zsmul, kc_pt_zsmul]
  rw [e1, e2, ← sub_eq_zero, ← CalPoint.tateS_pt_sub_apply, ← sub_smul, hw, mul_smul]
  have h0 := kc_pt_two_pow_smul (w • T) 0 (μ + n)
  rw [zero_add] at h0
  rw [h0]
  exact congrArg Subtype.val (kc_lev_zero_eq (projLev 0 (w • T)))

end Generic

/-! ### The compatibility for a global tower -/

section Tower

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic]
  (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
  (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
    ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n))

/-- **`hcomp` for the class of a global tower**: the universal-coefficient map of the concrete
comparison sends `κ(P) ⊗ [q]`, `κ(P) = [(a_R, u_R, 0)]`, to `kummerInf (ι P) [q]`. Both sides are
classes of the cocycle `g ↦ a' (g R_n − R_n)` for `[q] = [a'/2^n]`: the left side is
`g ↦ (a · (g R − R))_μ` with `q = a/2^μ` (`kcPsi_pi_tmul`), and `kc_pt_frac` identifies the two.
Kind: PROVED. -/
theorem kc_hcomp_tower (hk : k < 0) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ S)
    (G : KcArithSelmerLevel k S (Ecurve ℓ))
    {P : ((Ecurve ℓ).baseChange (QuadraticField k)).toAffine.Point}
    {R : ℕ → (((Ecurve ℓ).baseChange (QuadraticField k)).baseChange
      (KS (QuadraticField k) S)).toAffine.Point}
    (hR : CalPoint.IsGlobalDivTower ((Ecurve ℓ).baseChange (QuadraticField k)) P R) (q : ℚ_[2]) :
    arithmeticUniversalCoefficientMap ℓ k S hFull
        (kcKummerCoefficientComparison ℓ k S hFull hk hS h2 G)
        (CalPoint.kummerClassOf S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull P R hR ⊗ₜ[ℤ_[2]]
          divisibleQuotient q) =
      kummerInf (sqrtK k) (Ecurve ℓ) (kcPointsEquiv k (Ecurve ℓ) P) (divisibleQuotient q) := by
  set z : (compactKummerComplex S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull).X 1 :=
    CalPoint.kummerSelmerCochain S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull hR with hzdef
  have hz : ((compactKummerComplex S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull).d 1 2).hom
      z = 0 :=
    CalPoint.kummerSelmerCochain_closed S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull hR
  rw [arithmeticUniversalCoefficientMap_formula]
  obtain ⟨c', hc'i, hc'⟩ := kc_rationalToDivisible_cycle
    (compactKummerComplex S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull) q
    (CalPoint.degOneCycle _ z hz)
  have e1 : CalPoint.kummerClassOf S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull P R hR =
      ((compactKummerComplex S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull).homologyπ 1).hom
        (CalPoint.degOneCycle _ z hz) := rfl
  rw [e1, hc']
  apply Subtype.ext
  obtain ⟨hd, hsel⟩ := kc_comparison_selmerEquiv_cycle
    (kcKummerCoefficientComparison ℓ k S hFull hk hS h2 G)
    (kcPsi hFull (kcArithLevelData k S (Ecurve ℓ) hFull))
    (kcPhi_comp hFull (kcArithLevelData k S (Ecurve ℓ) hFull) (SelK ℓ k)
      (kcSelmerSupport_of_level k S (Ecurve ℓ) hFull hk hS h2 G)) c'
  rw [hsel]
  -- the left side as an inflated level class
  set μ := kcMu q
  set a := kcNum q (kcMu q) (kcMu_spec q)
  have hdz : ((compactKummerComplex S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull).d 1 2).hom
      (a • z) = (2 : ℤ_[2]) ^ μ • 0 := by
    rw [LinearMap.map_smul, hz, smul_zero, smul_zero]
  have hf := kcRed1_d hFull μ _ _ hdz
  have hcongr : ∀ (x y : (contCochains ℤ (galK (sqrtK k)) (TwoPowerCoeff (Ecurve ℓ))).X 1)
      (hx : x ∈ LinearMap.ker
        ((contCochains ℤ (galK (sqrtK k)) (TwoPowerCoeff (Ecurve ℓ))).d 1 2).hom)
      (hy : y ∈ LinearMap.ker
        ((contCochains ℤ (galK (sqrtK k)) (TwoPowerCoeff (Ecurve ℓ))).d 1 2).hom),
      x = y → kerToH1 (k := ℤ) ⟨x, hx⟩ = kerToH1 (k := ℤ) ⟨y, hy⟩ := by
    rintro x _ hx hy rfl
    rfl
  have hval : ((kcPsi hFull (kcArithLevelData k S (Ecurve ℓ) hFull)).f 1).hom
      (((arithmeticCoefficientComplex ℓ k S hFull).iCycles 1).hom c') =
        ((kcInflate (kcArithLevelData k S (Ecurve ℓ) hFull) μ).f 1).hom
          (kcRed1 hFull μ (a • z)) := by
    rw [hc'i, CalPoint.iCycles_degOneCycle, kcPsi_pi_tmul, kcTheta_one]
  rw [hcongr _ _ hd (kcInflate_mem_ker _ hf) hval]
  -- the right side as an inflated level class
  set n := repN (divisibleQuotient q)
  set a' := repA (divisibleQuotient q)
  have hb : (levelSequence (sqrtK k) (Ecurve ℓ) n).proj (a' • kcPt k S (Ecurve ℓ) (R n)) =
      ((a' • kcPointsEquiv k (Ecurve ℓ) P : pointsK (sqrtK k) (Ecurve ℓ)) :
        (Ecurve ℓ).PointCoeff) := by
    change (2 ^ n : ℕ) • (a' • kcPt k S (Ecurve ℓ) (R n)) = _
    rw [smul_comm, ← map_nsmul, hR.two_pow_smul n, kcPt_pointToKS]
    rfl
  have hab : ∀ g : galK (sqrtK k), (levelSequence (sqrtK k) (Ecurve ℓ) n).incl
      (a' • kcLev k S (Ecurve ℓ) n (CalPoint.globalKummerLev hR n (kcGal k S g))) =
        g • (a' • kcPt k S (Ecurve ℓ) (R n)) - a' • kcPt k S (Ecurve ℓ) (R n) := by
    intro g
    change ((a' • kcLev k S (Ecurve ℓ) n (CalPoint.globalKummerLev hR n (kcGal k S g)) :
      (Ecurve ℓ).TorsionCoeff (2 ^ n)) : (Ecurve ℓ).PointCoeff) =
        (g : AbsoluteGaloisGroup ℚ) • (a' • kcPt k S (Ecurve ℓ) (R n)) -
          a' • kcPt k S (Ecurve ℓ) (R n)
    have hcomm : ∀ (h : AbsoluteGaloisGroup ℚ) (y : (Ecurve ℓ).PointCoeff),
        h • (a' • y) = a' • (h • y) := fun h y => smul_comm h a' y
    rw [AddSubgroup.coe_zsmul, coe_kcLev, CalPoint.coe_globalKummerLev, map_sub, kcPt_smul,
      hcomm, smul_sub]
  have hδ := (levelSequence (sqrtK k) (Ecurve ℓ) n).explicitDelta0_apply
    (a' • kcPointsEquiv k (Ecurve ℓ) P) hb hab
  change _ = levelToInfinite (sqrtK k) (Ecurve ℓ) n
    ((levelSequence (sqrtK k) (Ecurve ℓ) n).explicitDelta0 (a' • kcPointsEquiv k (Ecurve ℓ) P))
  rw [hδ, levelToInfinite, kerToH1_apply]
  erw [explicitCoeff1_mk]
  apply congrArg (H1pi (galK (sqrtK k)) (TwoPowerCoeff (Ecurve ℓ)))
  apply Subtype.ext
  funext g
  apply Subtype.ext
  -- the values
  have hq : ‖(a : ℚ_[2]) / 2 ^ μ - (a' : ℚ_[2]) / 2 ^ n‖ ≤ 1 := by
    have hrep : (Submodule.Quotient.mk ((a' : ℚ_[2]) / 2 ^ n) : ℚ_[2] ⧸ integralLattice) =
        Submodule.Quotient.mk q := rep_spec (divisibleQuotient q)
    have hmem := (Submodule.Quotient.eq integralLattice).1 hrep
    change ‖(a' : ℚ_[2]) / 2 ^ n - q‖ ≤ 1 at hmem
    have ha : (a : ℚ_[2]) / 2 ^ μ = q := by
      rw [kcNum_coe]
      field_simp
      exact mul_comm _ _
    rw [ha, norm_sub_rev]
    exact hmem
  have hpt := kc_pt_frac (CalPoint.globalKummerFun hR (kcGal k S g)) μ n a a' hq
  change kcPt k S (Ecurve ℓ) ((a • CalPoint.globalKummerFun hR (kcGal k S g)).pt μ) =
    a' • kcPt k S (Ecurve ℓ) ((CalPoint.globalKummerFun hR (kcGal k S g)).pt n)
  rw [hpt, map_zsmul]

end Tower

/-! ### The identification `ι` and the central compatibility -/

section Cast

/-- **Points along an equality of curves** (the identity on points, transported along `h`).
Kind: definition. -/
def kcCurveCast {K : Type} [Field K] [DecidableEq K] {W₁ W₂ : WeierstrassCurve K} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point :=
  h ▸ AddEquiv.refl _

/-- **The Kummer class map commutes with transport along an equality of curves.**
Kind: PROVED. -/
theorem kc_kummerClass_cast {K : Type} [Field K] [NumberField K] [DecidableEq K]
    (S : Set (HeightOneSpectrum (𝓞 K))) {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic]
    [W₂.IsElliptic] (h : W₁ = W₂) (hF₁ : ∀ n : ℕ, FullTorsion K S W₁ (2 ^ n))
    (hF₂ : ∀ n : ℕ, FullTorsion K S W₂ (2 ^ n)) (hdiv₁ : CalPoint.GlobalDivisionTowers S W₁)
    (hdiv₂ : CalPoint.GlobalDivisionTowers S W₂)
    (e : compactKummerComplex S W₁ hF₁ = compactKummerComplex S W₂ hF₂) (P : W₁.toAffine.Point) :
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ_[2]) (ComplexShape.up ℤ) 1).mapIso
      (eqToIso e)).toLinearEquiv (CalPoint.kummerClass S W₁ hF₁ hdiv₁ P) =
        CalPoint.kummerClass S W₂ hF₂ hdiv₂ (kcCurveCast h P) := by
  subst h
  rw [eqToIso_refl, Functor.mapIso_refl]
  rfl

end Cast

section Central

open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (compactCentralComplex centralCurve
  centralFullTorsion)
open ZInQ.Contrib.RC53Assist.CalibrationShape (compactCentral_eq_arithmetic arithmeticCentralFull)
open ZInQ.Contrib.CloudB3E2.KappaGen (centralH1Equiv hκ_central)
open ZInQ.Manuscript.RC.CalPoint (centralKummer GlobalDivisionTowers IsFreeLineGenerator)

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData (QuadraticField k) E₀ hZ)
  (hcurve : centralCurve G = (Ecurve ℓ).baseChange (QuadraticField k))

/-- **The identification `ι : E^{(h)}(K) ≅ E_ℓ(K) = pointsK`** of the central twist's points
with the fixed-geometric-point model: the cast along `hcurve` followed by the field embedding
`K ⊂ ℚˢ` (`kcPointsEquiv`). Kind: definition. -/
def kcCentralPoints :
    (centralCurve G).toAffine.Point ≃+ pointsK (sqrtK k) (Ecurve ℓ) :=
  (kcCurveCast hcurve).trans (kcPointsEquiv k (Ecurve ℓ))

/-- **`hcomp` for the central twist**, in the exact form of the input of `hκ_central`, for the
concrete comparison and `δ P d = kummerInf (ι P) d`. Kind: PROVED (from the finite-level
Selmer description `KcArithSelmerLevel`). -/
theorem kc_hcomp_central (hk : k < 0) (hS : G.S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ G.S)
    (Gl : KcArithSelmerLevel k G.S (Ecurve ℓ)) (hdiv : GlobalDivisionTowers G.S (centralCurve G))
    (P : (centralCurve G).toAffine.Point) (d : Q2Z2) :
    arithmeticUniversalCoefficientMap ℓ k G.S (arithmeticCentralFull ℓ k G hcurve)
        (kcKummerCoefficientComparison ℓ k G.S (arithmeticCentralFull ℓ k G hcurve) hk hS h2 Gl)
        (centralH1Equiv ℓ k G hcurve (centralKummer G hdiv P) ⊗ₜ[ℤ_[2]] d) =
      kummerInf (sqrtK k) (Ecurve ℓ) (kcCentralPoints ℓ k G hcurve P) d := by
  obtain ⟨q, rfl⟩ := divisibleQuotient_surjective d
  have hdiv' : GlobalDivisionTowers G.S ((Ecurve ℓ).baseChange (QuadraticField k)) :=
    hcurve ▸ hdiv
  have hcast : centralH1Equiv ℓ k G hcurve (centralKummer G hdiv P) =
      CalPoint.kummerClass G.S ((Ecurve ℓ).baseChange (QuadraticField k))
        (arithmeticCentralFull ℓ k G hcurve) hdiv' (kcCurveCast hcurve P) :=
    kc_kummerClass_cast G.S hcurve (centralFullTorsion G) (arithmeticCentralFull ℓ k G hcurve)
      hdiv hdiv' (compactCentral_eq_arithmetic ℓ k G hcurve) P
  rw [hcast]
  obtain ⟨R, hR⟩ := hdiv' (kcCurveCast hcurve P)
  rw [CalPoint.kummerClass_apply G.S _ (arithmeticCentralFull ℓ k G hcurve) hdiv' hR]
  exact kc_hcomp_tower ℓ k G.S (arithmeticCentralFull ℓ k G hcurve) hk hS h2 Gl hR q

omit [(Ecurve ℓ).IsElliptic] in
/-- `k < 0` is not a rational square. Kind: PROVED. -/
theorem kc_not_isSquare (hk : k < 0) : ¬ IsSquare (k : ℚ) := by
  rintro ⟨r, hr⟩
  have h1 : (0 : ℚ) ≤ r * r := mul_self_nonneg r
  have h2 : (k : ℚ) < 0 := by exact_mod_cast hk
  linarith

/-- **`hκ` for the central twist with the concrete comparison** (`KappaGen.hκ_central` with
`I = kcKummerCoefficientComparison`, `δ = kummerInf ∘ ι` and `hcomp = kc_hcomp_central`).
Kind: PROVED from the remaining named inputs of `hκ_central` and `KcArithSelmerLevel`. -/
theorem kc_hκ_central (hk : k < 0) (hS : G.S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ G.S)
    (Gl : KcArithSelmerLevel k G.S (Ecurve ℓ))
    (F : KummerCohomologyFinite ℓ k G.S (arithmeticCentralFull ℓ k G hcurve))
    (hSel : SelmerCorankOneOverK ℓ k) (hdiv : GlobalDivisionTowers G.S (centralCurve G))
    (gen : (centralCurve G).toAffine.Point)
    (hδ : ∀ d, kummerInf (sqrtK k) (Ecurve ℓ) (kcCentralPoints ℓ k G hcurve gen) d = 0 → d = 0) :
    IsFreeLineGenerator ℤ_[2] (centralKummer G hdiv gen) :=
  hκ_central ℓ k G hcurve (kc_not_isSquare k hk)
    (kcKummerCoefficientComparison ℓ k G.S (arithmeticCentralFull ℓ k G hcurve) hk hS h2 Gl) F
    hSel hdiv gen (fun P d => kummerInf (sqrtK k) (Ecurve ℓ) (kcCentralPoints ℓ k G hcurve P) d)
    (kc_hcomp_central ℓ k G hcurve hk hS h2 Gl hdiv) hδ

/-- **`hκ` for a free generator**: `hδ` from E2's `hδ_of_equiv` through `ι`. Kind: PROVED. -/
theorem kc_hκ_central_gen (hk : k < 0) (hS : G.S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ G.S)
    (Gl : KcArithSelmerLevel k G.S (Ecurve ℓ))
    (F : KummerCohomologyFinite ℓ k G.S (arithmeticCentralFull ℓ k G hcurve))
    (hSel : SelmerCorankOneOverK ℓ k) (hdiv : GlobalDivisionTowers G.S (centralCurve G))
    (gen : (centralCurve G).toAffine.Point) (hg : ¬ IsOfFinAddOrder gen)
    (hgen : ∀ P : (centralCurve G).toAffine.Point, ∃ c : ℤ, IsOfFinAddOrder (P - c • gen)) :
    IsFreeLineGenerator ℤ_[2] (centralKummer G hdiv gen) :=
  kc_hκ_central ℓ k G hcurve hk hS h2 Gl F hSel hdiv gen
    (ZInQ.Contrib.CloudB3E2.KummerInj.hδ_of_equiv (sqrtK k) (Ecurve ℓ)
      (kcCentralPoints ℓ k G hcurve) hg hgen)

end Central

end ZInQ.Manuscript.RC
