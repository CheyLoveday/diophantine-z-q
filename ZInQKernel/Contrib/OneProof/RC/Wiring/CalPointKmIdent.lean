import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointSelfDual
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointKummerClass
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointRenorm
import ZInQKernel.Contrib.OneProof.RC.Wiring.KmIdentCentral

/-!
# Theorem 5.3, Lane RC34: the central class and functional for the Knudsen–Mumford identification

Lemma `ex:arith-central-specialization` (`diophantine_zq.tex`, tex 3895–3910) and the proof of
Proposition `ex:arith-central-calibration` (tex 4005–4021, 4057–4064). Lane RC35's
identification of the calibration block over the ordinary compact central Kummer complex `C_K`
(`KmIdentCentral`) is pinned by a `CentralClassFunctional`: a degree-one cycle `z₀` and a closed
degree-two functional `λ₀` of the retained integral model, with class coefficient
`a₀ = retainedA0 z₀` and functional coefficient `b₀ = retainedB0 λ₀`. This file supplies them
from the genuine objects:

* `centralKummer G hdiv`: the genuine global `2`-adic Kummer map `E^{(h)}(K) → H¹(C_K)` of the
  central twist (`CalPointKummerClass.kummerClass`; `hdiv` is the division-tower input, proved
  from good reduction outside `S` by `globalDivisionTowers_of_goodReduction`).
* `centralClassFunctional hdual D hm`: `z₀ := kummerCentralCycle D m` (a cycle whose class is
  `κ(L m P)`, tex 3901), `λ₀ := kummerCentralFunctional e D m` (the image of a cycle of class
  `c_K(κ(L m P))` under the duality homotopy equivalence `e`, tex 3902), for the point data `D`
  at the address; `hdual` is the integral central Kummer duality (from the nine book statements).
* `centralClassFunctional_v2_a0`, `centralClassFunctional_v2_b0`: `v₂ a₀ = v₂ b₀ = j + vL + v₂ m`
  (tex 3905–3907, 4061–4062).
* `centralClassFunctional_core_v2`: for RC35's identification `I`,
  `v₂ (a b u₀)(0) = 2 (j + vL + v₂ m)` (tex 4063–4064).
* `centralClassFunctional_sevenFields`: the seven fields of the block hold for `I` itself, with
  `a_P = C (a₀ / m)`, `b_P = C (b₀ / m)`.
* `RetainedPointData.ofGenerator`: non-vacuity of the point data relative to its Kummer input.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CalPoint

open CategoryTheory
open ZInQ.Manuscript ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.Height (IsFreeGenerator)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (compactCentralComplex centralCurve
  centralFullTorsion)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape retainedCentralComplex)
open ZInQ.Contrib.RC53Assist.CalibrationShape (IntegralCentralKummerDuality)
open ZInQ.Contrib.CloudB3RC53.Calibration (central_mul v2_mul)
open ZInQ.Manuscript.RC.Wiring.KmIdent (retainedA0 retainedB0 CentralClassFunctional
  centralKMIdentModelOf centralKMIdentModelOf_a centralKMIdentModelOf_b centralKMIdentModelOf_u₀
  centralKMIdentModelOf_core)

attribute [local instance] Nat.fact_prime_two

section Central

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ} (G : GenuineKummerData K E₀ hZ)
  (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
  (H : CalibrationCohomologyShape (compactCentralComplex G))

omit [DecidableEq K] in
/-- **The class coefficient is lane RC35's `retainedA0`**, by definition. PROVED. -/
theorem retainedA0_eq_freeCoord1 (z0 : (retainedCentralComplex G hfinite).X 1) :
    retainedA0 G hfinite H z0 = freeCoord1 G hfinite H z0 := rfl

omit [DecidableEq K] in
/-- **The functional coefficient is lane RC35's `retainedB0`**, by definition. PROVED. -/
theorem retainedB0_eq_e2 (lam0 : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2]) :
    retainedB0 G hfinite H lam0 = lam0 (e2 G hfinite H) := rfl

/-- **The genuine Kummer map of the central twist** `E^{(h)}(K) → H¹(C_K)` (tex 3901, 4007–4014):
the global `2`-adic Kummer class map of `CalPointKummerClass`. Kind: definition. -/
def centralKummer (hdiv : GlobalDivisionTowers G.S (centralCurve G)) :
    (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1 :=
  kummerClass G.S (centralCurve G) (centralFullTorsion G) hdiv

/-- **The point data at an address for the genuine Kummer map.** Kind: definition. -/
abbrev CentralPointData (hdiv : GlobalDivisionTowers G.S (centralCurve G)) (j vL : ℤ) :=
  RetainedPointData G (centralKummer G hdiv) j vL

/-- The duality homotopy equivalence, with source the retained model. Kind: definition. -/
def dualityEquiv (hdual : IntegralCentralKummerDuality G hfinite) :
    HomotopyEquiv (retainedCentralComplex G hfinite)
      (ZInQ.Contrib.CloudB3RC53.SelmerDuality.dualCx
        (ZInQ.Contrib.RC53Assist.CalibrationShape.centralRetainedGCx G hfinite) 3).toCC :=
  Classical.choice hdual

variable {G hfinite H}

/-- A `2`-adic integer of finite valuation is nonzero. PROVED. -/
theorem ne_zero_of_v2 {x : ℤ_[2]} {n : ℤ} (h : v2 (x : ℚ_[2]) = (n : WithTop ℤ)) : x ≠ 0 := by
  rintro rfl
  rw [PadicInt.coe_zero] at h
  unfold v2 at h
  rw [AddValuation.map_zero] at h
  exact WithTop.top_ne_coe h

variable {κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1} {j vL : ℤ}

/-- **The central class and functional of Lemma `ex:arith-central-specialization`, in lane
RC35's form** (tex 3901–3902): `z₀` a cycle of class `κ(L m P)`, `λ₀ = e(y₀)` for a cycle `y₀` of
class `c_K(κ(L m P))`. Kind: definition. -/
def centralClassFunctional (hdual : IntegralCentralKummerDuality G hfinite)
    (D : RetainedPointData G κ j vL) {m : ℤ} (hm : m ≠ 0) : CentralClassFunctional G hfinite H where
  z0 := kummerCentralCycle D m
  hz0 := kummerCentralCycle_closed D m
  lam0 := kummerCentralFunctional (dualityEquiv G hfinite hdual) D m
  hlam0 := kummerCentralFunctional_closed (dualityEquiv G hfinite hdual) D m
  ha0 := ne_zero_of_v2 (v2_centralA0 H D hm)
  hb0 := ne_zero_of_v2 (v2_centralB0_selfDual H (dualityEquiv G hfinite hdual) D hm)

/-- **The class coefficient has valuation `j + vL + v₂ m`** (tex 3905–3907, 4061–4062). PROVED. -/
theorem centralClassFunctional_v2_a0 (hdual : IntegralCentralKummerDuality G hfinite)
    (D : RetainedPointData G κ j vL) {m : ℤ} (hm : m ≠ 0) :
    v2 ((retainedA0 G hfinite H (centralClassFunctional (H := H) hdual D hm).z0 : ℤ_[2]) :
      ℚ_[2]) = ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) :=
  v2_centralA0 H D hm

/-- **The functional coefficient has valuation `j + vL + v₂ m`** (tex 3977–3982, 4015–4018,
4061–4062). PROVED. -/
theorem centralClassFunctional_v2_b0 (hdual : IntegralCentralKummerDuality G hfinite)
    (D : RetainedPointData G κ j vL) {m : ℤ} (hm : m ≠ 0) :
    v2 ((retainedB0 G hfinite H (centralClassFunctional (H := H) hdual D hm).lam0 : ℤ_[2]) :
      ℚ_[2]) = ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) :=
  v2_centralB0_selfDual H (dualityEquiv G hfinite hdual) D hm

/-- **The point half of the Kummer valuation for lane RC35's identification** (tex 4063–4064):
`v₂ (a b u₀)(0) = 2 (j + vL + v₂ m)`. PROVED. -/
theorem centralClassFunctional_core_v2 (hdual : IntegralCentralKummerDuality G hfinite)
    (D : RetainedPointData G κ j vL) {m : ℤ} (hm : m ≠ 0) :
    v2 (central ((centralKMIdentModelOf G hfinite H (centralClassFunctional hdual D hm)).a *
      (centralKMIdentModelOf G hfinite H (centralClassFunctional hdual D hm)).b *
        (centralKMIdentModelOf G hfinite H (centralClassFunctional hdual D hm)).u₀)) =
      ((2 * (j + vL + ((padicValInt 2 m : ℕ) : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [centralKMIdentModelOf_core, v2_mul, centralClassFunctional_v2_a0 hdual D hm,
    centralClassFunctional_v2_b0 hdual D hm, ← WithTop.coe_add]
  congr 1
  ring

/-- **The seven fields of the calibration block hold for lane RC35's identification**, with
`a_P = C (a₀ / m)`, `b_P = C (b₀ / m)` (tex 3898–3906, 4061–4064). PROVED. -/
theorem centralClassFunctional_sevenFields (hdual : IntegralCentralKummerDuality G hfinite)
    (D : RetainedPointData G κ j vL) {m : ℤ} (hm : m ≠ 0) :
    SevenFields (centralKMIdentModelOf G hfinite H (centralClassFunctional hdual D hm)) j vL m
      (PowerSeries.C (((retainedA0 G hfinite H (centralClassFunctional (H := H) hdual D hm).z0 :
        ℤ_[2]) : ℚ_[2]) / (m : ℚ_[2])))
      (PowerSeries.C (((retainedB0 G hfinite H
        (centralClassFunctional (H := H) hdual D hm).lam0 : ℤ_[2]) : ℚ_[2]) / (m : ℚ_[2]))) :=
  sevenFields_of_central _ hm (centralKMIdentModelOf_a _) (centralKMIdentModelOf_b _)
    (centralKMIdentModelOf_u₀ _) (centralClassFunctional_v2_a0 hdual D hm)
    (centralClassFunctional_v2_b0 hdual D hm)

end Central

/-! ### From the book statements -/

section Book

open ZInQ.Manuscript.RC.Wiring (CalibrationBookProps)

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ} (G : GenuineKummerData K E₀ hZ)
  (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))

omit [DecidableEq K] in
/-- **The integral central Kummer duality from the nine book statements** of the calibration
leaf's literature form (the same statements as its disk half; tex 4015–4018).
PROVED (from `CalibrationBookProps`). -/
theorem bookDuality (B : CalibrationBookProps) (hK : NumberField.IsTotallyComplex K)
    (h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (2 : NumberField.RingOfIntegers K) ∈ v.asIdeal → v ∈ G.S) :
    IntegralCentralKummerDuality G hfinite :=
  ZInQ.Contrib.RC53Assist.DKLocalAdapter.integralCentralKummerDuality_of_literature_with_finiteness
    G hfinite B.milneLocalDuality B.milneFiniteLocalDuality B.milneFiniteDegreeBound
    B.nekovarCompactLocality B.nekovarGlobalDuality B.milneGlobalFiniteness
    B.milneLocalFiniteness B.milneGlobalDimensionTwo B.milneLocalDimensionTwo hK h2

variable {G hfinite} {H : CalibrationCohomologyShape (compactCentralComplex G)}

/-- **The point half of the calibration from the book statements and the point data**
(tex 3895–3910, 4005–4021, 4057–4064): for the genuine Kummer map, the integral duality of the
book statements, and point data `D` at the address, lane RC35's identification pinned by
`centralClassFunctional` has `v₂ (a b u₀)(0) = 2 (j + vL + v₂ m)`, and the seven fields of the
block hold for it. PROVED. -/
theorem pointHalf_of_book (B : CalibrationBookProps) (hK : NumberField.IsTotallyComplex K)
    (h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (2 : NumberField.RingOfIntegers K) ∈ v.asIdeal → v ∈ G.S)
    (hdiv : GlobalDivisionTowers G.S (centralCurve G)) {j vL : ℤ}
    (D : CentralPointData G hdiv j vL) {m : ℤ} (hm : m ≠ 0) :
    let Z := centralClassFunctional (H := H) (bookDuality G hfinite B hK h2) D hm
    let I := centralKMIdentModelOf G hfinite H Z
    v2 (central (I.a * I.b * I.u₀)) =
        ((2 * (j + vL + ((padicValInt 2 m : ℕ) : ℤ)) : ℤ) : WithTop ℤ) ∧
      SevenFields I j vL m
        (PowerSeries.C (((retainedA0 G hfinite H Z.z0 : ℤ_[2]) : ℚ_[2]) / (m : ℚ_[2])))
        (PowerSeries.C (((retainedB0 G hfinite H Z.lam0 : ℤ_[2]) : ℚ_[2]) / (m : ℚ_[2]))) :=
  ⟨centralClassFunctional_core_v2 _ D hm, centralClassFunctional_sevenFields _ D hm⟩

end Book

/-! ### Non-vacuity of the point data -/

section NonVacuity

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ} {G : GenuineKummerData K E₀ hZ}
  {κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1}

/-- **Non-vacuity of `RetainedPointData`**: a free generator `g` of `E^{(h)}(K)` modulo torsion
whose Kummer class generates `H¹(C_K)` modulo torsion gives point data with `P = g`, `L = 1`
(`j = vL = 0`) and `c_K` the identity. Its only inputs are the rank-one free generator
(tex 4020–4021) and the Kummer identification of the free lattice (tex 4007–4014). PROVED. -/
def RetainedPointData.ofGenerator (g : (centralCurve G).toAffine.Point) (hg : IsFreeGenerator g)
    (hκ : IsFreeLineGenerator ℤ_[2] (κ g)) : RetainedPointData G κ 0 0 where
  L := 1
  hL := one_ne_zero
  hvL := by simp
  P := g
  gen := g
  hgen := hg
  nP := 1
  hnP := by simp
  hnP0 := one_ne_zero
  hj := by simp
  hκ := hκ
  cK := LinearMap.id
  hcK := fun _ => rfl

end NonVacuity

end ZInQ.Manuscript.RC.CalPoint
