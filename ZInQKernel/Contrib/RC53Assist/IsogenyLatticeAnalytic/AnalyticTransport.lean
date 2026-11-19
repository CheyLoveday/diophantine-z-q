import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.IsogenyScalar
import ZInQKernel.Contrib.RC53Assist.NewformPeriodsG1.ParametrizationPeriods
import Mathlib.Order.Filter.Germ.Basic

/-!
# Isogenies act on normalized period lattices

The exact statement `IsogenyLatticeAnalyticGlue` is proved here. For an embedding
of a field into `ℂ`, an isogeny with pullback scalar `α`, and normalized period
lattices `L₁`, `L₂`, multiplication by the embedded scalar carries `L₁` into `L₂`.

The proof uses complex germs at the punctured origin. The normalized Weierstrass
coordinates satisfy the curve equation as germs, and their first coordinate is
transcendental because it has a pole. Consequently coordinate-ring evaluation is
injective and extends by localization to rational functions. Every such rational
function has a globally meromorphic, lattice-periodic representative. Differentiation
of these germs is a derivation; the universal property of Kähler differentials
therefore turns the algebraic pullback identity into the analytic derivative identity.

A local inverse of the target Weierstrass function gives a local affine lift. The
meromorphic identity theorem extends the coordinate identity, and periodicity of the
source coordinate gives a local period of the target Weierstrass function. The local
period theorem then gives the required lattice inclusion. The constant term of the
local affine lift cancels, so no pointed analytic lifting theorem is required.

Main result: `isogenyLatticeAnalyticGlue_holds`. There are no unproved realization,
differential-comparison, uniformization, or lattice-transport inputs.

Kinds: definitions and proved theorems. Locators: Silverman, The Arithmetic of
Elliptic Curves, VI.3; `NewformPeriodsG1/ParametrizationPeriods.lean`, the local
inverse and local period theorems; `ModularWeil/IsogenyLattice.lean`, the exact target.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.IsogenyLatticeAnalytic

open Filter Topology Bornology Set Complex
open ZInQ.Contrib.RC53Assist.NewformPeriodsG1

/-- Kind: PROVED. A meromorphic function with periods in `L₁` which locally is the
first coordinate of a point of the curve of `L₂`, with differential multiplier `c`,
has `c L₁ ⊆ L₂`. Locators: Silverman VI.3, the differential equation of the
Weierstrass function; `eventually_weierstrassP_comp_eq`,
`mem_lattice_of_eventually_weierstrassP_add` in the G1 analytic proof. -/
theorem lattice_transport_of_periodic_curve_point
    (L₁ L₂ : PeriodPair) {c : ℂ} (hc : c ≠ 0)
    {X Y : ℂ → ℂ} (hXm : MeromorphicOn X Set.univ)
    (hXper : ∀ (z l : ℂ), l ∈ L₁.lattice → X (z + l) = X z)
    {t₀ : ℂ}
    (hderiv : ∀ᶠ t in 𝓝 t₀, HasDerivAt X (c * (2 * Y t)) t)
    (hcurve : ∀ᶠ t in 𝓝 t₀, Y t ^ 2 = X t ^ 3 - L₂.g₂ / 4 * X t - L₂.g₃ / 4)
    (hYc : ContinuousAt Y t₀) (hY0 : Y t₀ ≠ 0) :
    ∀ l ∈ L₁.lattice, c * l ∈ L₂.lattice := by
  obtain ⟨z₀, hz₀, hPz₀, hP'z₀⟩ := exists_weierstrassP_point L₂ hcurve.self_of_nhds
  let u : ℂ → ℂ := fun t => c * t + (z₀ - c * t₀)
  have hud : ∀ t, HasDerivAt u c t := by
    intro t
    simpa [u] using ((hasDerivAt_id t).const_mul c).add_const (z₀ - c * t₀)
  have hu0 : u t₀ = z₀ := by dsimp [u]; ring
  have hloc : ∀ᶠ t in 𝓝 t₀, L₂.weierstrassP (u t) = X t :=
    eventually_weierstrassP_comp_eq (h := fun _ => c) hderiv hcurve hYc hY0
      hz₀ hPz₀ hP'z₀ (Eventually.of_forall hud) hu0
  let D : ℂ → ℂ := fun t => L₂.weierstrassP (u t) - X t
  have hDm : MeromorphicOn D Set.univ := by
    intro t ht
    exact ((L₂.meromorphic_weierstrassP (u t)).comp_analyticAt
      (g := u) (by dsimp [u]; fun_prop)).sub (hXm t ht)
  have hD0 : meromorphicOrderAt D t₀ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds hloc] with t ht
    simp [D, ht]
  have hglob : ∀ t, ∀ᶠ s in 𝓝[≠] t, L₂.weierstrassP (u s) = X s := by
    intro t
    have h := hDm.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ t₀) (Set.mem_univ t) hD0
    rw [meromorphicOrderAt_eq_top_iff] at h
    filter_upwards [h] with s hs
    simpa [D, sub_eq_zero] using hs
  intro l hl
  have htend : Tendsto (fun t : ℂ => t + l) (𝓝[≠] t₀) (𝓝[≠] (t₀ + l)) :=
    ((hasDerivAt_id t₀).add_const l).tendsto_nhdsNE one_ne_zero
  have hshift : ∀ t, u (t + l) = u t + c * l := by intro t; dsimp [u]; ring
  have hev : ∀ᶠ t in 𝓝[≠] t₀,
      L₂.weierstrassP (u t + c * l) = L₂.weierstrassP (u t) := by
    filter_upwards [htend.eventually (hglob (t₀ + l)), hglob t₀] with t h₁ h₂
    rw [← hshift t, h₁, h₂, hXper t l hl]
  have hut : Tendsto u (𝓝[≠] t₀) (𝓝[≠] z₀) := by
    have h := (hud t₀).tendsto_nhdsNE hc
    rwa [hu0] at h
  let A : ℂ → ℂ := fun z => L₂.weierstrassP (z + c * l) - L₂.weierstrassP z
  have hAm : MeromorphicAt A z₀ :=
    ((L₂.meromorphic_weierstrassP (z₀ + c * l)).comp_analyticAt
      (g := fun z => z + c * l) (by fun_prop)).sub (L₂.meromorphic_weierstrassP z₀)
  rcases hAm.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · apply mem_lattice_of_eventually_weierstrassP_add L₂ (z₀ := z₀)
    filter_upwards [hzero] with z hz
    simpa [A, sub_eq_zero] using hz
  · exfalso
    obtain ⟨t, h₁, h₂⟩ := ((hut.eventually hne).and hev).exists
    exact h₁ (by simp [A, h₂])

namespace Germs

/-- Kind: DEFINITION. Complex germs at the punctured origin. Locator:
`Mathlib/Order/Filter/Germ/Basic.lean`, `Filter.Germ`. -/
abbrev AtZero := Filter.Germ (𝓝[≠] (0 : ℂ)) ℂ

/-- Kind: DEFINITION. Constants embedded in punctured complex germs. Locator:
`Filter.Germ.const` and the pointwise ring operations on germs. -/
def constantHom : ℂ →+* AtZero where
  toFun := Germ.const
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Kind: DEFINITION. Differentiation of punctured complex germs. Locator:
`Filter.EventuallyEq.nhdsNE_deriv`. -/
def derivative : AtZero → AtZero :=
  Germ.map' deriv (fun _ _ h => h.nhdsNE_deriv)

/-- Kind: PROVED. Germ differentiation is computed on any representative. Locator:
`Filter.Germ.map'_coe`. -/
theorem derivative_ofFun (f : ℂ → ℂ) : derivative (f : AtZero) = (deriv f : AtZero) := rfl

/-- Kind: DEFINITION. A germ represented by a globally meromorphic function periodic
under a specified lattice. Locator: Silverman VI.3, elliptic functions; `MeromorphicOn`. -/
def Represented (L : PeriodPair) (g : AtZero) : Prop :=
  ∃ f : ℂ → ℂ, MeromorphicOn f Set.univ ∧
    (∀ z l : ℂ, l ∈ L.lattice → f (z + l) = f z) ∧ (f : AtZero) = g

/-- Kind: PROVED. Constant functions give periodic meromorphic germs. Locators:
`MeromorphicOn.const`, `Germs.Represented`. -/
theorem represented_const (L : PeriodPair) (a : ℂ) : Represented L (constantHom a) :=
  ⟨fun _ => a, MeromorphicOn.const a, fun _ _ _ => rfl, rfl⟩

/-- Kind: PROVED. Addition preserves periodic meromorphic representation. Locators:
`MeromorphicOn.add`, `Filter.Germ.coe_add`. -/
theorem represented_add {L : PeriodPair} {a b : AtZero}
    (ha : Represented L a) (hb : Represented L b) : Represented L (a + b) := by
  obtain ⟨f, hfm, hfp, rfl⟩ := ha
  obtain ⟨g, hgm, hgp, rfl⟩ := hb
  exact ⟨fun z => f z + g z, hfm.add hgm,
    fun z l hl => by beta_reduce; rw [hfp z l hl, hgp z l hl], rfl⟩

/-- Kind: PROVED. Multiplication preserves periodic meromorphic representation.
Locators: `MeromorphicOn.mul`, `Filter.Germ.coe_mul`. -/
theorem represented_mul {L : PeriodPair} {a b : AtZero}
    (ha : Represented L a) (hb : Represented L b) : Represented L (a * b) := by
  obtain ⟨f, hfm, hfp, rfl⟩ := ha
  obtain ⟨g, hgm, hgp, rfl⟩ := hb
  exact ⟨fun z => f z * g z, hfm.mul hgm,
    fun z l hl => by beta_reduce; rw [hfp z l hl, hgp z l hl], rfl⟩

/-- Kind: PROVED. Inversion preserves periodic meromorphic representation, including
zero functions. Locators: `MeromorphicOn.inv`, `Filter.Germ.coe_inv`. -/
theorem represented_inv {L : PeriodPair} {a : AtZero}
    (ha : Represented L a) : Represented L a⁻¹ := by
  obtain ⟨f, hfm, hfp, rfl⟩ := ha
  exact ⟨fun z => (f z)⁻¹, hfm.inv,
    fun z l hl => by beta_reduce; rw [hfp z l hl], rfl⟩

/-- Kind: PROVED. Natural powers preserve periodic meromorphic representation.
Locators: `represented_const`, `represented_mul`. -/
theorem represented_pow {L : PeriodPair} {a : AtZero}
    (ha : Represented L a) (n : ℕ) : Represented L (a ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using represented_const L 1
  | succ n hn => simpa only [pow_succ] using represented_mul hn ha

/-- Kind: PROVED. Polynomial evaluation preserves periodic meromorphic
representation. Locators: `Polynomial.induction_on'`, `represented_add`,
`represented_mul`, `represented_pow`. -/
theorem represented_eval₂ {R : Type*} [Semiring R] {L : PeriodPair}
    (φ : R →+* AtZero) (hφ : ∀ a, Represented L (φ a))
    {x : AtZero} (hx : Represented L x) (p : Polynomial R) :
    Represented L (p.eval₂ φ x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval₂_add] using represented_add hp hq
  | monomial n a =>
    simpa only [Polynomial.eval₂_monomial] using represented_mul (hφ a) (represented_pow hx n)

/-- Kind: PROVED. A nonzero meromorphic germ has a representative nonzero on a
punctured neighbourhood. Locators: `MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`,
`Filter.Germ.coe_eq`. -/
theorem eventually_ne_zero_of_represented {L : PeriodPair} {g : AtZero}
    (hg : Represented L g) (hne : g ≠ 0) {f : ℂ → ℂ} (hf : (f : AtZero) = g) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z ≠ 0 := by
  obtain ⟨r, hrm, hrp, hr⟩ := hg
  have hfr : f =ᶠ[𝓝[≠] (0 : ℂ)] r := Germ.coe_eq.mp (hf.trans hr.symm)
  rcases (hrm 0 (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · exact False.elim (hne (hr.symm.trans (Germ.coe_eq.mpr hz)))
  · filter_upwards [hfr, hz] with z h₁ h₂
    rwa [h₁]

/-- Kind: PROVED. A represented nonzero germ is a unit in the ambient germ ring.
Locators: `eventually_ne_zero_of_represented`, `Units.mkOfMulEqOne`. -/
theorem isUnit_of_represented_ne_zero {L : PeriodPair} {g : AtZero}
    (hg : Represented L g) (hne : g ≠ 0) : IsUnit g := by
  obtain ⟨f, hfm, hfp, hf⟩ := hg
  have hn := eventually_ne_zero_of_represented ⟨f, hfm, hfp, hf⟩ hne hf
  have hmul : g * g⁻¹ = 1 := by
    rw [← hf]
    apply Germ.coe_eq.mpr
    filter_upwards [hn] with z hz
    exact mul_inv_cancel₀ hz
  exact ⟨Units.mkOfMulEqOne g g⁻¹ hmul, rfl⟩

/-- Kind: PROVED. Differentiation is additive on meromorphic germs. Locators:
`MeromorphicAt.eventually_analyticAt`, `deriv_add`. -/
theorem derivative_add {L : PeriodPair} {a b : AtZero}
    (ha : Represented L a) (hb : Represented L b) :
    derivative (a + b) = derivative a + derivative b := by
  obtain ⟨f, hfm, hfp, rfl⟩ := ha
  obtain ⟨g, hgm, hgp, rfl⟩ := hb
  apply Germ.coe_eq.mpr
  filter_upwards [(hfm 0 (Set.mem_univ _)).eventually_analyticAt,
    (hgm 0 (Set.mem_univ _)).eventually_analyticAt] with z hf hg
  exact deriv_add hf.differentiableAt hg.differentiableAt

/-- Kind: PROVED. Differentiation obeys the Leibniz rule on meromorphic germs.
Locators: `MeromorphicAt.eventually_analyticAt`, `deriv_mul`. -/
theorem derivative_mul {L : PeriodPair} {a b : AtZero}
    (ha : Represented L a) (hb : Represented L b) :
    derivative (a * b) = a * derivative b + b * derivative a := by
  obtain ⟨f, hfm, hfp, rfl⟩ := ha
  obtain ⟨g, hgm, hgp, rfl⟩ := hb
  apply Germ.coe_eq.mpr
  filter_upwards [(hfm 0 (Set.mem_univ _)).eventually_analyticAt,
    (hgm 0 (Set.mem_univ _)).eventually_analyticAt] with z hf hg
  calc
    deriv (fun x => f x * g x) z = deriv f z * g z + f z * deriv g z :=
      deriv_mul hf.differentiableAt hg.differentiableAt
    _ = f z * deriv g z + g z * deriv f z := by ring

/-- Kind: PROVED. Constant germs have zero derivative. Locator: `deriv_const`. -/
theorem derivative_const (a : ℂ) : derivative (constantHom a) = 0 := by
  apply Germ.coe_eq.mpr
  filter_upwards with z
  exact deriv_const z a

end Germs

section EmbeddedCoordinates

open ZInQ.Contrib.CloudB3RC53.ModularWeil
open WeierstrassCurve.Affine

variable {F : Type} [Field F] [Algebra F ℂ]

/-- Kind: DEFINITION. The scalar action on complex germs induced by the chosen
field embedding. Locator: `RingHom.toAlgebra`, `Germs.constantHom`. -/
local instance embeddedGermAlgebra : Algebra F Germs.AtZero where
  toSMul := Germ.instSMul
  algebraMap := Germs.constantHom.comp (algebraMap F ℂ)
  commutes' _ _ := mul_comm _ _
  smul_def' r g := by
    induction g using Germ.inductionOn with
    | h f =>
      apply Germ.coe_eq.mpr
      filter_upwards with z
      exact Algebra.smul_def r (f z)

/-- Kind: PROVED. Embedded coefficients are constant complex germs. Locators:
`RingHom.algebraMap_toAlgebra`, `embeddedGermAlgebra`. -/
theorem algebraMap_germ (a : F) :
    algebraMap F Germs.AtZero a = Germs.constantHom ((algebraMap F ℂ) a) := rfl

/-- Kind: PROVED. Polynomial evaluation commutes with passage to a germ. Locators:
`Polynomial.induction_on'`, `Filter.Germ.coe_mul`, `Filter.Germ.coe_pow`. -/
theorem aeval_germ (f : ℂ → ℂ) (p : Polynomial F) :
    Polynomial.aeval (f : Germs.AtZero) p =
      (fun z => p.eval₂ (algebraMap F ℂ) (f z) : Germs.AtZero) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.eval₂_add, hp, hq]
    rfl
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, algebraMap_germ, Polynomial.eval₂_monomial]
    rfl

/-- Kind: PROVED. The germ of `℘ - b` is transcendental over any embedded subfield.
Locators: `tendsto_weierstrassP_cobounded`; `Polynomial.tendsto_norm_atTop` and
`Polynomial.eq_C_of_degree_le_zero`. This is a pole argument, not a uniformization input. -/
theorem transcendental_weierstrass_germ (L : PeriodPair) (b : ℂ) :
    Transcendental F (fun z => L.weierstrassP z - b : Germs.AtZero) := by
  rintro ⟨p, hp, heq⟩
  rw [aeval_germ] at heq
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), p.eval₂ (algebraMap F ℂ) (L.weierstrassP z - b) = 0 :=
    Germ.coe_eq.mp heq
  let q := p.map (algebraMap F ℂ)
  have hq : q ≠ 0 := Polynomial.map_ne_zero hp
  have heval : ∀ᶠ z in 𝓝[≠] (0 : ℂ), q.eval (L.weierstrassP z - b) = 0 := by
    simpa only [q, Polynomial.eval_map] using hev
  have hnorm : Tendsto (fun z => ‖L.weierstrassP z - b‖)
      (𝓝[≠] (0 : ℂ)) atTop := by
    have h := tendsto_weierstrassP_cobounded L (zero_mem _)
    rw [← tendsto_norm_atTop_iff_cobounded] at h
    exact tendsto_atTop_mono (fun z => norm_sub_norm_le (L.weierstrassP z) b)
      (tendsto_atTop_add_const_right _ (-‖b‖) h)
  by_cases hd : 0 < q.degree
  · have hT := q.tendsto_norm_atTop hd hnorm
    obtain ⟨z, hz, hbig⟩ := (heval.and (hT.eventually (eventually_gt_atTop (0 : ℝ)))).exists
    rw [hz, norm_zero] at hbig
    exact (lt_irrefl 0) hbig
  · have hC := Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hd)
    obtain ⟨z, hz⟩ := heval.exists
    rw [hC, Polynomial.eval_C] at hz
    exact hq (hC.trans (by rw [hz, Polynomial.C_0]))

/-- Kind: DEFINITION. The normalized first Weierstrass coordinate. Locator:
Silverman VI.3; `IsLatticeOfEmb`, the normalization by `b₂/12`. -/
def uniformX (E : WeierstrassCurve F) (L : PeriodPair) (z : ℂ) : ℂ :=
  L.weierstrassP z - (algebraMap F ℂ) E.b₂ / 12

/-- Kind: DEFINITION. The normalized second Weierstrass coordinate. Locator:
Silverman VI.3; `dx/(2y+a₁x+a₃)` in normalized Weierstrass coordinates. -/
def uniformY (E : WeierstrassCurve F) (L : PeriodPair) (z : ℂ) : ℂ :=
  (L.derivWeierstrassP z - (algebraMap F ℂ) E.a₁ * uniformX E L z - (algebraMap F ℂ) E.a₃) / 2

/-- Kind: PROVED. The normalized first coordinate has a periodic meromorphic
representative. Locators: `PeriodPair.meromorphic_weierstrassP`,
`PeriodPair.weierstrassP_add_coe`. -/
theorem represented_uniformX (E : WeierstrassCurve F) (L : PeriodPair) :
    Germs.Represented L (uniformX E L : Germs.AtZero) := by
  refine ⟨uniformX E L, ?_, ?_, rfl⟩
  · intro z hz
    exact (L.meromorphic_weierstrassP z).sub (MeromorphicAt.const _ z)
  · intro z l hl
    dsimp only [uniformX]
    rw [L.weierstrassP_add_coe z ⟨l, hl⟩]

/-- Kind: PROVED. The normalized second coordinate has a periodic meromorphic
representative. Locators: `PeriodPair.meromorphic_derivWeierstrassP`,
`PeriodPair.derivWeierstrassP_add_coe`, `represented_uniformX`. -/
theorem represented_uniformY (E : WeierstrassCurve F) (L : PeriodPair) :
    Germs.Represented L (uniformY E L : Germs.AtZero) := by
  have hXm : MeromorphicOn (uniformX E L) Set.univ :=
    fun z _ => (L.meromorphic_weierstrassP z).sub (MeromorphicAt.const _ z)
  refine ⟨uniformY E L, ?_, ?_, rfl⟩
  · intro z hz
    exact (((L.meromorphic_derivWeierstrassP z).sub
      ((MeromorphicAt.const _ z).mul (hXm z hz))).sub
      (MeromorphicAt.const _ z)).div (MeromorphicAt.const _ z)
  · intro z l hl
    dsimp only [uniformY, uniformX]
    rw [L.weierstrassP_add_coe z ⟨l, hl⟩, L.derivWeierstrassP_add_coe z ⟨l, hl⟩]

/-- Kind: PROVED. The normalized coordinates satisfy the equation of the embedded
Weierstrass curve, as germs. Locators: `PeriodPair.derivWeierstrassP_sq`,
`IsLatticeOfEmb`; the identities defining `b₂`, `b₄`, `b₆`, `c₄`, `c₆`. -/
theorem uniformization_equation (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    (E.toAffine⁄Germs.AtZero).toAffine.Equation
      (uniformX E L : Germs.AtZero) (uniformY E L : Germs.AtZero) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  change (uniformY E L : Germs.AtZero) ^ 2 +
      Germs.constantHom ((algebraMap F ℂ) E.a₁) * (uniformX E L : Germs.AtZero) *
        (uniformY E L : Germs.AtZero) +
      Germs.constantHom ((algebraMap F ℂ) E.a₃) * (uniformY E L : Germs.AtZero) =
    (uniformX E L : Germs.AtZero) ^ 3 +
      Germs.constantHom ((algebraMap F ℂ) E.a₂) * (uniformX E L : Germs.AtZero) ^ 2 +
      Germs.constantHom ((algebraMap F ℂ) E.a₄) * (uniformX E L : Germs.AtZero) + Germs.constantHom ((algebraMap F ℂ) E.a₆)
  apply Germ.coe_eq.mpr
  filter_upwards [compl_lattice_mem_nhdsNE L 0] with z hz
  have h := L.derivWeierstrassP_sq z hz
  rw [hL.1, hL.2] at h
  simp only [Function.comp_apply, uniformY, uniformX, WeierstrassCurve.c₄,
    WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat] at h ⊢
  linear_combination h / 4

/-- Kind: DEFINITION. Evaluation of the affine coordinate ring in normalized
Weierstrass germs. Locators: `uniformization_equation`,
`WeierstrassCurve.Affine.CoordinateRing.evalAlgHom`. -/
def coordinateEvaluation (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    E.toAffine.CoordinateRing →ₐ[F] Germs.AtZero :=
  CoordinateRing.evalAlgHom (uniformization_equation E L hL)

/-- Kind: PROVED. Coordinate evaluation sends `x` to the normalized first
Weierstrass germ. Locator: `CoordinateRing.evalAlgHom_of_X`. -/
theorem coordinateEvaluation_X (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    coordinateEvaluation E L hL (coordX E.toAffine) = (uniformX E L : Germs.AtZero) :=
  CoordinateRing.evalAlgHom_of_X _

/-- Kind: PROVED. Coordinate evaluation sends `y` to the normalized second
Weierstrass germ. Locator: `CoordinateRing.evalAlgHom_root`. -/
theorem coordinateEvaluation_Y (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    coordinateEvaluation E L hL (coordY E.toAffine) = (uniformY E L : Germs.AtZero) :=
  CoordinateRing.evalAlgHom_root _

/-- Kind: PROVED. Coordinate evaluation is injective. Locators:
`transcendental_weierstrass_germ`, `CoordinateRing.algHom_injective`.
The first coordinate remains transcendental because it has a pole. -/
theorem coordinateEvaluation_injective (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    Function.Injective (coordinateEvaluation E L hL) := by
  apply CoordinateRing.algHom_injective
  rw [CoordinateRing.mk, AdjoinRoot.mk_C]
  change Transcendental F (coordinateEvaluation E L hL (coordX E.toAffine))
  rw [coordinateEvaluation_X]
  exact transcendental_weierstrass_germ L ((algebraMap F ℂ) E.b₂ / 12)

/-- Kind: PROVED. Every evaluated coordinate-ring element is represented by a
periodic meromorphic function. Locators: `AdjoinRoot.induction_on`,
`CoordinateRing.algHom_mk_eq_evalEval`, `Germs.represented_eval₂`. -/
theorem represented_coordinateEvaluation (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) (a : E.toAffine.CoordinateRing) :
    Germs.Represented L (coordinateEvaluation E L hL a) := by
  refine AdjoinRoot.induction_on E.toAffine.polynomial a ?_
  intro p
  change Germs.Represented L (coordinateEvaluation E L hL (CoordinateRing.mk E.toAffine p))
  rw [CoordinateRing.algHom_mk_eq_evalEval]
  change Germs.Represented L
    ((p.map (Polynomial.mapRingHom (algebraMap F Germs.AtZero))).evalEval
      (coordinateEvaluation E L hL (coordX E.toAffine))
      (coordinateEvaluation E L hL (coordY E.toAffine)))
  rw [coordinateEvaluation_X, coordinateEvaluation_Y,
    ← Polynomial.eval₂_eval₂RingHom_apply]
  apply Germs.represented_eval₂ _ ?_ (represented_uniformY E L) p
  intro q
  apply Germs.represented_eval₂ _ ?_ (represented_uniformX E L) q
  intro a
  rw [algebraMap_germ]
  exact Germs.represented_const L ((algebraMap F ℂ) a)

/-- Kind: PROVED. Denominators become units under coordinate evaluation. Locators:
`coordinateEvaluation_injective`, `represented_coordinateEvaluation`,
`Germs.isUnit_of_represented_ne_zero`. -/
theorem coordinateEvaluation_isUnit (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L)
    (a : nonZeroDivisors E.toAffine.CoordinateRing) :
    IsUnit (coordinateEvaluation E L hL a) := by
  apply Germs.isUnit_of_represented_ne_zero (represented_coordinateEvaluation E L hL a)
  exact (map_ne_zero_iff _ (coordinateEvaluation_injective E L hL)).mpr
    (nonZeroDivisors.ne_zero a.property)

/-- Kind: DEFINITION. Evaluation of rational functions by localization into complex
germs. Locators: `IsLocalization.liftAlgHom`, `coordinateEvaluation_isUnit`.
No assertion about transport of lattices is built into this map. -/
def fieldEvaluation (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    E.toAffine.FunctionField →ₐ[F] Germs.AtZero :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors E.toAffine.CoordinateRing)
    (coordinateEvaluation_isUnit E L hL)

/-- Kind: PROVED. Rational-function evaluation extends coordinate-ring evaluation.
Locator: `IsLocalization.lift_eq`. -/
theorem fieldEvaluation_algebraMap (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) (a : E.toAffine.CoordinateRing) :
    fieldEvaluation E L hL (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField a) =
      coordinateEvaluation E L hL a := by
  exact IsLocalization.lift_eq (coordinateEvaluation_isUnit E L hL) a

/-- Kind: PROVED. A homomorphism from a field into complex germs carries a nonzero
represented inverse to pointwise inversion. Locators: uniqueness of an inverse to a unit;
`Germs.eventually_ne_zero_of_represented`. -/
theorem map_inv_of_represented {K : Type*} [Field K] (L : PeriodPair)
    (f : K →+* Germs.AtZero) {a : K} (ha : a ≠ 0)
    (hr : Germs.Represented L (f a)) : f a⁻¹ = (f a)⁻¹ := by
  have hu : IsUnit (f a) := (isUnit_iff_ne_zero.mpr ha).map f
  have hne : f a ≠ 0 := (map_ne_zero_iff f f.injective).mpr ha
  obtain ⟨r, hrm, hrp, heq⟩ := hr
  have hn := Germs.eventually_ne_zero_of_represented ⟨r, hrm, hrp, heq⟩ hne heq
  apply hu.mul_left_cancel
  calc
    f a * f a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    _ = f a * (f a)⁻¹ := by
      rw [← heq]
      apply Germ.coe_eq.mpr
      filter_upwards [hn] with z hz
      exact (mul_inv_cancel₀ hz).symm

/-- Kind: PROVED. Every rational function is represented by a globally meromorphic
periodic function after normalized evaluation. Locators: `IsFractionRing.div_surjective`,
`represented_coordinateEvaluation`, `map_inv_of_represented`.
This is the rational-function part of the analytic dictionary, proved by fractions. -/
theorem represented_fieldEvaluation (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) (a : E.toAffine.FunctionField) :
    Germs.Represented L (fieldEvaluation E L hL a) := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective E.toAffine.CoordinateRing a
  have hq0 : algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField q ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hrq : Germs.Represented L (fieldEvaluation E L hL
      (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField q)) := by
    rw [fieldEvaluation_algebraMap]
    exact represented_coordinateEvaluation E L hL q
  have hinv : fieldEvaluation E L hL
      ((algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField q)⁻¹) =
      (fieldEvaluation E L hL
        (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField q))⁻¹ :=
    map_inv_of_represented L (fieldEvaluation E L hL).toRingHom hq0 hrq
  rw [div_eq_mul_inv, map_mul, hinv,
    fieldEvaluation_algebraMap, fieldEvaluation_algebraMap]
  exact Germs.represented_mul (represented_coordinateEvaluation E L hL p)
    (Germs.represented_inv (represented_coordinateEvaluation E L hL q))

/-- Kind: PROVED. Rational-function evaluation sends the generic first coordinate
to the normalized Weierstrass germ. Locators: `genericX_eq_coordX`,
`fieldEvaluation_algebraMap`, `coordinateEvaluation_X`. -/
theorem fieldEvaluation_genericX (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    fieldEvaluation E L hL (genericX E.toAffine) = (uniformX E L : Germs.AtZero) := by
  rw [← genericX_eq_coordX, fieldEvaluation_algebraMap, coordinateEvaluation_X]

/-- Kind: PROVED. Rational-function evaluation sends the generic second coordinate
to the normalized Weierstrass germ. Locators: `genericY_eq_coordY`,
`fieldEvaluation_algebraMap`, `coordinateEvaluation_Y`. -/
theorem fieldEvaluation_genericY (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    fieldEvaluation E L hL (genericY E.toAffine) = (uniformY E L : Germs.AtZero) := by
  rw [← genericY_eq_coordY, fieldEvaluation_algebraMap, coordinateEvaluation_Y]

/-- Kind: PROVED. The invariant differential denominator evaluates to the derivative
of the Weierstrass function. Locators: `invariantDifferentialDenom_def`,
`fieldEvaluation_genericX`, `fieldEvaluation_genericY`, `uniformY`. -/
theorem fieldEvaluation_denominator (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    fieldEvaluation E L hL (invariantDifferentialDenom E.toAffine) =
      (L.derivWeierstrassP : Germs.AtZero) := by
  rw [invariantDifferentialDenom_def, map_add, map_add, map_mul, map_mul, map_ofNat,
    fieldEvaluation_genericX, fieldEvaluation_genericY, AlgHom.commutes, AlgHom.commutes,
    algebraMap_germ, algebraMap_germ]
  rw [two_mul]
  apply Germ.coe_eq.mpr
  filter_upwards with z
  simp only [uniformY, uniformX]
  ring

/-- Kind: PROVED. The derivative of the generic first coordinate under evaluation
is the evaluated invariant differential denominator. Locators:
`PeriodPair.analyticOnNhd_weierstrassP`, `PeriodPair.deriv_weierstrassP`,
`fieldEvaluation_denominator`. Thus normalized evaluation sends `ω` to `dz`. -/
theorem derivative_fieldEvaluation_genericX (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    Germs.derivative (fieldEvaluation E L hL (genericX E.toAffine)) =
      fieldEvaluation E L hL (invariantDifferentialDenom E.toAffine) := by
  rw [fieldEvaluation_genericX, fieldEvaluation_denominator]
  apply Germ.coe_eq.mpr
  filter_upwards [compl_lattice_mem_nhdsNE L 0] with z hz
  have hd := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  rw [L.deriv_weierstrassP] at hd
  exact (hd.sub_const ((algebraMap F ℂ) E.b₂ / 12)).deriv

/-- Kind: DEFINITION. The function-field action on the germ ring induced by normalized
evaluation. Locator: `fieldEvaluation`, `RingHom.toAlgebra`. -/
abbrev evaluationAlgebra (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    Algebra E.toAffine.FunctionField Germs.AtZero :=
  (fieldEvaluation E L hL).toRingHom.toAlgebra

/-- Kind: DEFINITION, constructed from proved calculus laws. Differentiation after
evaluation is a derivation on the function field with values in complex germs.
Locators: `represented_fieldEvaluation`, `Germs.derivative_add`,
`Germs.derivative_mul`, `Germs.derivative_const`. -/
def evaluatedDerivation (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) :
    letI := evaluationAlgebra E L hL
    Derivation F E.toAffine.FunctionField Germs.AtZero := by
  letI := evaluationAlgebra E L hL
  refine
    { toFun := fun a => Germs.derivative (fieldEvaluation E L hL a)
      map_add' := ?_
      map_smul' := ?_
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · intro a b
    rw [map_add]
    exact Germs.derivative_add (represented_fieldEvaluation E L hL a)
      (represented_fieldEvaluation E L hL b)
  · intro r a
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def,
      map_mul, AlgHom.commutes, algebraMap_germ]
    rw [Germs.derivative_mul (Germs.represented_const L ((algebraMap F ℂ) r))
      (represented_fieldEvaluation E L hL a), Germs.derivative_const, mul_zero, add_zero]
  · change Germs.derivative (fieldEvaluation E L hL 1) = 0
    rw [map_one]
    simpa only [map_one] using Germs.derivative_const 1
  · intro a b
    change Germs.derivative (fieldEvaluation E L hL (a * b)) =
      fieldEvaluation E L hL a * Germs.derivative (fieldEvaluation E L hL b) +
      fieldEvaluation E L hL b * Germs.derivative (fieldEvaluation E L hL a)
    rw [map_mul]
    exact Germs.derivative_mul (represented_fieldEvaluation E L hL a)
      (represented_fieldEvaluation E L hL b)

/-- Kind: PROVED. The algebraic pullback identity becomes the analytic derivative
identity after normalized evaluation. Locators: `IsPullbackScalar`,
`Derivation.liftKaehlerDifferential_comp_D`, `derivative_fieldEvaluation_genericX`.
This is proved by applying the universal property of Kähler differentials and
cancelling the nonzero source denominator; no analytic isogeny theorem is assumed. -/
theorem evaluated_pullbackScalar (E₁ E₂ : WeierstrassCurve F)
    [E₁.IsElliptic] [E₂.IsElliptic]
    (β : TauCeti.Isogeny E₁.toAffine E₂.toAffine) (α : F)
    (hα : IsPullbackScalar β α) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E₁ L) :
    Germs.derivative (fieldEvaluation E₁ L hL (β.pullback (coordX E₂.toAffine))) =
      Germs.constantHom ((algebraMap F ℂ) α) *
        fieldEvaluation E₁ L hL (β.pullback (omegaDen E₂.toAffine)) := by
  let _ := evaluationAlgebra E₁ L hL
  have : IsScalarTower F E₁.toAffine.FunctionField Germs.AtZero :=
    IsScalarTower.of_algebraMap_eq (fun r => ((fieldEvaluation E₁ L hL).commutes r).symm)
  let δ := evaluatedDerivation E₁ L hL
  unfold IsPullbackScalar at hα
  have h := congrArg δ.liftKaehlerDifferential hα
  simp only [map_smul, Derivation.liftKaehlerDifferential_comp_D] at h
  change fieldEvaluation E₁ L hL
      (algebraMap E₁.toAffine.CoordinateRing E₁.toAffine.FunctionField (omegaDen E₁.toAffine)) *
      Germs.derivative (fieldEvaluation E₁ L hL (β.pullback (coordX E₂.toAffine))) =
    fieldEvaluation E₁ L hL
      (algebraMap F E₁.toAffine.FunctionField α * β.pullback (omegaDen E₂.toAffine)) *
      Germs.derivative (fieldEvaluation E₁ L hL
        (algebraMap E₁.toAffine.CoordinateRing E₁.toAffine.FunctionField (coordX E₁.toAffine))) at h
  rw [invariantDifferentialDenom_eq_omegaDen, genericX_eq_coordX,
    derivative_fieldEvaluation_genericX, map_mul, AlgHom.commutes, algebraMap_germ] at h
  have hu : IsUnit (fieldEvaluation E₁ L hL (invariantDifferentialDenom E₁.toAffine)) :=
    (isUnit_iff_ne_zero.mpr (invariantDifferentialDenom_ne_zero E₁.toAffine)).map
      (fieldEvaluation E₁ L hL).toRingHom
  apply hu.mul_left_cancel
  calc
    fieldEvaluation E₁ L hL (invariantDifferentialDenom E₁.toAffine) *
        Germs.derivative (fieldEvaluation E₁ L hL (β.pullback (coordX E₂.toAffine))) =
      (Germs.constantHom ((algebraMap F ℂ) α) *
        fieldEvaluation E₁ L hL (β.pullback (omegaDen E₂.toAffine))) *
        fieldEvaluation E₁ L hL (invariantDifferentialDenom E₁.toAffine) := h
    _ = fieldEvaluation E₁ L hL (invariantDifferentialDenom E₁.toAffine) *
      (Germs.constantHom ((algebraMap F ℂ) α) *
        fieldEvaluation E₁ L hL (β.pullback (omegaDen E₂.toAffine))) := by ring

/-- Kind: PROVED. Completing the square and removing the quadratic term gives the
short equation attached to the normalized period lattice. Locators: `IsLatticeOfEmb`;
Silverman VI.3; the definitions of the Weierstrass invariants. -/
theorem normalized_curve_equation (E : WeierstrassCurve F) (L : PeriodPair)
    (hL : IsLatticeOfEmb (algebraMap F ℂ) E L) {x y : ℂ}
    (hw : y ^ 2 + (algebraMap F ℂ) E.a₁ * x * y + (algebraMap F ℂ) E.a₃ * y =
      x ^ 3 + (algebraMap F ℂ) E.a₂ * x ^ 2 + (algebraMap F ℂ) E.a₄ * x +
        (algebraMap F ℂ) E.a₆) :
    ((y + y + (algebraMap F ℂ) E.a₁ * x + (algebraMap F ℂ) E.a₃) / 2) ^ 2 =
      (x + (algebraMap F ℂ) E.b₂ / 12) ^ 3 -
        L.g₂ / 4 * (x + (algebraMap F ℂ) E.b₂ / 12) - L.g₃ / 4 := by
  rw [hL.1, hL.2]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  linear_combination hw

/-- Kind: PROVED. An isogeny transports normalized periods by its specified pullback
scalar over an embedded field. Locators: `evaluated_pullbackScalar`,
`represented_fieldEvaluation`, `normalized_curve_equation`,
`lattice_transport_of_periodic_curve_point`.
All rational-function realization and differential comparison inputs are proved above. -/
theorem isogeny_transports_periods (E₁ E₂ : WeierstrassCurve F)
    [E₁.IsElliptic] [E₂.IsElliptic]
    (β : TauCeti.Isogeny E₁.toAffine E₂.toAffine) (α : F)
    (hα : IsPullbackScalar β α) (L₁ L₂ : PeriodPair)
    (hL₁ : IsLatticeOfEmb (algebraMap F ℂ) E₁ L₁)
    (hL₂ : IsLatticeOfEmb (algebraMap F ℂ) E₂ L₂) :
    ∀ l ∈ L₁.lattice, (algebraMap F ℂ) α * l ∈ L₂.lattice := by
  by_cases hc : (algebraMap F ℂ) α = 0
  · intro l hl
    rw [hc, zero_mul]
    exact zero_mem _
  let e := fieldEvaluation E₁ L₁ hL₁
  obtain ⟨X, hXm, hXp, hXg⟩ := represented_fieldEvaluation E₁ L₁ hL₁
    (β.pullback (coordX E₂.toAffine))
  obtain ⟨Y, hYm, hYp, hYg⟩ := represented_fieldEvaluation E₁ L₁ hL₁
    (β.pullback (coordY E₂.toAffine))
  let c : ℂ := (algebraMap F ℂ) α
  let D : ℂ → ℂ := fun z => Y z + Y z + (algebraMap F ℂ) E₂.a₁ * X z +
    (algebraMap F ℂ) E₂.a₃
  have hconst : ∀ a : F, e (β.pullback
      (AdjoinRoot.of E₂.toAffine.polynomial (Polynomial.C a))) =
      Germs.constantHom ((algebraMap F ℂ) a) := by
    intro a
    change e (β.pullback (algebraMap F E₂.toAffine.CoordinateRing a)) = _
    rw [AlgHom.commutes, AlgHom.commutes, algebraMap_germ]
  have hDg : (D : Germs.AtZero) = e (β.pullback (omegaDen E₂.toAffine)) := by
    symm
    simp only [omegaDen, map_add, map_mul, map_ofNat]
    rw [hconst, hconst, ← hXg, ← hYg, two_mul]
    rfl
  have hscalar : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv X z = c * D z := by
    have h := evaluated_pullbackScalar E₁ E₂ β α hα L₁ hL₁
    change Germs.derivative (e (β.pullback (coordX E₂.toAffine))) =
      Germs.constantHom c * e (β.pullback (omegaDen E₂.toAffine)) at h
    rw [← hXg, ← hDg] at h
    exact Germ.coe_eq.mp h
  have hraw : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      Y z ^ 2 + (algebraMap F ℂ) E₂.a₁ * X z * Y z +
        (algebraMap F ℂ) E₂.a₃ * Y z =
      X z ^ 3 + (algebraMap F ℂ) E₂.a₂ * X z ^ 2 +
        (algebraMap F ℂ) E₂.a₄ * X z + (algebraMap F ℂ) E₂.a₆ := by
    have h := CoordinateRing.equation_of_algHom (e.comp β.pullback)
    rw [WeierstrassCurve.Affine.equation_iff] at h
    change e (β.pullback (coordY E₂.toAffine)) ^ 2 +
        Germs.constantHom ((algebraMap F ℂ) E₂.a₁) * e (β.pullback (coordX E₂.toAffine)) *
          e (β.pullback (coordY E₂.toAffine)) +
        Germs.constantHom ((algebraMap F ℂ) E₂.a₃) * e (β.pullback (coordY E₂.toAffine)) =
      e (β.pullback (coordX E₂.toAffine)) ^ 3 +
        Germs.constantHom ((algebraMap F ℂ) E₂.a₂) * e (β.pullback (coordX E₂.toAffine)) ^ 2 +
        Germs.constantHom ((algebraMap F ℂ) E₂.a₄) * e (β.pullback (coordX E₂.toAffine)) +
        Germs.constantHom ((algebraMap F ℂ) E₂.a₆) at h
    rw [← hXg, ← hYg] at h
    filter_upwards [Germ.coe_eq.mp h] with z hz
    simpa only [Function.comp_apply] using hz
  have hden0 : β.pullback (omegaDen E₂.toAffine) ≠ 0 := by
    rw [← TauCeti.Isogeny.fieldPullback_algebraMap,
      invariantDifferentialDenom_eq_omegaDen]
    exact (map_ne_zero β.fieldPullback).mpr (invariantDifferentialDenom_ne_zero E₂.toAffine)
  have hD0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), D z ≠ 0 :=
    Germs.eventually_ne_zero_of_represented
      (represented_fieldEvaluation E₁ L₁ hL₁ (β.pullback (omegaDen E₂.toAffine)))
      ((map_ne_zero_iff e e.injective).mpr hden0) hDg
  have hXd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), HasDerivAt X (c * D z) z := by
    filter_upwards [hscalar, (hXm 0 (Set.mem_univ _)).eventually_analyticAt] with z hs hz
    rw [← hs]
    exact hz.differentiableAt.hasDerivAt
  have hAll : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      HasDerivAt X (c * D z) z ∧
      (Y z ^ 2 + (algebraMap F ℂ) E₂.a₁ * X z * Y z +
        (algebraMap F ℂ) E₂.a₃ * Y z =
        X z ^ 3 + (algebraMap F ℂ) E₂.a₂ * X z ^ 2 +
          (algebraMap F ℂ) E₂.a₄ * X z + (algebraMap F ℂ) E₂.a₆) ∧
      AnalyticAt ℂ Y z ∧ D z ≠ 0 :=
    hXd.and (hraw.and ((hYm 0 (Set.mem_univ _)).eventually_analyticAt.and hD0))
  rw [eventually_nhdsWithin_iff] at hAll
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hAll
  have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball 0 r :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hr)
  have hn : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0 := self_mem_nhdsWithin
  obtain ⟨t₀, ht₀b, ht₀n⟩ := (hb.and hn).exists
  have hU : IsOpen (Metric.ball (0 : ℂ) r ∩ ({0} : Set ℂ)ᶜ) :=
    Metric.isOpen_ball.inter isOpen_compl_singleton
  have hnear : ∀ᶠ z in 𝓝 t₀,
      HasDerivAt X (c * D z) z ∧
      (Y z ^ 2 + (algebraMap F ℂ) E₂.a₁ * X z * Y z +
        (algebraMap F ℂ) E₂.a₃ * Y z =
        X z ^ 3 + (algebraMap F ℂ) E₂.a₂ * X z ^ 2 +
          (algebraMap F ℂ) E₂.a₄ * X z + (algebraMap F ℂ) E₂.a₆) ∧
      AnalyticAt ℂ Y z ∧ D z ≠ 0 := by
    filter_upwards [hU.mem_nhds ⟨ht₀b, ht₀n⟩] with z hz
    exact hball z hz.1 hz.2
  have hcenter := hnear.self_of_nhds
  let Xn : ℂ → ℂ := fun z => X z + (algebraMap F ℂ) E₂.b₂ / 12
  let Yn : ℂ → ℂ := fun z => D z / 2
  apply lattice_transport_of_periodic_curve_point L₁ L₂ hc
    (X := Xn) (Y := Yn) (t₀ := t₀)
  · exact hXm.add (MeromorphicOn.const _)
  · intro z l hl
    dsimp only [Xn]
    rw [hXp z l hl]
  · filter_upwards [hnear] with z hz
    convert hz.1.add_const ((algebraMap F ℂ) E₂.b₂ / 12) using 1
    dsimp only [Xn, Yn, D]
    ring
  · filter_upwards [hnear] with z hz
    exact normalized_curve_equation E₂ L₂ hL₂ hz.2.1
  · have hXc := hcenter.1.continuousAt
    have hYc := hcenter.2.2.1.continuousAt
    exact (((hYc.add hYc).add (continuousAt_const.mul hXc)).add
      continuousAt_const).div_const 2
  · exact div_ne_zero hcenter.2.2.2 two_ne_zero

end EmbeddedCoordinates

/-- Kind: PROVED. The exact analytic isogeny--lattice glue over every subfield of
`ℂ` with a specified embedding. Locators: `ModularWeil/IsogenyLattice.lean`,
`IsogenyLatticeAnalyticGlue`; `isogeny_transports_periods`.
There are no unproved analytic or differential comparison inputs. -/
theorem isogenyLatticeAnalyticGlue_holds :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.IsogenyLatticeAnalyticGlue := by
  intro F _ σ E₁ E₂ h₁ h₂ β α hα L₁ L₂ hL₁ hL₂
  let _ : Algebra F ℂ := σ.toAlgebra
  change ZInQ.Contrib.CloudB3RC53.ModularWeil.IsLatticeOfEmb (algebraMap F ℂ) E₁ L₁ at hL₁
  change ZInQ.Contrib.CloudB3RC53.ModularWeil.IsLatticeOfEmb (algebraMap F ℂ) E₂ L₂ at hL₂
  exact isogeny_transports_periods E₁ E₂ β α hα L₁ L₂ hL₁ hL₂

end ZInQ.Contrib.RC53Assist.IsogenyLatticeAnalytic
