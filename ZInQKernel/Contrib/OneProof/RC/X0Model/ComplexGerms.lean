import ZInQKernel.Contrib.OneProof.ShimuraPointDictGerms
import ZInQKernel.Contrib.OneProof.RC.X0Model.Expansion
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-! The local analytic field used to realize the modular coordinates.
The subring of punctured germs is the meromorphic field construction of
`BShTracesMeromorphic`, with the hypotheses about the marked curve removed.
The use at tex 2915–2919 is on the spot (provenance (c)). -/

noncomputable section

open Filter ShimuraPointDict
open scoped Topology

namespace ZInQ.Manuscript.RC.X0Model

private def meromorphicSubring (z : ℂ) : Subring (PuncturedGerm z) where
  carrier := {g | ∃ f : ℂ → ℂ, (f : PuncturedGerm z) = g ∧ MeromorphicAt f z}
  zero_mem' := ⟨fun _ => 0, rfl, MeromorphicAt.const _ _⟩
  one_mem' := ⟨fun _ => 1, rfl, MeromorphicAt.const _ _⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨_, rfl, hf.add hg⟩
  mul_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨_, rfl, hf.mul hg⟩
  neg_mem' := by
    rintro _ ⟨f, rfl, hf⟩
    exact ⟨_, rfl, hf.neg⟩

abbrev MeromorphicGerm (z : ℂ) := meromorphicSubring z

private theorem meromorphic_isField (z : ℂ) : IsField (MeromorphicGerm z) where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    rintro ⟨g, f, rfl, hf⟩ hne
    have he : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 :=
      hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h =>
        hne (Subtype.ext (Germ.coe_eq.mpr h))
    refine ⟨⟨((fun w => (f w)⁻¹) : PuncturedGerm z), _, rfl, hf.inv⟩, Subtype.ext ?_⟩
    change ((fun w => f w * (f w)⁻¹) : PuncturedGerm z) = (fun _ : ℂ => (1 : ℂ))
    exact Germ.coe_eq.mpr (he.mono fun _ hw => mul_inv_cancel₀ hw)

instance (z : ℂ) : Field (MeromorphicGerm z) := (meromorphic_isField z).toField

abbrev meromorphicIncl (z : ℂ) : MeromorphicGerm z →+* PuncturedGerm z :=
  (meromorphicSubring z).subtype

/-- The germs with a finite limit, with their residue map defined by that limit. -/
def meromorphicValuation (z : ℂ) : ValuationSubring (MeromorphicGerm z) :=
  finiteValuationSubring (meromorphicIncl z) (fun g => g.property)

def valueOfGerm (z : ℂ) : meromorphicValuation z →+* ℂ :=
  finiteValue (meromorphicIncl z)

theorem valueOfGerm_isLocalHom (z : ℂ) : IsLocalHom (valueOfGerm z) := by
  constructor
  intro a ha
  by_cases h : (a.val)⁻¹ ∈ meromorphicValuation z
  · exact isUnit_iff_exists_inv.mpr ⟨⟨_, h⟩,
      Subtype.ext (mul_inv_cancel₀ (fun hz => (isUnit_iff_ne_zero.mp ha) (by
        rw [show a = 0 from Subtype.ext hz, map_zero])))⟩
  · have hz := hasValue_inv_of_not_mem (meromorphicIncl z) (fun g => g.property)
      (g := a.val⁻¹) h
    rw [inv_inv] at hz
    exact ((isUnit_iff_ne_zero.mp ha)
      (hasValue_unique (finiteValue_spec (meromorphicIncl z) a) hz)).elim

def constantGerm (z : ℂ) : ℂ →+* MeromorphicGerm z :=
  ((Germ.coeRingHom _).comp (RingHom.pi fun _ : ℂ => RingHom.id ℂ)).codRestrict
    (meromorphicSubring z) fun c => ⟨fun _ => c, rfl, MeromorphicAt.const _ _⟩

private theorem analyticJ_nonconstant (c : ℂ) : ¬ ∀ τ : UpperHalfPlane, analyticJ τ = c := by
  intro hc
  have hE : Tendsto (fun τ : UpperHalfPlane => ModularForm.E₄ τ ^ 3)
      UpperHalfPlane.atImInfty (𝓝 (1 : ℂ)) := by
    simpa using (EisensteinSeries.tendsto_E_atImInfty (k := 4)).pow 3
  have hD : Tendsto (fun τ : UpperHalfPlane => c * ModularForm.discriminant τ)
      UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
    simpa using ModularForm.discriminant_isZeroAtImInfty.const_mul c
  have heq : (fun τ : UpperHalfPlane => ModularForm.E₄ τ ^ 3) =
      (fun τ : UpperHalfPlane => c * ModularForm.discriminant τ) := by
    funext τ
    exact (div_eq_iff (ModularForm.discriminant_ne_zero τ)).mp (hc τ)
  rw [heq] at hE
  exact one_ne_zero (tendsto_nhds_unique hE hD)

/-- Evaluation of a rational polynomial at the analytic j-germ. -/
def jPolynomial (τ : UpperHalfPlane) : Polynomial ℚ →+* MeromorphicGerm (τ : ℂ) :=
  ((Germ.coeRingHom _).comp (RingHom.pi fun w : ℂ =>
    Polynomial.eval₂RingHom (Rat.castHom ℂ) (analyticJ (UpperHalfPlane.ofComplex w)))).codRestrict
    (meromorphicSubring _) fun P =>
      ⟨_, rfl, ((analyticOn_j τ τ.im_pos).aeval_polynomial P).meromorphicAt⟩

theorem jPolynomial_injective (τ : UpperHalfPlane) : Function.Injective (jPolynomial τ) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  refine le_antisymm ?_ bot_le
  intro P hP
  rw [Ideal.mem_bot]
  by_contra hne
  let H := {z : ℂ | 0 < z.im}
  let f := analyticJ ∘ UpperHalfPlane.ofComplex
  let g := fun w => P.eval₂ (Rat.castHom ℂ) (f w)
  have hg : AnalyticOnNhd ℂ g H := analyticOn_j.aeval_polynomial P
  have hev : g =ᶠ[𝓝[≠] (τ : ℂ)] (fun _ => 0) := by
    apply Germ.coe_eq.mp
    exact congrArg Subtype.val (RingHom.mem_ker.mp hP)
  have hconn : IsPreconnected H := (convex_halfSpace_im_gt 0).isPreconnected
  have hzero : Set.EqOn g (fun _ => 0) H :=
    hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn τ.im_pos
      (((hg τ τ.im_pos).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        continuousAt_const).mp hev)
  let T := {x : ℂ | (P.map (Rat.castHom ℂ)).IsRoot x}
  have hT : T.Finite := Polynomial.finite_setOfPred_isRoot
    ((Polynomial.map_ne_zero_iff (Rat.castHom ℂ).injective).mpr hne)
  apply analyticJ_nonconstant (analyticJ τ)
  intro σ
  have heq := hconn.constant_of_mapsTo hT.isDiscrete analyticOn_j.continuousOn
    (fun w hw => by simpa [T, g, f, Polynomial.IsRoot, Polynomial.eval_map] using hzero hw)
    (x := (σ : ℂ)) (y := (τ : ℂ)) σ.im_pos τ.im_pos
  simpa only [f, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    heq


end ZInQ.Manuscript.RC.X0Model
