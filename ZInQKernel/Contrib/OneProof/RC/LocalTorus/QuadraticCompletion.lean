import ZInQKernel.Contrib.OneProof.RC.LocalTorus.CompletedIntegers
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Embeddings
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-! The completed quadratic order has the same affine basis as the
global order. Tex 9164–9165, on-the-spot (c). -/

noncomputable section

set_option maxHeartbeats 1200000

open scoped NumberField Topology

namespace ZInQ.Manuscript.RC.LocalTorus

open Adelic O7Actual IsDedekindDomain HeightOneSpectrum Filter WithZero

variable {F : Type*} [Field F] [NumberField F] {d : ℤ}

abbrev AdicProduct (F : Type*) [Field F] [NumberField F] (p : Prime) :=
  ∀ v : PlacesAbove F p, v.val.adicCompletion F

abbrev generator (Q : QuadraticBasis F d) : F := (1 + Q.model QuadraticAlgebra.omega) / 2

theorem affine_relation (Q : QuadraticBasis F d) {c : ℤ} (hc : d = 1 - 4 * c) :
    generator Q * generator Q = -(c : F) + generator Q := by
  have h : Q.model QuadraticAlgebra.omega * Q.model QuadraticAlgebra.omega = (d : F) := by
    rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  have hcast : (d : F) = 1 - 4 * (c : F) := by exact_mod_cast hc
  rw [hcast] at h
  have hα : 2 * generator Q - 1 = Q.model QuadraticAlgebra.omega := by unfold generator; ring
  rw [← hα] at h
  linear_combination h / 4

theorem generator_linear_independent (Q : QuadraticBasis F d) {i j : ℚ}
    (h : (i : F) + (j : F) * generator Q = 0) : i = 0 ∧ j = 0 := by
  let f := Q.model.symm
  have hα : f (generator Q) =
      (1 / 2 : ℚ) • (1 + QuadraticAlgebra.omega) := by
    have hgf : generator Q = (1 / 2 : ℚ) • (1 + Q.model QuadraticAlgebra.omega) := by
      rw [Algebra.smul_def]
      change (1 + Q.model _) / 2 = ((1 / 2 : ℚ) : F) * _
      push_cast
      ring
    rw [hgf, map_smul, map_add, map_one]
    change _ • (1 + Q.model.symm (Q.model _)) = _
    rw [AlgEquiv.symm_apply_apply]
  have h₀ : algebraMap ℚ F i + j • generator Q = 0 := by
    rw [Algebra.smul_def]
    exact h
  have h' : algebraMap ℚ _ i + (j : ℚ) • ((1 / 2 : ℚ) •
      (1 + QuadraticAlgebra.omega : QuadraticAlgebra ℚ (d : ℚ) 0)) = 0 := by
    simpa only [map_add, map_zero, map_smul, f.commutes, hα]
      using congrArg f h₀
  have hj : j = 0 := by
    have hj := congrArg QuadraticAlgebra.im h'
    simp [QuadraticAlgebra.im_one] at hj
    exact hj
  subst j
  exact ⟨by simpa using congrArg QuadraticAlgebra.re h', rfl⟩

/-- The affine basis also spans over the rational field. -/
theorem generator_rational_span (Q : QuadraticBasis F d) (x : F) :
    ∃ i j : ℚ, x = (i : F) + (j : F) * generator Q := by
  let y := Q.model.symm x
  refine ⟨y.re - y.im, 2 * y.im, ?_⟩
  have h := congrArg Q.model (QuadraticAlgebra.re_smul_add_im_smul y)
  simp only [map_add, map_smul, map_one] at h
  have hy : Q.model y = x := Q.model.apply_symm_apply x
  rw [hy] at h
  rw [← h, Algebra.smul_def, Algebra.smul_def, mul_one]
  change (y.re : F) + (y.im : F) * _ = _
  push_cast
  unfold generator
  ring

def affineEval (Q : QuadraticBasis F d) (p : Prime) (a b : ℚ_[p.val]) :
    AdicProduct F p :=
  fun v => completedScalar p v a +
    completedScalar p v b * algebraMap F (v.val.adicCompletion F) (generator Q)

theorem affineEval_rat (Q : QuadraticBasis F d) (p : Prime) (i j : ℚ)
    (v : PlacesAbove F p) :
    affineEval Q p (i : ℚ_[p.val]) (j : ℚ_[p.val]) v =
      algebraMap F (v.val.adicCompletion F) ((i : F) + (j : F) * generator Q) := by
  simp only [affineEval, completedScalar_ratCast, map_add, map_mul]

private theorem affineEval_int (Q : QuadraticBasis F d) (p : Prime) (i j : ℤ)
    (v : PlacesAbove F p) :
    affineEval Q p (i : ℚ_[p.val]) (j : ℚ_[p.val]) v =
      algebraMap F (v.val.adicCompletion F) ((i : F) + (j : F) * generator Q) := by
  simpa only [Rat.cast_intCast] using affineEval_rat Q p (i : ℚ) (j : ℚ) v

private theorem localInteg_eval (Q : QuadraticBasis F d) (p : Prime) (v : PlacesAbove F p)
    (a b : ℤ_[p.val]) :
    affineEval Q p a.val b.val v ∈ v.val.adicCompletionIntegers F :=
  add_mem (completedScalar_mem p v a) (mul_mem (completedScalar_mem p v b)
    (coe_algebraMap_mem (𝓞 F) F v.val (⟨generator Q, Q.half_integral⟩ : 𝓞 F)))

private theorem choose_residue (p : Prime) (x : ℤ_[p.val]) :
    ∃ n : ℤ, (p.val : ℤ_[p.val]) ∣ x - (n : ℤ_[p.val]) := by
  let r := PadicInt.toZModPow 1 x
  let _ : NeZero (p.val ^ 1) := ⟨pow_ne_zero _ p.prop.ne_zero⟩
  refine ⟨(r.val : ℤ), ?_⟩
  have h : x - ((r.val : ℤ) : ℤ_[p.val]) ∈ RingHom.ker (PadicInt.toZModPow (p := p.val) 1) := by
    rw [RingHom.mem_ker, map_sub, map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self]
  rwa [PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton] at h

private theorem nat_scalar (p : Prime) (v : PlacesAbove F p) (n : ℕ) :
    completedScalar p v (n : ℚ_[p.val]) = (n : v.val.adicCompletion F) := map_natCast _ _

private theorem coefficients_dvd (Q : QuadraticBasis F d) (p : Prime)
    (a b : ℤ_[p.val])
    (h : ∀ v : PlacesAbove F p, Valued.v (affineEval Q p a.val b.val v) ≤
      Valued.v (p.val : v.val.adicCompletion F)) :
    (p.val : ℤ_[p.val]) ∣ a ∧ (p.val : ℤ_[p.val]) ∣ b := by
  obtain ⟨i, hia⟩ := choose_residue p a
  obtain ⟨j, hjb⟩ := choose_residue p b
  obtain ⟨k, hk⟩ := hia
  obtain ⟨l, hl⟩ := hjb
  have hdiff (v : PlacesAbove F p) :
      affineEval Q p a.val b.val v - affineEval Q p (i : ℚ_[p.val]) (j : ℚ_[p.val]) v =
        (p.val : v.val.adicCompletion F) * affineEval Q p k.val l.val v := by
    have hk' : a.val - (i : ℚ_[p.val]) = (p.val : ℚ_[p.val]) * k.val := by
      exact congrArg Subtype.val hk
    have hl' : b.val - (j : ℚ_[p.val]) = (p.val : ℚ_[p.val]) * l.val := by
      exact congrArg Subtype.val hl
    have ha : a.val = (i : ℚ_[p.val]) + (p.val : ℚ_[p.val]) * k.val := by linear_combination hk'
    have hb : b.val = (j : ℚ_[p.val]) + (p.val : ℚ_[p.val]) * l.val := by linear_combination hl'
    simp only [affineEval]
    rw [ha, hb, map_add, map_add, map_mul, map_mul, nat_scalar]
    ring
  let t : 𝓞 F := (i : 𝓞 F) + (j : 𝓞 F) * ⟨generator Q, Q.half_integral⟩
  have ht := dvd_of_local_valuation p t (fun v => by
    have he : affineEval Q p (i : ℚ_[p.val]) (j : ℚ_[p.val]) v =
        algebraMap (𝓞 F) (v.val.adicCompletion F) t := by
      rw [affineEval_int, IsScalarTower.algebraMap_apply (𝓞 F) F]
      apply congrArg (algebraMap F (v.val.adicCompletion F))
      simp only [t, map_add, map_mul, map_intCast] <;> rfl
    have hv (a : 𝓞 F) : Valued.v (algebraMap (𝓞 F) (v.val.adicCompletion F) a) =
        v.val.intValuation a :=
      (valuedAdicCompletion_eq_valuation (K := F) v.val a).trans
        (v.val.valuation_of_algebraMap (K := F) a)
    rw [← hv t, ← hv (p.val : 𝓞 F), map_natCast, ← he]
    have hb : Valued.v (affineEval Q p a.val b.val v -
      affineEval Q p (i : ℚ_[p.val]) (j : ℚ_[p.val]) v) ≤
        Valued.v (p.val : v.val.adicCompletion F) := by
      rw [hdiff, map_mul]
      exact mul_le_of_le_one_right' (localInteg_eval Q p v k l)
    rw [← sub_sub_cancel (affineEval Q p a.val b.val v)
      (affineEval Q p (i : ℚ_[p.val]) (j : ℚ_[p.val]) v)]
    exact (Valuation.map_sub _ _ _).trans (max_le (h v) hb))
  obtain ⟨y, hy⟩ := ht
  obtain ⟨u, w, huw⟩ := Q.spans y
  have hzero : ((i - (p.val : ℤ) * u : ℤ) : F) +
      ((j - (p.val : ℤ) * w : ℤ) : F) * generator Q = 0 := by
    have hh := congrArg (algebraMap (𝓞 F) F) hy
    simp only [t, map_add, map_mul, map_intCast, map_natCast] at hh
    change (i : F) + (j : F) * generator Q = (p.val : F) * (y : F) at hh
    rw [huw] at hh
    push_cast
    linear_combination hh
  obtain ⟨hi, hj⟩ := generator_linear_independent Q
    (i := ((i - (p.val : ℤ) * u : ℤ) : ℚ)) (j := ((j - (p.val : ℤ) * w : ℤ) : ℚ))
    (by simpa only [Rat.cast_intCast] using hzero)
  constructor
  · rw [← sub_add_cancel a (i : ℤ_[p.val])]
    apply dvd_add (show (p.val : ℤ_[p.val]) ∣ a - (i : ℤ_[p.val]) from ⟨k, hk⟩)
    exact ⟨(u : ℤ_[p.val]), by exact_mod_cast (sub_eq_zero.mp (Int.cast_eq_zero.mp hi))⟩
  · rw [← sub_add_cancel b (j : ℤ_[p.val])]
    apply dvd_add (show (p.val : ℤ_[p.val]) ∣ b - (j : ℤ_[p.val]) from ⟨l, hl⟩)
    exact ⟨(w : ℤ_[p.val]), by exact_mod_cast (sub_eq_zero.mp (Int.cast_eq_zero.mp hj))⟩

/-- If all the completed values of an affine expression are integral, the
two rational local coefficients are integral. -/
theorem affineEval_mem_iff (Q : QuadraticBasis F d) (p : Prime) (a b : ℚ_[p.val]) :
    (∀ v : PlacesAbove F p, affineEval Q p a b v ∈ v.val.adicCompletionIntegers F) ↔
      ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 := by
  refine ⟨?_, fun ⟨ha, hb⟩ v => localInteg_eval Q p v ⟨a, ha⟩ ⟨b, hb⟩⟩
  intro h
  have impossible (r : ℚ_[p.val]) (hr : ‖r‖ < 1) (ha : ‖r * a‖ ≤ 1)
      (hb : ‖r * b‖ ≤ 1) :
      (p.val : ℤ_[p.val]) ∣ (⟨r * a, ha⟩ : ℤ_[p.val]) ∧
      (p.val : ℤ_[p.val]) ∣ (⟨r * b, hb⟩ : ℤ_[p.val]) := by
    apply coefficients_dvd Q p
    let ri : ℤ_[p.val] := ⟨r, hr.le⟩
    obtain ⟨s, hs⟩ := (PadicInt.norm_lt_one_iff_dvd ri).mp hr
    intro v
    have he : r = (p.val : ℚ_[p.val]) * s.val := congrArg Subtype.val hs
    have hm := completedScalar_mem p v s
    have hz : Valued.v (completedScalar p v r) ≤ Valued.v (p.val : v.val.adicCompletion F) := by
      rw [he, map_mul, nat_scalar, map_mul]
      exact mul_le_of_le_one_right' hm
    have heval : affineEval Q p (r * a) (r * b) v =
        completedScalar p v r * affineEval Q p a b v := by simp only [affineEval, map_mul]; ring
    rw [heval, map_mul]
    exact (mul_le_of_le_one_right' (h v)).trans hz
  by_contra! hn
  rcases le_total ‖b‖ ‖a‖ with hab | hab
  · have ha : 1 < ‖a‖ := by
      by_contra! hle
      exact (hn hle).not_ge (hab.trans hle)
    have ha0 : a ≠ 0 := by intro he; rw [he, norm_zero] at ha; linarith
    have hi : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0
    have hh : ‖a⁻¹ * b‖ ≤ 1 := by rw [norm_mul, norm_inv, ← div_eq_inv_mul]; exact
      (div_le_one (zero_lt_one.trans ha)).mpr hab
    have ht := (impossible a⁻¹ (by rwa [norm_inv, inv_lt_one₀ (zero_lt_one.trans ha)])
      (by rw [hi, norm_one]) hh).1
    have ht' := (PadicInt.norm_lt_one_iff_dvd _).mpr ht
    change ‖a⁻¹ * a‖ < 1 at ht'
    rw [hi, norm_one] at ht'
    exact (lt_irrefl 1) ht'
  · have hb : 1 < ‖b‖ := by
      by_contra! hle
      exact (hn (hab.trans hle)).not_ge hle
    have hb0 : b ≠ 0 := by intro he; rw [he, norm_zero] at hb; linarith
    have hi : b⁻¹ * b = 1 := inv_mul_cancel₀ hb0
    have hh : ‖b⁻¹ * a‖ ≤ 1 := by rw [norm_mul, norm_inv, ← div_eq_inv_mul]; exact
      (div_le_one (zero_lt_one.trans hb)).mpr hab
    have ht := (impossible b⁻¹ (by rwa [norm_inv, inv_lt_one₀ (zero_lt_one.trans hb)])
      hh (by rw [hi, norm_one])).2
    have ht' := (PadicInt.norm_lt_one_iff_dvd _).mpr ht
    change ‖b⁻¹ * b‖ < 1 at ht'
    rw [hi, norm_one] at ht'
    exact (lt_irrefl 1) ht'

/-- The completed integer ring, in affine coordinates, surjects onto
the product of the actual completed valuation rings. -/
theorem integral_eval_surjective (Q : QuadraticBasis F d) (p : Prime) :
    Function.Surjective (fun ab : ℤ_[p.val] × ℤ_[p.val] => fun v : PlacesAbove F p =>
      (⟨affineEval Q p ab.1.val ab.2.val v, localInteg_eval Q p v ab.1 ab.2⟩ :
        v.val.adicCompletionIntegers F)) := by
  let g := fun ab : ℤ_[p.val] × ℤ_[p.val] => fun v : PlacesAbove F p =>
    (⟨affineEval Q p ab.1.val ab.2.val v, localInteg_eval Q p v ab.1 ab.2⟩ :
      v.val.adicCompletionIntegers F)
  have hg : Continuous g := by
    apply continuous_pi
    intro v
    apply Continuous.subtype_mk
    change Continuous (fun ab : ℤ_[p.val] × ℤ_[p.val] =>
      completedScalar p v ab.1.val + completedScalar p v ab.2.val *
        algebraMap F (v.val.adicCompletion F) (generator Q))
    exact ((continuous_completedScalar p v).comp (continuous_subtype_val.comp continuous_fst)).add
      (((continuous_completedScalar p v).comp (continuous_subtype_val.comp continuous_snd)).mul
        continuous_const)
  have hc : IsClosed (Set.range g) := isCompact_range hg |>.isClosed
  have hd := denseRange_diagonal_integers (F := F) p
  have hsub : Set.range (fun a : 𝓞 F => fun v : PlacesAbove F p =>
      algebraMap (𝓞 F) (v.val.adicCompletionIntegers F) a) ⊆ Set.range g := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨i, j, hij⟩ := Q.spans a
    refine ⟨((i : ℤ_[p.val]), (j : ℤ_[p.val])), funext fun v => Subtype.ext ?_⟩
    change affineEval Q p (i : ℚ_[p.val]) (j : ℚ_[p.val]) v =
      algebraMap (𝓞 F) (v.val.adicCompletion F) a
    rw [affineEval_int, IsScalarTower.algebraMap_apply (𝓞 F) F]
    exact congrArg (algebraMap F (v.val.adicCompletion F)) hij.symm
  intro z
  exact (closure_minimal hsub hc) (hd z)

/-- Inverting the rational prime gives every element of the product
of completed fields. -/
theorem eval_surjective (Q : QuadraticBasis F d) (p : Prime) :
    Function.Surjective (fun ab : ℚ_[p.val] × ℚ_[p.val] => affineEval Q p ab.1 ab.2) := by
  intro x
  have hlarge (v : PlacesAbove F p) : ∀ᶠ n : ℕ in atTop,
      (p.val : v.val.adicCompletion F) ^ n * x v ∈ v.val.adicCompletionIntegers F := by
    have h := (Valued.tendsto_zero_pow_of_v_lt_one (valuation_prime_lt_one p v)).mul_const (x v)
    rw [zero_mul] at h
    exact h.eventually_mem ((Valued.isOpen_valuationSubring
      (v.val.adicCompletion F) (Γ₀ := ℤᵐ⁰)).mem_nhds (zero_mem _))
  obtain ⟨n, hn⟩ := (eventually_all.2 hlarge).exists
  obtain ⟨⟨a, b⟩, hab⟩ := integral_eval_surjective Q p (fun v => ⟨_, hn v⟩)
  let q : ℚ_[p.val] := (p.val : ℚ_[p.val]) ^ n
  have hq : q ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)
  refine ⟨(q⁻¹ * a.val, q⁻¹ * b.val), funext fun v => ?_⟩
  have he := congrArg Subtype.val (congrFun hab v)
  change affineEval Q p a.val b.val v = (p.val : v.val.adicCompletion F) ^ n * x v at he
  have hq' : completedScalar p v q = (p.val : v.val.adicCompletion F) ^ n := by
    rw [map_pow, nat_scalar]
  rw [← hq'] at he
  change affineEval Q p (q⁻¹ * a.val) (q⁻¹ * b.val) v = x v
  have hm : affineEval Q p (q⁻¹ * a.val) (q⁻¹ * b.val) v =
      (completedScalar p v q)⁻¹ * affineEval Q p a.val b.val v := by
    simp only [affineEval, map_mul, map_inv₀]; ring
  have hne : completedScalar p v q ≠ 0 := by
    simpa only [map_zero] using (completedScalar p v).injective.ne hq
  rw [hm, he, inv_mul_cancel_left₀ hne]

/-- The affine evaluation is injective: an element in its kernel can
be scaled arbitrarily, whereas integral images force integral coefficients. -/
theorem eval_injective (Q : QuadraticBasis F d) (p : Prime) :
    Function.Injective (fun ab : ℚ_[p.val] × ℚ_[p.val] => affineEval Q p ab.1 ab.2) := by
  have hker (a b : ℚ_[p.val]) (h : affineEval Q p a b = 0) : a = 0 ∧ b = 0 := by
    have hscaled (r : ℚ_[p.val]) : ‖r * a‖ ≤ 1 ∧ ‖r * b‖ ≤ 1 := by
      apply (affineEval_mem_iff Q p _ _).mp
      intro v
      have he : affineEval Q p (r * a) (r * b) v =
          completedScalar p v r * affineEval Q p a b v := by simp only [affineEval, map_mul]; ring
      rw [he, h]
      change _ * (0 : v.val.adicCompletion F) ∈ _
      rw [mul_zero]
      exact zero_mem _
    have hnorm : 1 < ‖(p.val : ℚ_[p.val])⁻¹‖ := by
      rw [norm_inv, Padic.norm_p, inv_inv]
      exact_mod_cast p.prop.one_lt
    constructor
    · by_contra ha
      have hh := (hscaled ((p.val : ℚ_[p.val])⁻¹ * a⁻¹)).1
      rw [mul_assoc, inv_mul_cancel₀ ha, mul_one] at hh
      exact hnorm.not_ge hh
    · by_contra hb
      have hh := (hscaled ((p.val : ℚ_[p.val])⁻¹ * b⁻¹)).2
      rw [mul_assoc, inv_mul_cancel₀ hb, mul_one] at hh
      exact hnorm.not_ge hh
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have hz : affineEval Q p (a - a') (b - b') = 0 := by
    funext v
    have hv := congrFun h v
    change affineEval Q p a b v = affineEval Q p a' b' v at hv
    simp only [affineEval, map_sub] at hv ⊢
    change _ = (0 : v.val.adicCompletion F)
    linear_combination hv
  obtain ⟨ha, hb⟩ := hker _ _ hz
  exact Prod.ext (sub_eq_zero.mp ha) (sub_eq_zero.mp hb)

private def evalAt (Q : QuadraticBasis F d) (p : Prime) (v : PlacesAbove F p)
    {c : ℤ} (hc : d = 1 - 4 * c) :
    QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1 →+* v.val.adicCompletion F := by
  letI : Algebra ℚ_[p.val] (v.val.adicCompletion F) := (completedScalar p v).toAlgebra
  let a := algebraMap F (v.val.adicCompletion F) (generator Q)
  refine (QuadraticAlgebra.lift ⟨a, ?_⟩).toRingHom
  have hr := congrArg (algebraMap F (v.val.adicCompletion F)) (affine_relation Q hc)
  simp only [map_mul, map_add, map_neg, map_intCast] at hr
  change a * a = completedScalar p v (-(c : ℚ_[p.val])) * 1 + completedScalar p v 1 * a
  simpa only [map_neg, map_intCast, map_one, mul_one, one_mul] using hr

/-- The completed quadratic algebra decomposes into the actual completions
above the rational prime. Its integral locus is given by the two integral
affine coefficients, uniformly in the split, inert and ramified cases. -/
def completedQuadratic (Q : QuadraticBasis F d) (p : Prime) {c : ℤ}
    (hc : d = 1 - 4 * c) :
    QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1 ≃+* AdicProduct F p := by
  let f : QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1 →+* AdicProduct F p :=
    RingHom.pi (fun v => evalAt Q p v hc)
  have hf (a : QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1) :
      f a = affineEval Q p a.re a.im := by
    funext v
    change completedScalar p v a.re * 1 + completedScalar p v a.im * _ = _
    rw [mul_one]
    rfl
  have hinj : Function.Injective f := by
    intro a b h
    rw [hf, hf] at h
    let f₀ : ℚ_[p.val] × ℚ_[p.val] → AdicProduct F p := fun ab => affineEval Q p ab.1 ab.2
    have hh : f₀ (a.re, a.im) = f₀ (b.re, b.im) := h
    have hfun : Function.Injective f₀ := eval_injective Q p
    have he : (a.re, a.im) = (b.re, b.im) := hfun hh
    exact QuadraticAlgebra.ext (congrArg (fun x : ℚ_[p.val] × ℚ_[p.val] => x.1) he)
      (congrArg (fun x : ℚ_[p.val] × ℚ_[p.val] => x.2) he)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨⟨a, b⟩, hab⟩ := (eval_surjective Q p) x
    let z : QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1 := ⟨a, b⟩
    have hz : affineEval Q p z.re z.im = x := hab
    exact ⟨z, (hf z).trans hz⟩
  exact RingEquiv.ofBijective f ⟨hinj, hsurj⟩

theorem completedQuadratic_apply (Q : QuadraticBasis F d) (p : Prime) {c : ℤ}
    (hc : d = 1 - 4 * c) (x : QuadraticAlgebra ℚ_[p.val] (-(c : ℚ_[p.val])) 1) :
    completedQuadratic Q p hc x = affineEval Q p x.re x.im := by
  funext v
  change completedScalar p v x.re * 1 + completedScalar p v x.im * _ = _
  rw [mul_one]
  rfl

end ZInQ.Manuscript.RC.LocalTorus
