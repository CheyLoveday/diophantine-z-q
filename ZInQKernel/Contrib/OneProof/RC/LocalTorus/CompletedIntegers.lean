import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Grouped
import ZInQKernel.Contrib.OneProof.RC.Adelic.Coordinates
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-! The scalar maps and simultaneous integral approximation used in the
completion of the quadratic torus (tex 9164–9165, on-the-spot (c)). -/

noncomputable section

open scoped NumberField

namespace ZInQ.Manuscript.RC.LocalTorus

open Eichler Adelic PicardFibers IsDedekindDomain HeightOneSpectrum
open UniformSpace.Completion WithZero Filter Rat.HeightOneSpectrum
open scoped Function
open scoped Topology

variable {F : Type*} [Field F] [NumberField F]

local instance (q : Nat.Primes) : Fact q.val.Prime := ⟨q.property⟩

abbrev PlacesAbove (F : Type*) [Field F] [NumberField F] (p : Prime) :=
  {v : HeightOneSpectrum (𝓞 F) // rationalPrimeEquiv.symm (rationalPrimeUnder F v) = p}

private theorem under_eq (p : Prime) (v : PlacesAbove F p) :
    rationalPrimeUnder F v.val = rationalPrimeEquiv p := by
  have hv : rationalPrimeEquiv.symm (rationalPrimeUnder F v.val) = p := v.property
  simpa using congrArg rationalPrimeEquiv hv

instance liesOver (p : Prime) (v : PlacesAbove F p) :
    v.val.asIdeal.LiesOver (rationalPrimeEquiv p).asIdeal := by
  constructor
  exact (congrArg HeightOneSpectrum.asIdeal (under_eq p v)).symm

instance finitePlacesAbove (p : Prime) : Finite (PlacesAbove F p) := by
  apply Set.Finite.to_subtype
  exact (rationalPrimeUnder_finite F (rationalPrimeEquiv p)).subset (fun v hv => under_eq p ⟨v, hv⟩)

/-- Divisibility by the rational prime can be checked over that prime
alone: the other prime ideals occur to exponent zero in its factorization. -/
theorem dvd_of_local_valuation (p : Prime) (a : 𝓞 F)
    (h : ∀ v : PlacesAbove F p, v.val.intValuation a ≤ v.val.intValuation (p.val : 𝓞 F)) :
    (p.val : 𝓞 F) ∣ a := by
  let q : 𝓞 F := p.val
  have hq : q ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  let I : Ideal (𝓞 F) := Ideal.span {q}
  have hI : I ≠ ⊥ := by simpa [I, Ideal.span_singleton_eq_bot] using hq
  apply Ideal.mem_span_singleton.mp
  change a ∈ I
  rw [← Ideal.iInf_maxPowDividing_eq hI, Submodule.mem_iInf]
  intro v
  rw [v.maxPowDividing_eq_pow_multiplicity hI, ← v.intValuation_le_pow_iff_mem,
    ← v.intValuation_eq_exp_neg_multiplicity hq]
  by_cases hv : rationalPrimeEquiv.symm (rationalPrimeUnder F v) = p
  · exact h ⟨v, hv⟩
  · have hnot : q ∉ v.asIdeal := by
      intro ha
      have he : (rationalPrimeEquiv p).asIdeal ≤ (rationalPrimeUnder F v).asIdeal := by
        apply Ideal.span_le.mpr
        intro t ht
        obtain rfl := Set.mem_singleton_iff.mp ht
        change algebraMap ℤ (𝓞 F) (p.val : ℤ) ∈ v.asIdeal
        simpa only [map_natCast] using ha
      have heq := (rationalPrimeEquiv p).isMaximal.eq_of_le
        (rationalPrimeUnder F v).isPrime.ne_top he
      exact hv (rationalPrimeEquiv.symm_apply_eq.mpr (HeightOneSpectrum.ext_iff.mpr heq.symm))
    rw [(v.intValuation_eq_one_iff_mem_primeCompl q).mpr hnot]
    exact v.intValuation_le_one a

theorem valuation_prime_lt_one (p : Prime) (v : PlacesAbove F p) :
    Valued.v (p.val : v.val.adicCompletion F) < 1 := by
  have h : (p.val : ℤ) ∈ (rationalPrimeEquiv p).asIdeal := Ideal.subset_span (by simp)
  have hp : (p.val : 𝓞 F) ∈ v.val.asIdeal := by
    simpa only [map_natCast] using
      (Ideal.mem_of_liesOver v.val.asIdeal (rationalPrimeEquiv p).asIdeal _).mp h
  have he := (v.val.intValuation_lt_one_iff_mem (p.val : 𝓞 F)).mpr hp
  have hh := valuedAdicCompletion_eq_valuation (K := F) v.val (p.val : 𝓞 F)
  rw [valuation_of_algebraMap] at hh
  rw [← hh] at he
  simpa only [map_natCast] using he

private def completionMap (p : Prime) (v : PlacesAbove F p) :
    (rationalPrimeEquiv p).adicCompletion ℚ →+* v.val.adicCompletion F :=
  let q := rationalPrimeEquiv p
  let f : WithVal (q.valuation ℚ) →+* WithVal (v.val.valuation F) := algebraMap _ _
  (adicCompletion.equiv F v.val).symm.toRingHom.comp
    ((mapRingHom f (uniformContinuous_algebraMap_liesOver ℚ F q v.val).continuous).comp
      (adicCompletion.equiv ℚ q).toRingHom)

private theorem primesEquiv_eq (p : Prime) :
    primesEquiv (rationalPrimeEquiv p) = p := by
  apply Subtype.ext
  change natGenerator (rationalPrimeEquiv p) = p.val
  have he := span_natGenerator (rationalPrimeEquiv p)
  have hr : (Rat.IsIntegralClosure.intEquiv ℤ).toRingHom = RingHom.id ℤ := Subsingleton.elim _ _
  change Ideal.span {((natGenerator (rationalPrimeEquiv p)) : ℤ)} =
    Ideal.map (Rat.IsIntegralClosure.intEquiv ℤ).toRingHom (rationalPrimeEquiv p).asIdeal at he
  rw [hr, Ideal.map_id] at he
  have ha := Ideal.span_singleton_eq_span_singleton.mp he
  simpa using Int.associated_iff_natAbs.mp ha

private def padicCast (q r : Prime) (h : q = r) : ℚ_[q.val] ≃+* ℚ_[r.val] := by
  subst r
  exact RingEquiv.refl _

/-- Extension of the rational diagonal to the completed scalars at a place. -/
def completedScalar (p : Prime) (v : PlacesAbove F p) :
    ℚ_[p.val] →+* v.val.adicCompletion F :=
  (completionMap p v).comp
    ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPrimeEquiv p)).symm.toRingHom.comp
      (padicCast p _ (primesEquiv_eq p).symm).toRingHom)

theorem completedScalar_ratCast (p : Prime) (v : PlacesAbove F p) (q : ℚ) :
    completedScalar p v (q : ℚ_[p.val]) = algebraMap F (v.val.adicCompletion F) (q : F) := by
  rw [map_ratCast, map_ratCast]

theorem continuous_completedScalar (p : Prime) (v : PlacesAbove F p) :
    Continuous (completedScalar p v) := by
  have cast_continuous (q r : Prime) (h : q = r) :
      Continuous (padicCast q r h) := by
    cases h
    exact continuous_id
  have hcast := cast_continuous p (primesEquiv (rationalPrimeEquiv p)) (primesEquiv_eq p).symm
  exact (adicCompletion.continuous_ofCompletion F v.val).comp
    (continuous_map.comp ((adicCompletion.continuous_toCompletion ℚ (rationalPrimeEquiv p)).comp
      ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv (rationalPrimeEquiv p)).symm.continuous.comp hcast)))

theorem completedScalar_mem (p : Prime) (v : PlacesAbove F p) (x : ℤ_[p.val]) :
    completedScalar p v (x : ℚ_[p.val]) ∈ v.val.adicCompletionIntegers F := by
  refine PadicInt.denseRange_intCast.induction_on x ?_ ?_
  · exact (Valued.isClosed_valuationSubring (v.val.adicCompletion F) (Γ₀ := ℤᵐ⁰)).preimage
      ((continuous_completedScalar p v).comp continuous_subtype_val)
  · intro n
    change completedScalar p v (n : ℚ_[p.val]) ∈ _
    rw [map_intCast]
    exact intCast_mem (v.val.adicCompletionIntegers F).toSubring n

/-- The integer ring is dense in the product of the completed integer rings
above one prime, by simultaneous approximation modulo prime powers. -/
theorem denseRange_diagonal_integers (p : Prime) :
    DenseRange (fun a : 𝓞 F => fun v : PlacesAbove F p =>
      (algebraMap (𝓞 F) (v.val.adicCompletionIntegers F) a)) := by
  classical
  let I (v : PlacesAbove F p) := v.val.asIdeal
  have ham (v : PlacesAbove F p) (a : 𝓞 F) :
      Valued.v (algebraMap (𝓞 F) (v.val.adicCompletion F) a) = v.val.intValuation a := by
    exact (valuedAdicCompletion_eq_valuation (K := F) v.val a).trans
      (v.val.valuation_of_algebraMap a)
  have near (v : PlacesAbove F p) (x : v.val.adicCompletion F)
      (hx : Valued.v x ≤ 1) (γ : (ℤᵐ⁰)ˣ) (hγ : γ.val ≤ 1) :
      ∃ a : 𝓞 F, Valued.v (algebraMap (𝓞 F) (v.val.adicCompletion F) a - x) < γ.val := by
    let f := algebraMap F (v.val.adicCompletion F)
    have hs : {z | Valued.v (z - x) < γ.val} ∈ 𝓝 x := by
      rw [Valued.mem_nhds]
      let E := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt
        (Valued.v : Valuation (v.val.adicCompletion F) ℤᵐ⁰)
      refine ⟨Units.map E.symm.toMonoidHom γ, ?_⟩
      intro z hz
      have hE (a : v.val.adicCompletion F) :
          E ((Valued.v : Valuation _ ℤᵐ⁰).restrict a) = Valued.v a :=
        Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
          (valuedAdicCompletion_surjective (K := F) (v := v.val)) a
      change Valued.v (z - x) < γ.val
      rw [← hE (z - x), ← E.apply_symm_apply γ.val]
      exact E.strictMono hz
    obtain ⟨y, hy⟩ := (v.val.denseRange_algebraMap F).mem_nhds hs
    have hy' : Valued.v (f y - x) < γ.val := hy
    have hy0 : v.val.valuation F y ≤ 1 := by
      rw [← valuedAdicCompletion_eq_valuation' v.val y]
      change Valued.v (f y) ≤ 1
      calc
        Valued.v (f y) = Valued.v ((f y - x) + x) := by rw [sub_add_cancel]
        _ ≤ 1 := (Valuation.map_add Valued.v _ _).trans (max_le (hy'.le.trans hγ) hx)
    obtain ⟨a, ha⟩ := v.val.exists_valuation_sub_lt_of_integer hy0 γ
    refine ⟨a, ?_⟩
    have ha' : Valued.v (algebraMap (𝓞 F) (v.val.adicCompletion F) a - f y) < γ.val := by
      rw [IsScalarTower.algebraMap_apply _ F, ← map_sub]
      exact (valuedAdicCompletion_eq_valuation' v.val _).trans_lt ha
    rw [← sub_add_sub_cancel _ (f y)]
    exact (Valuation.map_add Valued.v _ _).trans_lt (max_lt ha' hy')
  -- A product neighborhood contains a product of valuation balls.
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [nhds_pi] at hU
  obtain ⟨_, W, hW, hWU⟩ := Filter.mem_pi'.mp hU
  -- For each coordinate choose a congruence class contained in its ball.
  have choose_class (v : PlacesAbove F p) :
      ∃ n : ℕ, ∃ a : 𝓞 F,
        ∀ b : 𝓞 F, b - a ∈ I v ^ n →
          algebraMap (𝓞 F) (v.val.adicCompletionIntegers F) b ∈ W v := by
    have hw := hW v
    rw [nhds_subtype_eq_comap] at hw
    obtain ⟨S, hS, hSW⟩ := Filter.mem_comap.mp hw
    obtain ⟨r, hr⟩ := Valued.mem_nhds.mp hS
    let E := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt
      (Valued.v : Valuation (v.val.adicCompletion F) ℤᵐ⁰)
    have hE0 : E 0 = 0 := E.toOrderIso.map_bot
    have hEr : E r.val ≠ 0 := fun h => r.ne_zero (E.injective (h.trans hE0.symm))
    obtain ⟨n, hn⟩ := exists_exp_neg_natCast_lt_and_lt hEr
      (show (1 : ℤᵐ⁰) ≠ 0 from one_ne_zero)
    let γ : (ℤᵐ⁰)ˣ := Units.mk0 _ (by simp : WithZero.exp (-(n : ℤ)) ≠ 0)
    obtain ⟨a, ha⟩ := near v (x v).val (x v).prop γ hn.2.le
    refine ⟨n, a, fun b hb => hSW (hr ?_)⟩
    have hb' : Valued.v (algebraMap (𝓞 F) (v.val.adicCompletion F) b -
        algebraMap (𝓞 F) (v.val.adicCompletion F) a) ≤ γ.val := by
      rw [← map_sub, ham]
      exact (v.val.intValuation_le_pow_iff_mem _ _).mpr hb
    have hba : Valued.v (algebraMap (𝓞 F) (v.val.adicCompletion F) b - (x v).val) ≤ γ.val := by
      rw [← sub_add_sub_cancel _ (algebraMap (𝓞 F) (v.val.adicCompletion F) a)]
      exact (Valuation.map_add Valued.v _ _).trans (max_le hb' ha.le)
    apply E.strictMono.lt_iff_lt.mp
    rw [Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (valuedAdicCompletion_surjective (K := F) (v := v.val))]
    exact hba.trans_lt hn.1
  choose n a ha using choose_class
  let := Fintype.ofFinite (PlacesAbove F p)
  have hcop : Pairwise (IsCoprime on fun v => I v ^ n v) := by
    intro v w hvw
    exact (Ideal.isCoprime_of_isMaximal (I := I v) (J := I w) (fun he =>
      hvw (Subtype.ext (HeightOneSpectrum.ext_iff.mpr he)))).pow
  obtain ⟨b, hb⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun v => Ideal.Quotient.mk _ (a v))
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨_, hWU ?_, ⟨b, rfl⟩⟩
  exact fun v _ => ha v b (Ideal.Quotient.eq.mp (congrFun hb v))

end ZInQ.Manuscript.RC.LocalTorus
