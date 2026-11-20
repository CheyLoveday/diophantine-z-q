import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import Mathlib.RingTheory.ClassGroup.Basic

/-! The finite idele description of the ideal class group (tex 9165–9166).
The valuation and quotient constructions are on-the-spot (c). -/

noncomputable section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace ZInQ.Manuscript.RC.PicardFibers

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The exponent of the prime ideal in the ideal of an idele. Mathlib's
valuation is multiplicative, so its logarithm has the opposite sign. -/
def ideleExponent (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) : ℤ :=
  -WithZero.log (Valued.v (a.val v))

private theorem ideleVal_ne_zero (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    Valued.v (a.val v) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr ((FiniteAdeleRing.isUnit_iff.mp a.isUnit).1 v)

theorem ideleExponent_eq_zero_iff (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    ideleExponent a v = 0 ↔ Valued.v (a.val v) = 1 := by
  unfold ideleExponent
  rw [neg_eq_zero]
  constructor
  · intro h
    rw [← WithZero.exp_log (ideleVal_ne_zero a v), h, WithZero.exp_zero]
  · simp +contextual

theorem ideleExponent_mul (a b : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    ideleExponent (a * b) v = ideleExponent a v + ideleExponent b v := by
  change -WithZero.log (Valued.v (a.val v * b.val v)) = _
  rw [map_mul, WithZero.log_mul (ideleVal_ne_zero a v) (ideleVal_ne_zero b v)]
  exact neg_add _ _

theorem ideleExponent_cofinite (a : (FiniteAdeleRing R K)ˣ) :
    ∀ᶠ v in Filter.cofinite, ideleExponent a v = 0 :=
  (FiniteAdeleRing.unitsEquiv_finite_valued_eq_one a).mono fun v h =>
    (ideleExponent_eq_zero_iff a v).mpr h

private theorem fractionalIdeal_eq_of_counts {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I.val =
      FractionalIdeal.count K v J.val) : I = J := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K J.ne_zero]
  exact finprod_congr fun v => by rw [h v]

private def idealOfIdele (a : (FiniteAdeleRing R K)ˣ) :
    (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ ideleExponent a v)
    (finprod_ne_zero fun v => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))

private theorem count_idealOfIdele (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v (idealOfIdele a).val = ideleExponent a v :=
  FractionalIdeal.count_finprod K v _ (ideleExponent_cofinite a)

/-- Send a finite idele to the product of the prime ideal powers given by
its local exponents. -/
def ideleToIdeal : (FiniteAdeleRing R K)ˣ →* (FractionalIdeal R⁰ K)ˣ where
  toFun := idealOfIdele
  map_one' := fractionalIdeal_eq_of_counts fun v => by
    rw [count_idealOfIdele, Units.val_one, FractionalIdeal.count_one, ideleExponent_eq_zero_iff]
    exact map_one _
  map_mul' a b := fractionalIdeal_eq_of_counts fun v => by
    rw [Units.val_mul, FractionalIdeal.count_mul K v (idealOfIdele a).ne_zero
      (idealOfIdele b).ne_zero, count_idealOfIdele, count_idealOfIdele, count_idealOfIdele,
      ideleExponent_mul]

theorem count_ideleToIdeal (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v (ideleToIdeal a).val = ideleExponent a v :=
  count_idealOfIdele a v

theorem mem_ker_ideleToIdeal (a : (FiniteAdeleRing R K)ˣ) :
    a ∈ (ideleToIdeal (R := R) (K := K)).ker ↔ ∀ v : HeightOneSpectrum R,
      Valued.v (a.val v) = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h v
    apply (ideleExponent_eq_zero_iff a v).mp
    rw [← count_ideleToIdeal, h, Units.val_one, FractionalIdeal.count_one]
  · intro h
    apply fractionalIdeal_eq_of_counts
    intro v
    rw [count_ideleToIdeal, Units.val_one, FractionalIdeal.count_one]
    exact (ideleExponent_eq_zero_iff a v).mpr (h v)

open scoped RestrictedProduct in
/-- Every nonzero fractional ideal is the ideal of a finite idele. -/
theorem ideleToIdeal_surjective :
    Function.Surjective (ideleToIdeal (R := R) (K := K)) := by
  intro I
  let e (v : HeightOneSpectrum R) := FractionalIdeal.count K v I.val
  have hex (v : HeightOneSpectrum R) :
      ∃ x : (v.adicCompletion K)ˣ, Valued.v (x : v.adicCompletion K) = WithZero.exp (-e v) := by
    obtain ⟨k, hk⟩ := v.valuation_surjective K (WithZero.exp (-e v))
    have he : Valued.v (k : v.adicCompletion K) = WithZero.exp (-e v) :=
      (v.valuedAdicCompletion_eq_valuation' k).trans hk
    exact ⟨Units.mk0 _ ((Valuation.ne_zero_iff _).mp (he.trans_ne WithZero.coe_ne_zero)), he⟩
  choose x hx using hex
  have hgood : ∀ᶠ v in Filter.cofinite,
      x v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
    filter_upwards [FractionalIdeal.finite_factors I.val] with v hv
    apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    rw [hx, show e v = 0 from hv, neg_zero, WithZero.exp_zero]
  let a : (FiniteAdeleRing R K)ˣ := RestrictedProduct.mkUnit x hgood
  refine ⟨a, fractionalIdeal_eq_of_counts fun v => ?_⟩
  rw [count_ideleToIdeal]
  change -WithZero.log (Valued.v (x v : v.adicCompletion K)) = e v
  rw [hx, WithZero.log_exp, neg_neg]

private theorem intValuation_eq_count (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    v.intValuation r = WithZero.exp
      (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K r))) := by
  classical
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v
    (show Ideal.span ({r} : Set R) ≠ 0 from
      fun h => hr (Ideal.span_singleton_eq_bot.mp h)), v.intValuation_if_neg hr]

/-- The diagonal idele of a field unit maps to the same principal ideal. -/
theorem ideleToIdeal_diagonal (k : Kˣ) :
    ideleToIdeal (FiniteAdeleRing.unitEmbedding R K k) = toPrincipalIdeal R K k := by
  apply fractionalIdeal_eq_of_counts
  intro v
  rw [count_ideleToIdeal, coe_toPrincipalIdeal]
  change -WithZero.log (Valued.v ((k : K) : v.adicCompletion K)) = _
  rw [v.valuedAdicCompletion_eq_valuation']
  obtain ⟨r, s, hs, he⟩ := IsFractionRing.div_surjective R (k : K)
  have hr : r ≠ 0 := by
    rintro rfl
    exact k.ne_zero (by simpa using he.symm)
  have hs₀ := nonZeroDivisors.ne_zero hs
  have hs' : algebraMap R K s ≠ 0 := fun h =>
    hs₀ ((IsFractionRing.injective R K) (h.trans (map_zero _).symm))
  rw [← he, map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap,
    intValuation_eq_count (K := K) v hr, intValuation_eq_count (K := K) v hs₀,
    WithZero.log_div (by exact WithZero.coe_ne_zero) (by exact WithZero.coe_ne_zero), WithZero.log_exp,
    WithZero.log_exp, div_eq_mul_inv, map_mul, map_inv₀ (FractionalIdeal.spanSingleton R⁰ : K →*₀ FractionalIdeal R⁰ K)]
  rw [FractionalIdeal.count_mul K v, FractionalIdeal.count_inv]
  · ring
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (fun h => hr ((IsFractionRing.injective R K) (h.trans (map_zero _).symm)))
  · exact inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hs')

/-- The classes of finite ideles modulo the diagonal field units and
everywhere integral unit ideles. -/
def ideleClassSubgroup (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] : Subgroup (FiniteAdeleRing R K)ˣ :=
  (FiniteAdeleRing.unitEmbedding R K).range ⊔ (ideleToIdeal (R := R) (K := K)).ker

/-- The valuation map with its principal ambiguity removed. -/
def ideleClassMap : (FiniteAdeleRing R K)ˣ →* ClassGroup R :=
  (ClassGroup.equiv (R := R) K).symm.toMonoidHom.comp
    ((QuotientGroup.mk' (toPrincipalIdeal R K).range).comp ideleToIdeal)

theorem ideleClassMap_surjective :
    Function.Surjective (ideleClassMap (R := R) (K := K)) :=
  (ClassGroup.equiv (R := R) K).symm.surjective.comp
    (QuotientGroup.mk'_surjective _ |>.comp ideleToIdeal_surjective)

theorem ker_ideleClassMap : (ideleClassMap (R := R) (K := K)).ker = ideleClassSubgroup R K := by
  ext a
  rw [MonoidHom.mem_ker, ideleClassSubgroup, Subgroup.mem_sup]
  change (ClassGroup.equiv (R := R) K).symm (QuotientGroup.mk' _ (ideleToIdeal a)) = 1 ↔ _
  rw [← (ClassGroup.equiv (R := R) K).symm.map_one,
    (ClassGroup.equiv (R := R) K).symm.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨FiniteAdeleRing.unitEmbedding R K k, ⟨k, rfl⟩,
      (FiniteAdeleRing.unitEmbedding R K k)⁻¹ * a, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, ideleToIdeal_diagonal, hk, inv_mul_cancel]
  · rintro ⟨_, ⟨k, rfl⟩, b, hb, rfl⟩
    rw [MonoidHom.mem_ker] at hb
    rw [map_mul, ideleToIdeal_diagonal, hb, mul_one]
    exact ⟨k, rfl⟩

/-- Tex 9165–9166: the finite idele quotient by diagonal and integral
units is the ideal class group. -/
def ideleClassEquiv : (FiniteAdeleRing R K)ˣ ⧸ ideleClassSubgroup R K ≃* ClassGroup R :=
  (QuotientGroup.congr _ _ (MulEquiv.refl _)
    (by simpa using (ker_ideleClassMap (R := R) (K := K)).symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ ideleClassMap_surjective)

end ZInQ.Manuscript.RC.PicardFibers
