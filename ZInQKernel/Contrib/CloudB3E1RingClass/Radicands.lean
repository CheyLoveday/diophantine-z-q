import ZInQKernel.Contrib.CloudB3E1RingClass.Assembly
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.Factorization

/-!
# Generators of principal relations among the chosen primes

Manuscript `diophantine_zq.tex`, tex 3536–3542: "`(β_a) = ∏_j 𝔭_j^{m_j^{(a)}}`, where the `m^{(a)}`
form a `ℤ`-basis of `𝓡`. The generators `β_a` may be fractional."

For a number field `K`, pairwise distinct primes `𝔭_j` and a relation `m` (`∑_j m_j [𝔭_j] = 0` in
`Cl(K)`), `exists_generator` gives `β ∈ K^×` with `(β) = ∏_j 𝔭_j^{m_j}` as fractional ideals. Hence
`v_{𝔭_j}(β) = m_j` and `v_w(β) = 0` at every other prime `w` (`valuation_generator`).

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- A prime of `𝒪_K` as a unit fractional ideal. Kind: definition. -/
def primeUnit (P : HeightOneSpectrum (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K ⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero P.ne_bot⟩

theorem coe_primeUnit (P : HeightOneSpectrum (𝓞 K)) :
    ((primeUnit P : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = P.asIdeal :=
  FractionalIdeal.coe_mk0 K _

/-- **A principal relation has a generator** (tex 3536–3542): if `∑_j m_j [𝔭_j] = 0` in
`Cl(K)`, then `∏_j 𝔭_j^{m_j} = (β)` for some `β ∈ K^×`. Kind: PROVED. -/
theorem exists_generator {S : ℕ} (P : Fin S → HeightOneSpectrum (𝓞 K)) (m : Fin S → ℤ)
    (hm : ∑ j, m j • Additive.ofMul
      (ClassGroup.mk0 ⟨(P j).asIdeal, mem_nonZeroDivisors_of_ne_zero (P j).ne_bot⟩) = 0) :
    ∃ β : Kˣ, toPrincipalIdeal (𝓞 K) K β = ∏ j, primeUnit (P j) ^ m j := by
  set I := ∏ j, primeUnit (P j) ^ m j
  have hI : ClassGroup.mk K I = 1 := by
    have h1 : Additive.toMul (∑ j, m j • Additive.ofMul
        (ClassGroup.mk0 ⟨(P j).asIdeal, mem_nonZeroDivisors_of_ne_zero (P j).ne_bot⟩)) = 1 := by
      rw [hm]; rfl
    rw [toMul_sum] at h1
    simp only [toMul_zsmul, toMul_ofMul] at h1
    rw [← h1, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, primeUnit, ClassGroup.mk_mk0]
  rw [ClassGroup.mk_eq_one_iff] at hI
  obtain ⟨β, hβ⟩ := hI
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have : ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = ⊥ := by
      rw [hβ, Submodule.span_singleton_eq_bot.mpr rfl]
    exact I.ne_zero (FractionalIdeal.coeToSubmodule_eq_bot.mp this)
  refine ⟨Units.mk0 β hβ0, Units.ext ?_⟩
  rw [coe_toPrincipalIdeal, Units.val_mk0]
  apply FractionalIdeal.coeToSubmodule_injective
  show ((FractionalIdeal.spanSingleton (𝓞 K)⁰ β : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
    ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  rw [FractionalIdeal.coe_spanSingleton, hβ]

open Classical in
/-- **The valuations of the generator** (tex 3540–3542): if `(β) = ∏_j 𝔭_j^{m_j}` with the `𝔭_j`
pairwise distinct, then `v_w(β) = ∑_{j : 𝔭_j = w} m_j` at every prime `w`, in Mathlib's
normalization `v_w(β) = exp(−·)`. Kind: PROVED. -/
theorem valuation_generator {S : ℕ} (P : Fin S → HeightOneSpectrum (𝓞 K)) (m : Fin S → ℤ)
    (β : Kˣ) (hβ : toPrincipalIdeal (𝓞 K) K β = ∏ j, primeUnit (P j) ^ m j)
    (w : HeightOneSpectrum (𝓞 K)) :
    w.valuation K (β : K) = WithZero.exp (-∑ j, if P j = w then m j else 0) := by
  have hc := FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation K w β
  rw [hβ, Units.coe_prod] at hc
  rw [FractionalIdeal.count_prod K w _ _ (fun j _ => by
      rw [Units.val_zpow_eq_zpow_val]
      exact zpow_ne_zero _ (Units.ne_zero _))] at hc
  have hsum : ∑ j, FractionalIdeal.count K w (((primeUnit (P j) ^ m j :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ)) : FractionalIdeal (𝓞 K)⁰ K) =
        ∑ j, if P j = w then m j else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Units.val_zpow_eq_zpow_val, coe_primeUnit, FractionalIdeal.count_zpow]
    split_ifs with h
    · rw [h, FractionalIdeal.count_self, mul_one]
    · rw [FractionalIdeal.count_maximal_coprime K w h, mul_zero]
  rw [hsum] at hc
  have hv0 : w.valuation K (β : K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact β.ne_zero
  rw [← WithZero.exp_log hv0, WithZero.exp_inj]
  linarith

/-- At a chosen prime (with the `𝔭_j` pairwise distinct), `v_{𝔭_k}(β) = m_k`; at any other prime,
`v_w(β) = 0`. Kind: PROVED. -/
theorem valuation_generator_of_injective {S : ℕ} {P : Fin S → HeightOneSpectrum (𝓞 K)}
    (hP : Function.Injective P) (m : Fin S → ℤ) (β : Kˣ)
    (hβ : toPrincipalIdeal (𝓞 K) K β = ∏ j, primeUnit (P j) ^ m j) :
    (∀ k, (P k).valuation K (β : K) = WithZero.exp (-m k)) ∧
      ∀ w, w ∉ Set.range P → w.valuation K (β : K) = 1 := by
  classical
  refine ⟨fun k => ?_, fun w hw => ?_⟩
  · rw [valuation_generator P m β hβ (P k)]
    congr 2
    rw [Finset.sum_eq_single k (fun j _ hj => ite_eq_right_iff.mpr (fun h => absurd (hP h) hj))
      (fun h => absurd (Finset.mem_univ k) h), ite_eq_left_iff.mpr (fun h => absurd rfl h)]
  · rw [valuation_generator P m β hβ w]
    have h0 : (∑ j, if P j = w then m j else 0) = (0 : ℤ) :=
      Finset.sum_eq_zero (fun j _ => ite_eq_right_iff.mpr (fun h => absurd ⟨j, h⟩ hw))
    rw [h0, neg_zero, WithZero.exp_zero]

end ZInQ.Contrib.CloudB3E1RingClass
