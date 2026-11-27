import ZInQKernel.Contrib.CloudB3E1RingClass.RadicandData

/-!
# Integral generators of the relation ideals

Manuscript `diophantine_zq.tex`, tex 3536–3542 and 3576–3579.

For a relation `m` (`∑_j m_j [𝔭_j] = 0` in `Cl(K)`), the integral ideal
`J_m = ∏_j 𝔭_j^{m_j⁺} 𝔭̄_j^{m_j⁻}` is principal, since `[𝔭̄_j] = −[𝔭_j]`. A generator
`β ∈ 𝒪_K` (`exists_integral_generator`) has
* `v_{𝔭_k}(β) = m_k⁺` and `v_{𝔭̄_k}(β) = m_k⁻` (`valuation_integral_generator_𝔭`, `…_𝔭bar`),
  with the chosen primes over pairwise distinct rational primes and `𝔭_k ≠ 𝔭̄_k`;
* `β ∉ 𝔯` for every prime `𝔯` over a rational prime other than the `p_j`
  (`not_mem_of_integral_generator`).

The integral form is the one the principal relations (`rel`) use, through the Picard class of
`J_m`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {S : ℕ}

/-- **The relation ideal** `J_m = ∏_j 𝔭_j^{m_j⁺} 𝔭̄_j^{m_j⁻}`. Kind: definition. -/
def relIdeal (C : RingClassSetup K S) (m : Fin S → ℤ) : Ideal (𝓞 K) :=
  ∏ j, (C.𝔭 j).asIdeal ^ (m j).toNat * (C.𝔭bar j).asIdeal ^ (-m j).toNat

/-- The relation ideal as a nonzero ideal. Kind: definition. -/
def relIdeal0 (C : RingClassSetup K S) (m : Fin S → ℤ) : (Ideal (𝓞 K))⁰ :=
  ∏ j, (⟨(C.𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot⟩ : (Ideal (𝓞 K))⁰) ^
      (m j).toNat *
    (⟨(C.𝔭bar j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭bar j).ne_bot⟩ : (Ideal (𝓞 K))⁰) ^
      (-m j).toNat

theorem coe_relIdeal0 (C : RingClassSetup K S) (m : Fin S → ℤ) :
    ((relIdeal0 C m : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = relIdeal C m := by
  simp [relIdeal0, relIdeal]

theorem zpow_toNat_mul_inv {G : Type*} [Group G] (c : G) (n : ℤ) :
    c ^ n.toNat * c⁻¹ ^ (-n).toNat = c ^ n := by
  rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add]
  congr 1
  omega

/-- **The relation ideal of a relation is principal, with an integral generator** (tex 3536–3542).
Kind: PROVED. -/
theorem exists_integral_generator (C : RingClassSetup K S) (m : Fin S → ℤ)
    (hm : ∑ j, m j • setupCls C j = 0) : ∃ β : 𝓞 K, relIdeal C m = Ideal.span {β} := by
  have hbar : ∀ j, ClassGroup.mk0
      (⟨(C.𝔭bar j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭bar j).ne_bot⟩ : (Ideal (𝓞 K))⁰) =
      (ClassGroup.mk0
        (⟨(C.𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot⟩ : (Ideal (𝓞 K))⁰))⁻¹ := by
    intro j
    rw [eq_inv_iff_mul_eq_one, ← map_mul, ClassGroup.mk0_eq_one_iff]
    change (((C.𝔭bar j).asIdeal * (C.𝔭 j).asIdeal : Ideal (𝓞 K))).IsPrincipal
    rw [mul_comm, C.𝔭_mul j]
    exact ⟨⟨_, rfl⟩⟩
  have hcl : ClassGroup.mk0 (relIdeal0 C m) = 1 := by
    have h1 : Additive.toMul (∑ j, m j • setupCls C j) = 1 := by rw [hm]; rfl
    rw [toMul_sum] at h1
    simp only [setupCls, toMul_zsmul, toMul_ofMul] at h1
    rw [← h1, relIdeal0, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, map_pow, hbar j, zpow_toNat_mul_inv]
  rw [ClassGroup.mk0_eq_one_iff, coe_relIdeal0] at hcl
  exact ⟨hcl.generator, (Ideal.span_singleton_generator _).symm⟩

/-! ### Valuations of the generator -/

open Classical in
/-- **The multiplicities of the relation ideal.** Kind: PROVED. -/
theorem count_relIdeal (C : RingClassSetup K S) (m : Fin S → ℤ) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w ((relIdeal C m : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ∑ j, ((if C.𝔭 j = w then ((m j).toNat : ℤ) else 0) +
        (if C.𝔭bar j = w then ((-m j).toNat : ℤ) else 0)) := by
  have hne : ∀ (P : HeightOneSpectrum (𝓞 K)) (e : ℕ),
      ((P.asIdeal ^ e : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := fun P e => by
    rw [FractionalIdeal.coeIdeal_pow]
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot)
  have hcount : ∀ (P : HeightOneSpectrum (𝓞 K)) (e : ℕ),
      FractionalIdeal.count K w ((P.asIdeal ^ e : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        if P = w then (e : ℤ) else 0 := fun P e => by
    rw [FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow]
    split_ifs with h
    · rw [h, FractionalIdeal.count_self, mul_one]
    · rw [FractionalIdeal.count_maximal_coprime K w h, mul_zero]
  have hprod : ((∏ j, (C.𝔭 j).asIdeal ^ (m j).toNat * (C.𝔭bar j).asIdeal ^ (-m j).toNat :
      Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ∏ j, (((C.𝔭 j).asIdeal ^ (m j).toNat * (C.𝔭bar j).asIdeal ^ (-m j).toNat : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) :=
    map_prod (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) _ _
  rw [relIdeal, hprod, FractionalIdeal.count_prod]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K w (hne _ _) (hne _ _), hcount,
      hcount]
  · intro j _
    rw [FractionalIdeal.coeIdeal_mul]
    exact mul_ne_zero (hne _ _) (hne _ _)

open Classical in
/-- **The valuations of an integral generator of the relation ideal.** Kind: PROVED. -/
theorem valuation_relGenerator (C : RingClassSetup K S) (m : Fin S → ℤ) (β : 𝓞 K)
    (hβ : relIdeal C m = Ideal.span {β}) (w : HeightOneSpectrum (𝓞 K)) :
    w.valuation K (algebraMap (𝓞 K) K β) = WithZero.exp (-∑ j,
      ((if C.𝔭 j = w then ((m j).toNat : ℤ) else 0) +
        (if C.𝔭bar j = w then ((-m j).toNat : ℤ) else 0))) := by
  have hβ0 : algebraMap (𝓞 K) K β ≠ 0 := by
    intro h
    have hb : β = 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h.trans (map_zero _).symm)
    have h0 : relIdeal C m = ⊥ := by rw [hβ, hb, Ideal.span_singleton_eq_bot.mpr rfl]
    have hne : ((relIdeal0 C m : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≠ 0 :=
      nonZeroDivisors.coe_ne_zero _
    exact hne ((coe_relIdeal0 C m).trans h0)
  let u : Kˣ := Units.mk0 _ hβ0
  have hu : (toPrincipalIdeal (𝓞 K) K u : FractionalIdeal (𝓞 K)⁰ K) =
      ((relIdeal C m : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [coe_toPrincipalIdeal, hβ, FractionalIdeal.coeIdeal_span_singleton]
    rfl
  have hc := FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation K w u
  rw [hu, count_relIdeal] at hc
  have hv0 : w.valuation K (u : K) ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact u.ne_zero
  change w.valuation K (u : K) = _
  rw [← WithZero.exp_log hv0, WithZero.exp_inj]
  linarith

variable {s : ZInQ.Contrib.ChebFD.C10.Qbar}
open ZInQ.Manuscript.RC.TateWiring

theorem 𝔭bar_injective (C : RingClassSetup (quadField s) S) (hinj : Function.Injective C.p) :
    Function.Injective C.𝔭bar := fun j k hjk => by
  by_contra h
  have hp : C.p j ≠ C.p k := fun h' => h (hinj h')
  exact (not_mem_of_ne C k (C.p j) (C.p_prime j) hp).2 (hjk ▸ (p_mem_𝔭 C j).2)

theorem 𝔭_ne_𝔭bar (C : RingClassSetup (quadField s) S) (hinj : Function.Injective C.p)
    (hne : ∀ j, C.𝔭 j ≠ C.𝔭bar j) (j k : Fin S) : C.𝔭 j ≠ C.𝔭bar k := fun h =>
  (𝔭_injective_and_bar C hinj hne).2 k ⟨j, h⟩

/-- At the chosen primes: `v_{𝔭_k}(β) = m_k⁺`, `v_{𝔭̄_k}(β) = m_k⁻`. Kind: PROVED. -/
theorem valuation_relGenerator_𝔭 (C : RingClassSetup (quadField s) S)
    (hinj : Function.Injective C.p) (hne : ∀ j, C.𝔭 j ≠ C.𝔭bar j) (m : Fin S → ℤ)
    (β : 𝓞 (quadField s)) (hβ : relIdeal C m = Ideal.span {β}) (k : Fin S) :
    (C.𝔭 k).valuation (quadField s) (algebraMap _ _ β) = WithZero.exp (-((m k).toNat : ℤ)) ∧
      (C.𝔭bar k).valuation (quadField s) (algebraMap _ _ β) =
        WithZero.exp (-((-m k).toNat : ℤ)) := by
  classical
  have hPinj := (𝔭_injective_and_bar C hinj hne).1
  have hQinj := 𝔭bar_injective C hinj
  constructor
  · rw [valuation_relGenerator C m β hβ]
    congr 2
    rw [Finset.sum_eq_single k]
    · have h1 : ¬ C.𝔭bar k = C.𝔭 k := fun h => 𝔭_ne_𝔭bar C hinj hne k k h.symm
      simp only [h1, ↓reduceIte, add_zero]
    · intro j _ hjk
      have h1 : ¬ C.𝔭 j = C.𝔭 k := fun h => hjk (hPinj h)
      have h2 : ¬ C.𝔭bar j = C.𝔭 k := fun h => 𝔭_ne_𝔭bar C hinj hne k j h.symm
      simp only [h1, h2, ↓reduceIte, add_zero]
    · exact fun h => absurd (Finset.mem_univ k) h
  · rw [valuation_relGenerator C m β hβ]
    congr 2
    rw [Finset.sum_eq_single k]
    · have h1 : ¬ C.𝔭 k = C.𝔭bar k := 𝔭_ne_𝔭bar C hinj hne k k
      simp only [h1, ↓reduceIte, zero_add]
    · intro j _ hjk
      have h1 : ¬ C.𝔭 j = C.𝔭bar k := 𝔭_ne_𝔭bar C hinj hne j k
      have h2 : ¬ C.𝔭bar j = C.𝔭bar k := fun h => hjk (hQinj h)
      simp only [h1, h2, ↓reduceIte, add_zero]
    · exact fun h => absurd (Finset.mem_univ k) h

/-- Away from the chosen rational primes the generator is a unit. Kind: PROVED. -/
theorem valuation_relGenerator_away (C : RingClassSetup (quadField s) S) (m : Fin S → ℤ)
    (β : 𝓞 (quadField s)) (hβ : relIdeal C m = Ideal.span {β}) {q : ℕ} (hq : q.Prime)
    (hqp : ∀ j, q ≠ C.p j) {w : HeightOneSpectrum (𝓞 (quadField s))}
    (hw : ((q : ℤ) : 𝓞 (quadField s)) ∈ w.asIdeal) :
    w.valuation (quadField s) (algebraMap _ _ β) = 1 := by
  classical
  have hw' : ((max q 1 : ℕ) : 𝓞 (quadField s)) ∈ w.asIdeal := by
    rw [max_eq_left hq.one_lt.le, ← Int.cast_natCast]; exact hw
  rw [valuation_relGenerator C m β hβ w, Finset.sum_eq_zero, neg_zero, WithZero.exp_zero]
  intro j _
  have h1 : ¬ C.𝔭 j = w := fun h => (not_mem_of_ne C j q hq (hqp j)).1 (h ▸ hw')
  have h2 : ¬ C.𝔭bar j = w := fun h => (not_mem_of_ne C j q hq (hqp j)).2 (h ▸ hw')
  simp only [h1, h2, ↓reduceIte, add_zero]

end ZInQ.Contrib.CloudB3E1RingClass
