import ZInQKernel.Contrib.CloudB3RC53.Mattuck.Levels
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.LocalConditions

/-!
# Mattuck at `p = 2`, part 4: counting `[𝔪^{e+1} : 𝔪^{2e+1}] = 2^{[K_w : ℚ₂]}`

Manuscript `diophantine_zq.tex`, tex 4551–4556 (`d_w = [K_w : ℚ₂]` in the residual dimension
`2 + d_w` of the old Kummer condition).

For the completion `𝒪_v` of a Dedekind domain at a height-one prime `v`, with maximal ideal `𝔪`
and a uniformizer `ϖ` (`v(ϖ) = exp(−1)`):

* `relIndex_maximalIdeal_pow_succ`: `[𝔪^k : 𝔪^{k+1}] = |𝒪_v/𝔪|` (`r ↦ ϖ^k r` induces
  `𝒪_v/𝔪 ≅ 𝔪^k/𝔪^{k+1}`), hence `relIndex_maximalIdeal_pow_add`: `[𝔪^k : 𝔪^{k+n}] = |𝒪_v/𝔪|^n`;
* `mem_pow_succ_iff`, `mem_pow_two_mul_succ_iff`: if `v(2) = exp(−e)` then `𝔪^{e+1} = 2𝔪` and
  `𝔪^{2e+1} = 4𝔪` (the hypotheses of `card_modN_lev`).

For a number field `K` and a place `w | 2`, with `e = e(w|2)`, `f = f(w|2)`:

* `valued_two_eq`: `v_w(2) = exp(−e)` (Mathlib's `intValuation_liesOver`);
* `natCard_residue_eq`: `|𝒪_w/𝔪| = 2^f` (`absNorm_pow_inertiaDeg`);
* **`relIndex_two_level`**: `[𝔪^{e+1} : 𝔪^{2e+1}] = 2^{e f} = 2^{[K_w : ℚ₂]}` (`finrank_qp`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Mattuck

open IsDedekindDomain WithZero

section Generic

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] (v : HeightOneSpectrum R)

theorem exists_uniformizer :
    ∃ ϖ : v.adicCompletionIntegers F, Irreducible ϖ ∧
      Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) = exp (-1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  exact ⟨ϖ, hϖ, HeightOneSpectrum.valued_algebraMap_eq_exp_neg_one_of_irreducible v hϖ⟩

theorem valued_pow_uniformizer {ϖ : v.adicCompletionIntegers F}
    (hϖ : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) = exp (-1)) (k : ℕ) :
    Valued.v (((ϖ ^ k : v.adicCompletionIntegers F)) : v.adicCompletion F) =
      exp (-(k : ℤ)) := by
  push_cast
  rw [map_pow, hϖ, ← exp_nsmul]
  congr 1
  simp

/-- `r ↦ ϖ^k r mod 𝔪^{k+1}`. -/
def mulPowRed (ϖ : v.adicCompletionIntegers F) (k : ℕ) :
    v.adicCompletionIntegers F →+
      v.adicCompletionIntegers F ⧸
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ (k + 1) :=
  (Ideal.Quotient.mk _).toAddMonoidHom.comp (AddMonoidHom.mulLeft (ϖ ^ k))

theorem mulPowRed_ker {ϖ : v.adicCompletionIntegers F}
    (hϖ : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) = exp (-1)) (k : ℕ) :
    (mulPowRed v ϖ k).ker =
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup := by
  ext r
  rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup]
  change Ideal.Quotient.mk _ (ϖ ^ k * r) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, HeightOneSpectrum.mem_maximalIdeal_pow_iff,
    ← pow_one (IsLocalRing.maximalIdeal _), HeightOneSpectrum.mem_maximalIdeal_pow_iff]
  push_cast
  rw [map_mul, show Valued.v ((ϖ : v.adicCompletion F) ^ k) = exp (-(k : ℤ)) by
      rw [map_pow, hϖ, ← exp_nsmul]; congr 1; simp,
    show (-((k : ℤ) + 1)) = -(k : ℤ) + -1 by ring, exp_add]
  exact mul_le_mul_iff_right₀ (zero_lt_iff.mpr exp_ne_zero)

theorem mulPowRed_range {ϖ : v.adicCompletionIntegers F}
    (hϖ : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) = exp (-1)) (k : ℕ) :
    (mulPowRed v ϖ k).range = (idealRed (I := IsLocalRing.maximalIdeal _) k (k + 1)).range := by
  have hspan := HeightOneSpectrum.span_singleton_eq_maximalIdeal_pow (v := v) (K := F)
    (x := ϖ ^ k) (valued_pow_uniformizer v hϖ k)
  ext x
  simp only [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨⟨ϖ ^ k * r, ?_⟩, rfl⟩
    rw [← hspan]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rintro ⟨t, rfl⟩
    have ht : (t : v.adicCompletionIntegers F) ∈ Ideal.span {ϖ ^ k} := by rw [hspan]; exact t.2
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp ht
    refine ⟨r, ?_⟩
    change Ideal.Quotient.mk _ (ϖ ^ k * r) = Ideal.Quotient.mk _ (t : v.adicCompletionIntegers F)
    rw [mul_comm, hr]

/-- **`[𝔪^k : 𝔪^{k+1}] = |𝒪_v/𝔪|`.** PROVED. -/
theorem relIndex_maximalIdeal_pow_succ (k : ℕ) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ (k + 1)).toAddSubgroup.relIndex
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ k).toAddSubgroup =
      Nat.card (v.adicCompletionIntegers F ⧸
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) := by
  obtain ⟨ϖ, -, hϖ⟩ := exists_uniformizer v (F := F)
  rw [AddSubgroup.relIndex, ← idealRed_ker, AddSubgroup.index_ker, ← mulPowRed_range v hϖ k,
    ← AddSubgroup.index_ker, mulPowRed_ker v hϖ k]
  rfl

/-- **`[𝔪^k : 𝔪^{k+n}] = |𝒪_v/𝔪|^n`.** PROVED. -/
theorem relIndex_maximalIdeal_pow_add (k n : ℕ) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ (k + n)).toAddSubgroup.relIndex
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ k).toAddSubgroup =
      Nat.card (v.adicCompletionIntegers F ⧸
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _
      (show (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ (k + (n + 1))).toAddSubgroup ≤
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ (k + n)).toAddSubgroup from
        Ideal.pow_le_pow_right (by omega))
      (show (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ (k + n)).toAddSubgroup ≤
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ k).toAddSubgroup from
        Ideal.pow_le_pow_right (by omega)),
      show k + (n + 1) = (k + n) + 1 by omega, relIndex_maximalIdeal_pow_succ, ih, pow_succ,
      mul_comm]

variable {v}

/-- `𝔪^e = (2)` when `v(2) = exp(−e)`. -/
theorem span_two_eq {e : ℕ}
    (h2 : Valued.v ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = exp (-(e : ℤ))) :
    Ideal.span {(2 : v.adicCompletionIntegers F)} =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ e :=
  HeightOneSpectrum.span_singleton_eq_maximalIdeal_pow v h2

/-- **`𝔪^{e+1} = 2𝔪`** when `v(2) = exp(−e)`. -/
theorem mem_pow_succ_iff {e : ℕ}
    (h2 : Valued.v ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = exp (-(e : ℤ)))
    (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ (e + 1) ↔
      ∃ t ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F), x = 2 * t := by
  rw [pow_succ, ← span_two_eq h2, Ideal.mem_span_singleton_mul]
  exact ⟨fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩, fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩⟩

/-- **`𝔪^{2e+1} = 4𝔪`** when `v(2) = exp(−e)`. -/
theorem mem_pow_two_mul_succ_iff {e : ℕ}
    (h2 : Valued.v ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = exp (-(e : ℤ)))
    (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ (2 * e + 1) ↔
      ∃ σ ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F), x = 4 * σ := by
  have h4 : Ideal.span {(4 : v.adicCompletionIntegers F)} =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ (2 * e) := by
    rw [show (4 : v.adicCompletionIntegers F) = 2 * 2 by norm_num,
      ← Ideal.span_singleton_mul_span_singleton,
      span_two_eq h2, ← pow_add, two_mul]
  rw [pow_succ, ← h4, Ideal.mem_span_singleton_mul]
  exact ⟨fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩, fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩⟩

end Generic

section NumberField

open NumberField ZInQ.Contrib.CloudB3RC53.RankCounts

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [w.asIdeal.LiesOver (vP ⟨2, Nat.prime_two⟩).asIdeal]

/-- The prime `2` of `ℤ`. -/
abbrev two : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- **`v_w(2) = exp(−e(w|2))`.** PROVED. -/
theorem valued_two_eq :
    Valued.v ((2 : w.adicCompletionIntegers K) : w.adicCompletion K) =
      exp (-((w.asIdeal.ramificationIdx ℤ : ℕ) : ℤ)) := by
  have hv : (vP two).intValuation (2 : ℤ) = exp (-1) := by
    refine HeightOneSpectrum.intValuation_singleton _ two_ne_zero ?_
    rw [vP_asIdeal]
    rfl
  have h := HeightOneSpectrum.intValuation_liesOver (vP two) w (2 : ℤ)
  rw [hv, ← exp_nsmul] at h
  have hc : ((2 : w.adicCompletionIntegers K) : w.adicCompletion K) =
      ((algebraMap (𝓞 K) K 2 : K) : w.adicCompletion K) := by
    have h1 := congrFun (HeightOneSpectrum.algebraMap_adicCompletion (𝓞 K) K w (S := 𝓞 K)) 2
    rw [Function.comp_apply, map_ofNat] at h1
    rw [← h1]
    exact map_ofNat (w.adicCompletionIntegers K).subtype 2
  rw [hc, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap, show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 by simp,
    ← h]
  congr 1
  simp

/-- **`|𝒪_w/𝔪| = 2^{f(w|2)}`.** PROVED. -/
theorem natCard_residue_eq :
    Nat.card (w.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers K)) =
      2 ^ (w.asIdeal.inertiaDeg ℤ) := by
  rw [← Nat.card_congr (HeightOneSpectrum.residueFieldEquivAdicCompletionIntegers w).toEquiv]
  have hn : Nat.card (𝓞 K ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hn, ← Ideal.absNorm_pow_inertiaDeg (vP two).asIdeal w.asIdeal, vP_asIdeal,
    Ideal.absNorm_span_singleton]
  congr 1
  simp [Algebra.norm_self]

/-- **`[𝔪^{e+1} : 𝔪^{2e+1}] = 2^{[K_w : ℚ₂]}`** for `e = e(w|2)`. PROVED. -/
theorem relIndex_two_level :
    letI := qpAlg K two w
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers K) ^
        (2 * w.asIdeal.ramificationIdx ℤ + 1)).toAddSubgroup.relIndex
      (IsLocalRing.maximalIdeal (w.adicCompletionIntegers K) ^
        (w.asIdeal.ramificationIdx ℤ + 1)).toAddSubgroup =
      2 ^ Module.finrank ℚ_[2] (w.adicCompletion K) := by
  let := qpAlg K two w
  rw [show 2 * w.asIdeal.ramificationIdx ℤ + 1 =
      (w.asIdeal.ramificationIdx ℤ + 1) + w.asIdeal.ramificationIdx ℤ by omega,
    relIndex_maximalIdeal_pow_add, natCard_residue_eq, finrank_qp K two w, ← pow_mul, mul_comm]

end NumberField

end ZInQ.Contrib.CloudB3RC53.Mattuck
