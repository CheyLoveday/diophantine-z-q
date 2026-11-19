import ZInQKernel.Contrib.CloudB3E2Norm.GenusSquare
import ZInQKernel.Contrib.CloudB3E2Norm.H20PiBridge

/-!
# Genus theory: `K(√q*)` lies in the ring class field of conductor `q`

Manuscript `diophantine_zq.tex`, tex 2683–2684, 2847–2855 (`χ_h` a character of `Δ_f`).

For `K` imaginary quadratic and `q` an odd prime, a square root `x` of `q* = (−1)^{(q−1)/2} q`
lies in Tau Ceti's ring class field `H_q` of `ℤ + q𝒪_K` (**`sqrt_qstar_mem_ringClassField`**,
PROVED). Proof (Bauer's argument): in the finite Galois extension `M = H_q(±x)` of `K`, let `σ`
fix `H_q`. By Chebotarev (Tau Ceti's natural-density theorem) `σ` is an arithmetic Frobenius at a
prime `Q` of `M` over a prime `𝔭` of `K` prime to `2q`. Its restriction to `H_q` is trivial, so
`𝔭` splits completely in `H_q`, and by the splitting law (Tau Ceti's
`ncard_primesOver_ringClassField_eq_finrank_iff`) `𝔭 = (a + q y)`. Then `q*` is a square modulo
`𝔭` (`GenusSquare.isSquare_qstar_residue`) and the Frobenius `σ` fixes `x`
(`GenusSquare.frob_sqrt_eq`). By Galois theory `x ∈ H_q`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.GenusRingClass

open NumberField Polynomial IsDedekindDomain
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Contrib.CloudB3E2.GenusSquare

variable {K : Type} [Field K] [NumberField K]

/-- `X² − c`. Kind: definition. -/
abbrev sqPoly (c : K) : K[X] := X ^ 2 - C c

/-- The splitting field of `X² − c` in `Kˢ`. Kind: definition. -/
abbrev sqField (c : K) : IntermediateField K (SeparableClosure K) :=
  IntermediateField.adjoin K ((sqPoly c).rootSet (SeparableClosure K))

omit [NumberField K] in
theorem splits_sqPoly {c : K} {x : SeparableClosure K} (hx : x ^ 2 = algebraMap K _ c) :
    ((sqPoly c).map (algebraMap K (SeparableClosure K))).Splits := by
  have : (sqPoly c).map (algebraMap K (SeparableClosure K)) = (X - C x) * (X - C (-x)) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ← hx, C_neg, sub_neg_eq_add]
    rw [C_pow]; ring
  rw [this]
  exact (Splits.X_sub_C x).mul (Splits.X_sub_C (-x))

instance (c : K) [h : Fact (∃ x : SeparableClosure K, x ^ 2 = algebraMap K _ c)] :
    Normal K (sqField c) :=
  have := IntermediateField.adjoin_rootSet_isSplittingField (splits_sqPoly h.out.choose_spec)
  Normal.of_isSplittingField (sqPoly c)

instance (c : K) : FiniteDimensional K (sqField c) :=
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem mem_sqField {c : K} {x : SeparableClosure K} (hx : x ^ 2 = algebraMap K _ c) :
    x ∈ sqField c := by
  refine IntermediateField.subset_adjoin K _ ?_
  rw [mem_rootSet]
  refine ⟨?_, ?_⟩
  · intro h0
    have := congrArg (Polynomial.coeff · 2) h0
    simp at this
  · simp [hx]

/-- **`K(√q*) ⊆ H_q`** (PROVED; genus theory for the order `ℤ + q𝒪_K`, by Bauer's argument with
Chebotarev and the splitting law). -/
theorem sqrt_qstar_mem_ringClassField (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    {q : ℕ} [Fact q.Prime] [NeZero q] (hq2 : q ≠ 2) {x : SeparableClosure K}
    (hx : x ^ 2 = algebraMap K _ ((qstar q : ℤ) : K)) :
    x ∈ ringClassField (conductorOrder K q) := by
  classical
  set c : K := ((qstar q : ℤ) : K)
  set O := conductorOrder K q
  set H := ringClassField O
  have : Fact (∃ y : SeparableClosure K, y ^ 2 = algebraMap K _ c) := ⟨⟨x, hx⟩⟩
  set M : IntermediateField K (SeparableClosure K) := H ⊔ sqField c
  have hHM : H ≤ M := le_sup_left
  have hxM : x ∈ M := le_sup_right (a := H) (mem_sqField hx)
  have : FiniteDimensional K M := IntermediateField.finiteDimensional_sup _ _
  have : Normal K M := IntermediateField.normal_sup K _ H (sqField c)
  have : IsGalois K M := IsGalois.mk
  have : NumberField M := NumberField.of_module_finite K M
  let _ : Algebra H M := (IntermediateField.inclusion hHM).toRingHom.toAlgebra
  have : IsScalarTower K H M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set x' : M := ⟨x, hxM⟩
  -- every automorphism of `M` fixing `H` fixes `x'`
  have key : ∀ σ : Gal(M/K), (∀ z : H, σ (algebraMap H M z) = algebraMap H M z) → σ x' = x' := by
    intro σ hσ
    -- a Frobenius prime for `σ` prime to `2q`
    have hinf : (Chebotarev.frobeniusPrimeSet K M (ConjClasses.mk σ)).Infinite := by
      refine (Chebotarev.hasNaturalDensity_frobeniusPrimeSet K M _).infinite ?_
      have h1 : Nat.card (ConjClasses.mk σ).carrier ≠ 0 :=
        Nat.card_ne_zero.2 ⟨⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩, inferInstance⟩
      have h2 : Nat.card Gal(M/K) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
      positivity
    have h2q0 : Ideal.span {((2 * q : ℕ) : 𝓞 K)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Nat.mul_ne_zero two_ne_zero (NeZero.ne q))
    obtain ⟨𝔭, h𝔭, h𝔭B⟩ := (hinf.sdiff (Ideal.finite_factors h2q0)).nonempty
    have h2q𝔭 : ((2 * q : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal := fun h =>
      h𝔭B (Ideal.dvd_span_singleton.2 h)
    have h2𝔭 : (2 : 𝓞 K) ∉ 𝔭.asIdeal := fun h =>
      h2q𝔭 (by push_cast; exact 𝔭.asIdeal.mul_mem_right _ h)
    have hq𝔭 : (q : 𝓞 K) ∉ 𝔭.asIdeal := fun h =>
      h2q𝔭 (by push_cast; exact 𝔭.asIdeal.mul_mem_left _ h)
    obtain ⟨⟨Q, hQp, hQl⟩, hQ⟩ := Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk h𝔭
    -- `𝔭` splits completely in `H`
    have hres : AlgEquiv.restrictNormalHom H σ = 1 := by
      refine AlgEquiv.ext fun z => (algebraMap H M).injective ?_
      change algebraMap H M ((σ.restrictNormal H) z) = algebraMap H M z
      rw [AlgEquiv.restrictNormal_commutes, hσ]
    have h𝔭H := Chebotarev.frobeniusPrimeSet_subset_map_restrictNormalHom (K := K) (L := M)
      (M := H) (ConjClasses.mk σ) h𝔭
    rw [ConjClasses.map_mk, hres, ← ConjClasses.one_eq_mk_one,
      Chebotarev.frobeniusPrimeSet_one_eq_setOf_ncard_primesOver_eq_finrank] at h𝔭H
    have hJ : 𝔭.asIdeal ∈ integralIdealsPrimeTo O.conductorModulus := by
      rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff_sup_eq_top]
      refine ⟨𝔭.ne_bot, ?_⟩
      rw [conductorModulus_finitePart]
      refine (𝔭.isMaximal.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hq𝔭 ?_))
      rw [h]
      exact Ideal.mem_sup_right (ZInQ.Contrib.CloudB3E2.NormCochain.natCast_mem_conductor q)
    have : (⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo O.conductorModulus).1.IsMaximal :=
      𝔭.isMaximal
    obtain ⟨β, hβO, hβ⟩ := (ncard_primesOver_ringClassField_eq_finrank_iff O
      ⟨𝔭.asIdeal, hJ⟩).1 h𝔭H
    rw [mem_toRingOfIntegers] at hβO
    obtain ⟨a, y, hay⟩ := hβO
    have hβay : β = (a : 𝓞 K) + (q : 𝓞 K) * y := by
      apply RingOfIntegers.ext
      rw [hay]; push_cast; rfl
    rw [hβay] at hβ
    have : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
    obtain ⟨t, ht⟩ := isSquare_qstar_residue hK2 hTC hq2 hβ hq𝔭 h2𝔭
    -- the Frobenius fixes `x'`
    have hx'2 : x' ^ 2 = ((qstar q : ℤ) : M) := by
      apply Subtype.ext
      rw [IntermediateField.coe_pow]
      change x ^ 2 = _
      rw [hx]
      simp [c]
    have hxint : IsIntegral ℤ x' := by
      refine IsIntegral.of_pow two_pos ?_
      rw [hx'2, ← eq_intCast (algebraMap ℤ M)]
      exact isIntegral_algebraMap
    set xO : 𝓞 M := ⟨x', hxint⟩
    have hxO : xO ^ 2 = algebraMap (𝓞 K) (𝓞 M) ((qstar q : ℤ) : 𝓞 K) := by
      rw [map_intCast]
      apply RingOfIntegers.ext
      rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_pow, map_intCast]
      exact hx'2
    have hQ𝔭 : 𝔭.asIdeal = Q.under (𝓞 K) := hQl.over
    have hmem : ∀ r : 𝓞 K, algebraMap (𝓞 K) (𝓞 M) r ∈ Q ↔ r ∈ 𝔭.asIdeal := fun r => by
      rw [hQ𝔭, Ideal.mem_comap]
    have := frob_sqrt_eq (φ := MulSemiringAction.toAlgHom (𝓞 K) (𝓞 M) σ) hQ hxO
      (c := ((qstar q : ℤ) : 𝓞 K)) (t := t)
      (by rw [← map_pow, ← map_sub, hmem]; exact ht)
      (by rw [← map_ofNat (algebraMap (𝓞 K) (𝓞 M)) 2, hmem]; exact h2𝔭)
      (by
        rw [hmem]
        intro h
        apply hq𝔭
        have : ((qstar q : ℤ) : 𝓞 K) = (-1) ^ (q / 2) * (q : 𝓞 K) := by simp [qstar]
        rw [this] at h
        rcases 𝔭.isPrime.mem_or_mem h with h' | h'
        · exact absurd (𝔭.isPrime.mem_of_pow_mem _ h') (fun h'' =>
            𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using 𝔭.asIdeal.neg_mem h'')))
        · exact h')
      (by
        rw [← sq_eq_sq_iff_eq_or_eq_neg, ← map_pow, hxO]
        exact AlgHom.commutes _ _)
    have := congrArg (fun z : 𝓞 M => ((z : M) : SeparableClosure K)) this
    exact Subtype.ext this
  -- Galois theory
  set H' : IntermediateField K M := IntermediateField.restrict hHM
  have hfix : x' ∈ IntermediateField.fixedField H'.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    refine key σ fun z => hσ _ ?_
    rw [IntermediateField.mem_restrict]
    exact z.2
  rw [IsGalois.fixedField_fixingSubgroup, IntermediateField.mem_restrict] at hfix
  exact hfix

end ZInQ.Contrib.CloudB3E2.GenusRingClass
