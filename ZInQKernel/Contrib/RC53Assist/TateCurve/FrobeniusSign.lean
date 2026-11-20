import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalArithmetic

/-!
# Reading the quadratic sign at arithmetic Frobenius

An isomorphism whose scaling coefficient is fixed by Galois descends to the
base field: its other three coefficients are explicit functions of that
coefficient and the two equations. An unramified sign which is one at
Frobenius therefore gives a base-field isomorphism. The converse is obtained
by comparing with a base-field isomorphism.

References: Weierstrass transformation formulas; the fundamental theorem of
Galois theory; Serre, *Local Fields*, I, §8 and III, §5 for Frobenius generation.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open Module WeierstrassCurve WeierstrassCurve.Affine
open ZInQ.Contrib.RC53Assist.GlobalTrace
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open scoped Classical WithZero

section Descent

variable {K F : Type*} [Field K] [Field F] [CharZero K] [CharZero F] [Algebra K F]

/-- **PROVED**: the remaining isomorphism coefficients are determined by
its scaling coefficient and the two equations. Locator: the `b₂`, `a₁`,
and `a₃` transformation formulas. -/
theorem variableChange_scaling_formulas (E E' : WeierstrassCurve F)
    (C : VariableChange F) (hC : C • E = E') :
    ((C.u : F) ^ 2 * E'.b₂ = E.b₂ + 12 * C.r) ∧
    ((C.u : F) * E'.a₁ = E.a₁ + 2 * C.s) ∧
    ((C.u : F) ^ 3 * E'.a₃ = E.a₃ + C.r * E.a₁ + 2 * C.t) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← hC, variableChange_b₂, ← mul_assoc, ← mul_pow,
      Units.mul_inv, one_pow, one_mul]
  · rw [← hC, variableChange_a₁, ← mul_assoc, Units.mul_inv, one_mul]
  · rw [← hC, variableChange_a₃, ← mul_assoc, ← mul_pow,
      Units.mul_inv, one_pow, one_mul]

/-- **PROVED**: if the scaling coefficient descends, the entire
Weierstrass isomorphism descends. Locator: `variableChange_scaling_formulas`
and injectivity of the base-field embedding. -/
theorem base_isomorphism_of_scaling (E E' : WeierstrassCurve K)
    (C : VariableChange F) (hC : C • E.baseChange F = E'.baseChange F)
    (u : K) (hu : algebraMap K F u = (C.u : F)) :
    ∃ A : VariableChange K, A • E = E' := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact C.u.ne_zero hu.symm
  let r := (u ^ 2 * E'.b₂ - E.b₂) / 12
  let s := (u * E'.a₁ - E.a₁) / 2
  let t := (u ^ 3 * E'.a₃ - E.a₃ - r * E.a₁) / 2
  let A : VariableChange K := ⟨Units.mk0 u hu0, r, s, t⟩
  obtain ⟨hc2, hc1, hc3⟩ := variableChange_scaling_formulas
    (E.baseChange F) (E'.baseChange F) C hC
  simp only [WeierstrassCurve.baseChange, map_b₂, map_a₁, map_a₃] at hc2 hc1 hc3
  have hr : algebraMap K F r = C.r := by
    dsimp [r]
    rw [map_div₀, map_sub, map_mul, map_pow, map_ofNat, hu]
    field_simp
    linear_combination hc2
  have hs : algebraMap K F s = C.s := by
    dsimp [s]
    rw [map_div₀, map_sub, map_mul, map_ofNat, hu]
    field_simp
    linear_combination hc1
  have ht : algebraMap K F t = C.t := by
    dsimp only [t]
    rw [map_div₀, map_sub, map_sub, map_mul, map_pow, map_mul, map_ofNat, hu, hr]
    field_simp
    linear_combination hc3
  have hAC : A.baseChange F = C := by
    ext
    · exact hu
    · exact hr
    · exact hs
    · exact ht
  have hb : (A • E).baseChange F = E'.baseChange F := by
    change (A • E).map (algebraMap K F) = E'.map (algebraMap K F)
    rw [← map_variableChange]
    change A.baseChange F • E.baseChange F = E'.baseChange F
    rw [hAC]
    exact hC
  refine ⟨A, ?_⟩
  ext
  all_goals apply (algebraMap K F).injective
  · simpa only [WeierstrassCurve.baseChange, map_a₁] using congrArg a₁ hb
  · simpa only [WeierstrassCurve.baseChange, map_a₂] using congrArg a₂ hb
  · simpa only [WeierstrassCurve.baseChange, map_a₃] using congrArg a₃ hb
  · simpa only [WeierstrassCurve.baseChange, map_a₄] using congrArg a₄ hb
  · simpa only [WeierstrassCurve.baseChange, map_a₆] using congrArg a₆ hb

/-- **PROVED**: a Galois-fixed scaling coefficient gives a base-field
isomorphism, even for an infinite Galois extension.
Locator: `InfiniteGalois.mem_range_algebraMap_iff_fixed`. -/
theorem base_isomorphism_of_scaling_fixed [IsGalois K F]
    (E E' : WeierstrassCurve K) (C : VariableChange F)
    (hC : C • E.baseChange F = E'.baseChange F)
    (hfix : ∀ σ : F ≃ₐ[K] F, σ (C.u : F) = C.u) :
    ∃ A : VariableChange K, A • E = E' := by
  obtain ⟨u, hu⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (C.u : F)).mpr hfix
  exact base_isomorphism_of_scaling E E' C hC u hu

/-- **PROVED**: a base-field isomorphism makes the derived sign trivial.
Locator: the two coefficient alternatives and the fact that inversion is
already defined over the base field. -/
theorem sign_trivial_of_base_isomorphism (E E' : WeierstrassCurve K)
    (C : VariableChange F) (hC : C • E.baseChange F = E'.baseChange F)
    (h4 : (E.baseChange F).c₄ ≠ 0) (h6 : (E.baseChange F).c₆ ≠ 0)
    (A : VariableChange K) (hA : A • E = E') :
    ∀ σ : F ≃ₐ[K] F, galoisSign C σ = 1 := by
  have hAF : A.baseChange F • E.baseChange F = E'.baseChange F := by
    change A.map (algebraMap K F) • E.map (algebraMap K F) = E'.map (algebraMap K F)
    rw [map_variableChange, hA]
  have hfixed : ∀ σ : F ≃ₐ[K] F, σ (C.u : F) = C.u := by
    have hf : ∀ σ : F ≃ₐ[K] F, σ ((A.baseChange F).u : F) = (A.baseChange F).u :=
      fun σ => σ.commutes (A.u : K)
    rcases isomorphism_coefficient_alternatives (E.baseChange F) (E'.baseChange F)
      (A.baseChange F) C hAF hC h4 h6 with ⟨hu, _, _, _⟩ | ⟨hu, _, _, _⟩
    · intro σ
      rw [hu]
      exact hf σ
    · intro σ
      rw [hu, map_neg, hf]
  intro σ
  have hunit : Units.map σ.toAlgHom.toMonoidHom C.u = C.u := Units.ext (hfixed σ)
  simp only [galoisSign, hunit, ite_true]

end Descent

section Frobenius

/-- **PROVED FROM FROBENIUS GENERATION**: an unramified quadratic descent
sign has Frobenius value one exactly when the isomorphism descends, and
minus one otherwise. This is a field-theoretic reading, not supplied as a
Tate-module assertion.
Locator: `base_isomorphism_of_scaling_fixed` and the open stabilizer of the
scaling coefficient. -/
theorem frobenius_sign_of_unramified (hF : LocalFrobeniusGenerationPrint)
    (p : ℕ) (hp : p.Prime) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ)
    (hw : (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
      (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰))
    (σF : LocalGaloisQ p hp)
    (hσF : IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σF)
    (E E' : WeierstrassCurve ((primeIdealQ p hp).adicCompletion ℚ))
    (C : VariableChange (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))
    (hC : C • E.baseChange (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) =
      E'.baseChange (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))
    (h4 : (E.baseChange (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).c₄ ≠ 0)
    (h6 : (E.baseChange (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).c₆ ≠ 0)
    (hI : ∀ σ ∈ localInertia w, galoisSign C σ = 1) :
    galoisSign C σF = if ∃ A : VariableChange ((primeIdealQ p hp).adicCompletion ℚ),
      A • E = E' then 1 else -1 := by
  classical
  by_cases hbase : ∃ A : VariableChange ((primeIdealQ p hp).adicCompletion ℚ), A • E = E'
  · rw [ite_eq_left hbase]
    obtain ⟨A, hA⟩ := hbase
    exact sign_trivial_of_base_isomorphism E E' C hC h4 h6 A hA σF
  · rw [ite_eq_right hbase]
    rcases galoisSign_values C σF with hpos | hneg
    · let H := MulAction.stabilizer (LocalGaloisQ p hp)
        (C.u : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))
      have hopen : IsOpen (H : Set (LocalGaloisQ p hp)) :=
        stabilizer_isOpen_of_isIntegral (C.u : AlgebraicClosure
          ((primeIdealQ p hp).adicCompletion ℚ))
      have hin : localInertia w ≤ H := by
        intro σ hσ
        change σ (C.u : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) = C.u
        rw [galoisSign_scalar E E' C hC h4 h6 σ, hI σ hσ, Int.cast_one, one_mul]
      have hFmem : σF ∈ H := by
        change σF (C.u : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) = C.u
        rw [galoisSign_scalar E E' C hC h4 h6 σF, hpos, Int.cast_one, one_mul]
      have htop := hF p hp Γ w hw σF hσF H hopen hin hFmem
      have hfix : ∀ σ : LocalGaloisQ p hp,
          σ (C.u : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) = C.u := by
        intro σ
        have hmem : σ ∈ H := by rw [htop]; exact Subgroup.mem_top _
        exact hmem
      exact (hbase (base_isomorphism_of_scaling_fixed E E' C hC hfix)).elim
    · exact hneg

end Frobenius

end ZInQ.Contrib.RC53Assist.TateCurve
