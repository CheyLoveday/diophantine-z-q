import ZInQKernel.Contrib.CloudB3E2Norm.H20DictFields

/-!
# Monotonicity of ring class fields in the order

Manuscript `diophantine_zq.tex`, tex 2914–2936 (`H_d ⊆ H_{dℓ}`; Cox, *Primes of the form
`x² + ny²`*, §9).

* **`ringClassField_mono`** (PROVED): for orders `O ⊆ O'` of a number field, the ring class field
  of `O'` lies in that of `O` (Tau Ceti's global class-field correspondence reverses inclusions,
  and the kernel of the ring-class quotient of `O` lies in that of `O'`: the conductor of `O'`
  divides that of `O`, ray classes are compatible with the transition map, and a generator in `O`
  is a generator in `O'`).
* `conductorOrder_mul_le` (PROVED): `ℤ + dq𝒪_K ⊆ ℤ + d𝒪_K`; **`ringClassField_le_mul`**
  (PROVED): `H_d ⊆ H_{dq}`.
* **`heegnerField_le_mul`** (PROVED, from the full anchor): `D.H d ⊆ D.H (dq)` at admissible
  `(d, q)`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53.CST

variable {K : Type} [Field K] [NumberField K]

/-- **Ring class fields shrink as the order grows** (PROVED; Cox §9): `O ⊆ O'` gives
`H_{O'} ⊆ H_O`. -/
theorem ringClassField_mono {O O' : NumberFieldOrder K} (h : O.toSubalgebra ≤ O'.toSubalgebra) :
    ringClassField O' ≤ ringClassField O := by
  have hdvd : O'.conductorModulus ∣ O.conductorModulus := by
    refine Modulus.dvd_iff.2 ⟨?_, ?_⟩
    · rw [conductorModulus_finitePart, conductorModulus_finitePart, Ideal.dvd_iff_le]
      exact conductor_mono h
    · rw [conductorModulus_infinitePart]
      exact Finset.empty_subset _
  have hker : (ringClassIdeleQuotient O).ker ≤ (ringClassIdeleQuotient O').ker := by
    intro c hc
    obtain ⟨J, hJc, β, hβ, hJβ⟩ := (mem_ker_ringClassIdeleQuotient_iff O).1 hc
    refine (mem_ker_ringClassIdeleQuotient_iff O').2
      ⟨integralIdealsPrimeToInclusion hdvd J, ?_, β, ?_, hJβ⟩
    · rw [← classMap_idealClass hdvd, hJc, classMap_rayClassQuotient]
    · rw [mem_toRingOfIntegers] at hβ ⊢
      exact h hβ
  have hN : ringClassNormSubgroup O ≤ ringClassNormSubgroup O' :=
    Subtype.coe_le_coe.symm.trans OpenSubgroup.toSubgroup_le.symm |>.2 hker
  exact (globalClassField_orderReversing _ _).1 hN

/-- `ℤ + dq𝒪_K ⊆ ℤ + d𝒪_K`. Kind: PROVED. -/
theorem conductorOrder_mul_le (d q : ℕ) [NeZero d] [NeZero q] [NeZero (d * q)] :
    (conductorOrder K (d * q)).toSubalgebra ≤ (conductorOrder K d).toSubalgebra := by
  rintro x ⟨a, y, rfl⟩
  exact ⟨a, (q : 𝓞 K) * y, by push_cast; ring⟩

/-- **`H_d ⊆ H_{dq}`** (PROVED). -/
theorem ringClassField_le_mul (d q : ℕ) [NeZero d] [NeZero q] [NeZero (d * q)] :
    ringClassField (conductorOrder K d) ≤ ringClassField (conductorOrder K (d * q)) :=
  ringClassField_mono (conductorOrder_mul_le d q)

/-- **`D.H d ⊆ D.H (dq)`** for the anchored datum at admissible `(d, q)` (PROVED). -/
theorem heegnerField_le_mul {E : WeierstrassCurve ℚ} {p : CSTParam E} {ι : Qbar →ₐ[ℚ] ℂ}
    {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} {D : HeegnerPointData E} (hA : FullAnchor E K p ι κ D)
    {d q : ℕ} [NeZero d] (hadm : D.Admissible d q) : ∀ x ∈ D.H d, x ∈ D.H (d * q) := by
  obtain ⟨hd, hdcop, hq, hqd⟩ := hadm
  have : NeZero q := ⟨hq.ne_zero⟩
  have : NeZero (d * q) := ⟨Nat.mul_ne_zero (NeZero.ne d) hq.ne_zero⟩
  have hcopP : Nat.Coprime d (D.N * D.DK.natAbs) :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 (by ring)) hdcop
  have hcopR : Nat.Coprime (d * q) (D.N * D.DK.natAbs) := by
    refine Nat.Coprime.mul_left hcopP ?_
    exact (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqd (h.trans ⟨6 * d, by ring⟩)
  intro x hx
  rw [hA.field d hcopP] at hx
  rw [hA.field (d * q) hcopR]
  obtain ⟨z, hz, hzx⟩ := hx
  exact ⟨z, ringClassField_le_mul d q hz, hzx⟩

end ZInQ.Contrib.CloudB3E2.NormCochain
