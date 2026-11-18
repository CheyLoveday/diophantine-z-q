import ZInQKernel.Contrib.OneProof.RC.Height.SumDifference
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension

/-!
# Lane RC19 (height): the quadratic-field hypotheses are satisfiable

The sum/difference theorems of `SumDifference.lean` assume a quadratic number field `K`
(`[Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]`) with a datum `D : QuadData K k`:
a square root `s ≠ 0` of `k` in `K` and a `ℚ`-automorphism `σ` of `K` with `σ s = −s`. This file
shows that these hypotheses are not vacuous: they are met by `K = ℚ(√k)` whenever `k` is not a
square in `ℚ` (for instance by the Gaussian field `ℚ(i)`, `k = −1`), and only for such `k`.

The field `ℚ(√k)` is Mathlib's quadratic algebra `QuadraticAlgebra ℚ k 0 = ℚ ⊕ ℚω`, `ω² = k`,
which is a field when `k` is not a square. It is wrapped in the type synonym `SqrtField k`, so that
the only `ℚ`-algebra structure on it is the canonical one coming from its field structure
(`DivisionRing.toRatAlgebra`), which is the structure used by the hypotheses of the
sum/difference theorems.

Every declaration in this file is PROVED.

* `SqrtField k`, with instances `DecidableEq` and, under `[Fact (¬IsSquare k)]`, `Field`,
  `CharZero`, `Algebra.IsQuadraticExtension ℚ (SqrtField k)` and `NumberField`.
* `SqrtField.root`, `SqrtField.root_sq`, `SqrtField.root_ne_zero`: the square root `√k = ω`.
* `SqrtField.conj`, `SqrtField.conj_root`: the conjugation `x + y√k ↦ x − y√k` as a
  `ℚ`-algebra automorphism, with `conj √k = −√k`.
* `SqrtField.quadData : QuadData (SqrtField k) k`.
* `exists_quadData_of_not_isSquare`, `QuadData.not_isSquare`, `exists_quadData_iff`: a quadratic
  number field carrying a `QuadData _ k` exists iff `k` is not a square in `ℚ`.
* `GaussField = SqrtField (-1)` (the field `ℚ(i)`), `GaussField.quadData : QuadData GaussField (-1)`
  and `exists_quadData`: there is a quadratic number field carrying a `QuadData _ (-1)`.
* `SqrtField.quadData_σ_σ`, `sumMap_diffMap_sqrtField`, `diffMap_sumMap_sqrtField`: the results
  `QuadData.σ_σ`, `sumMap_diffMap` and `diffMap_sumMap` of `SumDifference.lean` apply to
  `SqrtField.quadData k`, i.e. their instance hypotheses are met by the instances above.
-/

namespace ZInQ.Manuscript.RC.Height

open QuadraticAlgebra

/-! ### The field `ℚ(√k)` -/

/-- **The quadratic field `ℚ(√k)`**: Mathlib's quadratic algebra `QuadraticAlgebra ℚ k 0`,
i.e. `ℚ ⊕ ℚω` with `ω² = k`; it is a field when `k` is not a square in `ℚ`. A type synonym, so
that its only `ℚ`-algebra structure is the canonical one coming from its field structure. -/
def SqrtField (k : ℚ) : Type := QuadraticAlgebra ℚ k 0

namespace SqrtField

variable (k : ℚ)

/-- Decidable equality on `ℚ(√k)` (componentwise). -/
instance instDecidableEq : DecidableEq (SqrtField k) :=
  inferInstanceAs (DecidableEq (QuadraticAlgebra ℚ k 0))

/-- The square root `√k` in `ℚ(√k)`: the generator `ω` of the quadratic algebra. -/
def root : SqrtField k := (ω : QuadraticAlgebra ℚ k 0)

variable [Fact (¬IsSquare k)]

/-- `ℚ(√k)` is a field when `k` is not a square in `ℚ`. -/
instance instField : Field (SqrtField k) := inferInstanceAs (Field (QuadraticAlgebra ℚ k 0))

/-- `ℚ(√k)` has characteristic zero. PROVED. -/
instance instCharZero : CharZero (SqrtField k) :=
  inferInstanceAs (CharZero (QuadraticAlgebra ℚ k 0))

/-- `ℚ(√k)` is a quadratic extension of `ℚ`, for the canonical `ℚ`-algebra structure. PROVED. -/
instance instIsQuadraticExtension : Algebra.IsQuadraticExtension ℚ (SqrtField k) :=
  inferInstanceAs (Algebra.IsQuadraticExtension ℚ (QuadraticAlgebra ℚ k 0))

/-- `ℚ(√k)` is a number field. PROVED. -/
instance instNumberField : NumberField (SqrtField k) where
  to_finiteDimensional := inferInstance

/-- `(√k)² = k`. PROVED. -/
theorem root_sq : root k ^ 2 = algebraMap ℚ (SqrtField k) k := by
  have h : (ω : QuadraticAlgebra ℚ k 0) ^ 2 = QuadraticAlgebra.C k := by
    ext <;> simp [sq]
  exact h

/-- `√k ≠ 0`. PROVED. -/
theorem root_ne_zero : root k ≠ 0 := by
  have h : (ω : QuadraticAlgebra ℚ k 0) ≠ 0 := by
    intro h
    simpa using congrArg QuadraticAlgebra.im h
  exact h

/-- The conjugation `x + y√k ↦ x − y√k` of `ℚ(√k)`, as a ring automorphism: the quadratic
involution `star` of the quadratic algebra. -/
def conjRingEquiv : SqrtField k ≃+* SqrtField k := starRingAut (R := QuadraticAlgebra ℚ k 0)

/-- The conjugation of `ℚ(√k)`, as a `ℚ`-algebra automorphism. -/
def conj : SqrtField k ≃ₐ[ℚ] SqrtField k := (conjRingEquiv k).toRatAlgEquiv

/-- `conj √k = −√k`. PROVED. -/
theorem conj_root : conj k (root k) = -root k := by
  have h : star (ω : QuadraticAlgebra ℚ k 0) = -ω := by
    ext <;> simp
  exact h

/-- **A `QuadData` for `ℚ(√k)`**: `s = √k` and `σ` the conjugation `√k ↦ −√k`. -/
def quadData : QuadData (SqrtField k) k where
  s := root k
  hs := root_ne_zero k
  hsk := root_sq k
  σ := conj k
  hσ := conj_root k

/-- The automorphism of `quadData k` is an involution, by `QuadData.σ_σ` (whose hypotheses
`NumberField` and `Algebra.IsQuadraticExtension ℚ _` are met by `ℚ(√k)`). PROVED. -/
theorem quadData_σ_σ (x : SqrtField k) : (quadData k).σ ((quadData k).σ x) = x :=
  (quadData k).σ_σ x

end SqrtField

/-! ### A `QuadData _ k` exists exactly for non-square `k` -/

/-- If `k` is not a square in `ℚ`, there is a quadratic number field (`ℚ(√k)`) carrying a
`QuadData _ k`. PROVED. -/
theorem exists_quadData_of_not_isSquare {k : ℚ} (hk : ¬IsSquare k) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Algebra.IsQuadraticExtension ℚ K ∧ Nonempty (QuadData K k) :=
  haveI : Fact (¬IsSquare k) := ⟨hk⟩
  ⟨SqrtField k, inferInstance, inferInstance, inferInstance, ⟨SqrtField.quadData k⟩⟩

/-- A `QuadData K k` forces `k` to be a non-square in `ℚ`: if `k = r²`, then `s = ±r` is fixed
by `σ`, and `σ s = −s` gives `s = 0`. PROVED. -/
theorem QuadData.not_isSquare {K : Type*} [Field K] [Algebra ℚ K] {k : ℚ} (D : QuadData K k) :
    ¬IsSquare k := by
  rintro ⟨r, rfl⟩
  have h1 : (D.s - algebraMap ℚ K r) * (D.s + algebraMap ℚ K r) = 0 := by
    have h := D.hsk
    rw [map_mul] at h
    linear_combination h
  have hfix : D.σ D.s = D.s := by
    rcases mul_eq_zero.mp h1 with h | h
    · rw [sub_eq_zero.mp h, AlgEquiv.commutes]
    · rw [eq_neg_of_add_eq_zero_left h, map_neg, AlgEquiv.commutes]
  have h2 : (2 : K) * D.s = 0 := by linear_combination D.hσ - hfix
  have h3 : (2 : K) ≠ 0 := by
    have := (algebraMap ℚ K).injective.ne (two_ne_zero : (2 : ℚ) ≠ 0)
    rwa [map_ofNat, map_zero] at this
  exact D.hs ((mul_eq_zero.mp h2).resolve_left h3)

/-- **The quadratic-field hypotheses are satisfiable exactly for non-square `k`**: there is a
quadratic number field carrying a `QuadData _ k` iff `k` is not a square in `ℚ`. PROVED. -/
theorem exists_quadData_iff (k : ℚ) :
    (∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Algebra.IsQuadraticExtension ℚ K ∧ Nonempty (QuadData K k)) ↔ ¬IsSquare k :=
  ⟨fun ⟨_, _, _, _, ⟨D⟩⟩ => D.not_isSquare, exists_quadData_of_not_isSquare⟩

/-! ### The Gaussian field `ℚ(i)` -/

/-- `−1` is not a square in `ℚ`. PROVED. -/
theorem not_isSquare_neg_one_rat : ¬IsSquare (-1 : ℚ) := by
  rintro ⟨r, hr⟩
  nlinarith [mul_self_nonneg r]

/-- `−1` is not a square in `ℚ`, as an instance (it makes `SqrtField (-1)` a field). PROVED. -/
instance fact_not_isSquare_neg_one_rat : Fact (¬IsSquare (-1 : ℚ)) :=
  ⟨not_isSquare_neg_one_rat⟩

/-- **The Gaussian field `ℚ(i)`**: `SqrtField (-1)`, with `i = SqrtField.root (-1)` and complex
conjugation `SqrtField.conj (-1)`. -/
abbrev GaussField : Type := SqrtField (-1)

/-- **A `QuadData` for `ℚ(i)` and `k = −1`**: `s = i` (`i² = −1`, `i ≠ 0`) and `σ` complex
conjugation (`σ i = −i`). -/
def GaussField.quadData : QuadData GaussField (-1) := SqrtField.quadData (-1)

/-- **Non-vacuity of the quadratic-field hypotheses**: there is a quadratic number field `K`
(here `ℚ(i)`) carrying a `QuadData K (-1)`. PROVED. -/
theorem exists_quadData : ∃ (K : Type) (_ : Field K) (_ : NumberField K),
    Algebra.IsQuadraticExtension ℚ K ∧ Nonempty (QuadData K (-1)) :=
  ⟨GaussField, inferInstance, inferInstance, inferInstance, ⟨GaussField.quadData⟩⟩

/-! ### The sum/difference theorems apply to `ℚ(√k)` -/

section Apply

variable (k : ℚ) [Fact (¬IsSquare k)] (E : WeierstrassCurve ℚ) (h : ℚ)

/-- `ψ ∘ φ = [2]` (`sumMap_diffMap`) instantiated at `K = ℚ(√k)` and `D = SqrtField.quadData k`,
for a point `P` of the twist `E^{(h)}` over `ℚ(√k)`: the hypotheses of the sum/difference
theorems on `K` and `D` are met. PROVED. -/
theorem sumMap_diffMap_sqrtField (P) :
    sumMap E h k (SqrtField.quadData k) (diffMap E h k (SqrtField.quadData k) P) = 2 • P :=
  sumMap_diffMap E h k (SqrtField.quadData k) P

/-- `φ ∘ ψ = [2]` (`diffMap_sumMap`) instantiated at `K = ℚ(√k)` and `D = SqrtField.quadData k`,
for `x ∈ E^{(h)}(ℚ) × E^{(hk)}(ℚ)`. PROVED. -/
theorem diffMap_sumMap_sqrtField (x) :
    diffMap E h k (SqrtField.quadData k) (sumMap E h k (SqrtField.quadData k) x) = 2 • x :=
  diffMap_sumMap E h k (SqrtField.quadData k) x

end Apply

end ZInQ.Manuscript.RC.Height
