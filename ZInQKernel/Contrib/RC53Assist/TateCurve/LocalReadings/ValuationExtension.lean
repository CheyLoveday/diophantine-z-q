import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalArithmetic
import ZInQKernel.Contrib.RC53Assist.DecompositionGlue.Glue

/-!
# Integers and uniqueness of a valuation extension

The spectral unit ball is the integral closure of the base valuation ring.
Every other valuation extension contains that ring. An integral extension of a
one-dimensional valuation ring has dimension at most one, so a nontrivial
coarsening cannot be proper. This gives uniqueness without choosing a value-group
normalization on the algebraic closure.

Kinds: definitions and proved statements only.
Locators: Serre, *Local Fields*, II, §2 and III, §5; spectral norm and valuation
ring coarsenings. The book is distinct from Serre's chapter in Cassels--Fröhlich.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open Polynomial
open ZInQ.Contrib.RC53Assist.DecompositionGlue
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.GlobalTrace
open scoped NNReal WithZero

/-- **PROVED**: an integral element has value at most one if all base-ring
coefficients do. Locator: integrally closed valuation rings. -/
theorem integral_valuation_le_one {O F Γ : Type*} [CommRing O] [Field F]
    [Algebra O F] [LinearOrderedCommGroupWithZero Γ] (w : Valuation F Γ)
    (hO : ∀ a : O, w (algebraMap O F a) ≤ 1) {x : F} (hx : IsIntegral O x) :
    w x ≤ 1 := by
  let f : O →+* w.valuationSubring := (algebraMap O F).codRestrict _ hO
  letI : Algebra O w.valuationSubring := f.toAlgebra
  haveI : IsScalarTower O w.valuationSubring F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Valuation.valuationSubring.integers w).isIntegral_iff_v_le_one.mp
    (hx.tower_top : IsIntegral w.valuationSubring x)

/-- **PROVED**: spectral value at most one makes every coefficient of the
minimal polynomial integral over the base valuation ring.
Locator: the coefficient formula for the spectral value. -/
theorem isIntegral_of_spectralNorm_le_one {K Γ : Type*} [NormedField K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hkv : ∀ a : K, ‖a‖ ≤ 1 ↔ v a ≤ 1)
    (x : AlgebraicClosure K) (hx : spectralNorm K (AlgebraicClosure K) x ≤ 1) :
    IsIntegral v.valuationSubring x := by
  have hi : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hc : ∀ i : ℕ, (minpoly K x).coeff i ∈ v.valuationSubring := by
    intro i
    exact (hkv _).mp ((spectralValue_le_one_iff (minpoly.monic hi)).mp hx i)
  have hr : minpoly K x ∈ (mapRingHom (algebraMap v.valuationSubring K)).range := by
    apply (mem_map_range _).mpr
    intro i
    exact ⟨⟨(minpoly K x).coeff i, hc i⟩, rfl⟩
  obtain ⟨P, hP⟩ := hr
  change P.map (algebraMap v.valuationSubring K) = minpoly K x at hP
  refine ⟨P, ?_, ?_⟩
  · apply monic_of_injective (IsFractionRing.injective v.valuationSubring K)
    rw [hP]
    exact minpoly.monic hi
  · change aeval x P = 0
    rw [← aeval_map_algebraMap K x P, hP]
    exact minpoly.aeval K x

/-- **PROVED**: the spectral valuation extends the base valuation up to
normalization. Locator: spectral norm extension and comparison with one. -/
theorem spectral_hasExtension {K Γ : Type*} [NontriviallyNormedField K]
    [CompleteSpace K] [IsUltrametricDist K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hkv : ∀ a : K, ‖a‖ ≤ 1 ↔ v a ≤ 1) :
    v.HasExtension (spectralValuation K) := by
  constructor
  rw [Valuation.isEquiv_iff_val_le_one]
  intro a
  change v a ≤ 1 ↔ spectralValuation K (algebraMap K (AlgebraicClosure K) a) ≤ 1
  rw [← NNReal.coe_le_coe, spectralValuation_algebraMap, NNReal.coe_one]
  exact (hkv a).symm

/-- **PROVED**: a valuation of the algebraic closure extending a complete
DVR valuation has the same valuation ring as the spectral valuation.
Locator: integral closure of the unit ball and rank-one valuation coarsenings. -/
theorem valuationSubring_eq_spectral {K Γ₀ Γ : Type*} [NontriviallyNormedField K]
    [CompleteSpace K] [IsUltrametricDist K] [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ₀)
    [IsDiscreteValuationRing v.valuationSubring]
    (hkv : ∀ a : K, ‖a‖ ≤ 1 ↔ v a ≤ 1)
    (w : Valuation (AlgebraicClosure K) Γ)
    (hw : (w.comap (algebraMap K (AlgebraicClosure K))).IsEquiv v) :
    w.valuationSubring = (spectralValuation K).valuationSubring := by
  letI : v.HasExtension (spectralValuation K) := spectral_hasExtension v hkv
  letI : Algebra v.valuationSubring (spectralValuation K).valuationSubring :=
    Valuation.HasExtension.instAlgebra_valuationSubring v (spectralValuation K)
  haveI : IsScalarTower v.valuationSubring (spectralValuation K).valuationSubring
      (AlgebraicClosure K) :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring' v (spectralValuation K)
  haveI : Algebra.IsIntegral v.valuationSubring (spectralValuation K).valuationSubring := by
    constructor
    intro x
    apply (isIntegral_algebraMap_iff (A := (spectralValuation K).valuationSubring)
      (B := AlgebraicClosure K)).mp
    apply isIntegral_of_spectralNorm_le_one v hkv
    exact (spectralValuation_le_one_iff _).mp x.2
  haveI : Ring.DimensionLEOne (spectralValuation K).valuationSubring :=
    Ring.DimensionLEOne.of_isIntegral v.valuationSubring _
  have hle : (spectralValuation K).valuationSubring ≤ w.valuationSubring := by
    intro x hx
    apply integral_valuation_le_one (O := v.valuationSubring) w
    · intro a
      change w (algebraMap K (AlgebraicClosure K) (a : K)) ≤ 1
      exact hw.le_one_iff_le_one.mpr a.2
    · exact isIntegral_of_spectralNorm_le_one v hkv x
        ((spectralValuation_le_one_iff _).mp hx)
  have hne : w.valuationSubring ≠ ⊤ := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.valuationSubring
    have hvπ : v (π : K) < 1 :=
      (Valuation.valuationSubring.integers v).valuation_irreducible_lt_one hπ
    have hwπ : w (algebraMap K (AlgebraicClosure K) (π : K)) < 1 :=
      hw.lt_one_iff_lt_one.mpr hvπ
    have hπ0 : w (algebraMap K (AlgebraicClosure K) (π : K)) ≠ 0 := by
      apply (Valuation.ne_zero_iff _).mpr
      simpa only [map_zero] using (algebraMap K (AlgebraicClosure K)).injective.ne
        (show (π : K) ≠ 0 from Subtype.coe_injective.ne hπ.ne_zero)
    intro htop
    have hinv : (algebraMap K (AlgebraicClosure K) (π : K))⁻¹ ∈ w.valuationSubring := by
      rw [htop]
      exact Set.mem_univ _
    rw [Valuation.mem_valuationSubring_iff, map_inv₀] at hinv
    exact ((one_lt_inv₀ (zero_lt_iff.mpr hπ0)).mpr hwπ).not_ge hinv
  exact (ValuationSubring.eq_of_le_of_ne_top
    (spectralValuation K).valuationSubring hle hne).symm

/-- **PROVED**: all valuations in the rational local target are equivalent to
its spectral valuation. Locator: the preceding DVR uniqueness theorem. -/
theorem local_valuation_isEquiv_spectral (p : ℕ) (hp : p.Prime)
    (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ)
    (hw : (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
        (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰)) :
    letI := padicNontriviallyNormedField p hp
    w.IsEquiv (spectralValuation ((primeIdealQ p hp).adicCompletion ℚ)) := by
  letI := padicNontriviallyNormedField p hp
  apply (Valuation.isEquiv_iff_valuationSubring _ _).mpr
  exact valuationSubring_eq_spectral Valued.v (fun _ => Valued.toNormedField.norm_le_one_iff)
    w hw

/-- **PROVED**: every local automorphism preserves the value of every element,
even for an arbitrarily normalized extending valuation.
Locator: spectral invariance and valuation equivalence. -/
theorem local_valuation_galois (p : ℕ) (hp : p.Prime)
    (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ)
    (hw : (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
        (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰))
    (σ : LocalGaloisQ p hp)
    (x : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) : w (σ x) = w x := by
  letI := padicNontriviallyNormedField p hp
  exact (local_valuation_isEquiv_spectral p hp Γ w hw).eq_iff.mpr
    (spectralValuation_galois _ σ x)

end ZInQ.Contrib.RC53Assist.TateCurve
