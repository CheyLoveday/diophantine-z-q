import ZInQKernel.Contrib.OneProof.SGRDirectNVLocal

set_option linter.style.haveILetI false

open Polynomial CategoryTheory AlgebraicGeometry IsLocalRing
open GlueDescent.B2Q NumberField
open HDec HDec.G0ModField HDec.PropTSRed HDec.PropTSGlue HDec.HeckeRestNV HDec.TSHecke LeafQM LeafQM.AV

noncomputable section

namespace SGRDirect.NVLocal

/-- **The ramification index is unchanged by localizing the base at a submonoid** missing the prime
(Mathlib's `IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx`, for any submonoid). -/
theorem ramificationIdx_map_localization {R S Rₘ Sₘ : Type*} [CommRing R] [CommRing S]
    [CommRing Rₘ] [CommRing Sₘ] [Algebra R S] [Algebra R Rₘ] [Algebra S Sₘ] [Algebra Rₘ Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] [IsScalarTower R Rₘ Sₘ] (M : Submonoid R)
    [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
    (P : Ideal S) [P.IsPrime] (hP : Disjoint (M : Set R) (P.under R)) :
    (P.map (algebraMap S Sₘ)).ramificationIdx Rₘ = P.ramificationIdx R := by
  have hdisj : Disjoint ((Algebra.algebraMapSubmonoid S M : Submonoid S) : Set S) (P : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxP
    exact Set.disjoint_left.mp hP hx hxP
  haveI hPm : (P.map (algebraMap S Sₘ)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ Sₘ P inferInstance hdisj
  have hcomap : (P.map (algebraMap S Sₘ)).comap (algebraMap S Sₘ) = P :=
    IsLocalization.under_map_of_isPrime_disjoint _ Sₘ inferInstance hdisj
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def]
  let R₁ := Localization.AtPrime (P.map (algebraMap S Sₘ))
  let R₂ := Localization.AtPrime P
  haveI : (P.map (algebraMap S Sₘ)).LiesOver P := ⟨hcomap.symm⟩
  let : Algebra R₂ R₁ := Localization.AtPrime.algebraOfLiesOver P (P.map (algebraMap S Sₘ))
  haveI : IsLocalization.AtPrime R₁ P := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid S M) R₁ (P.map (algebraMap S Sₘ))
    exact hcomap.symm
  have h : Function.Bijective (algebraMap R₂ R₁) :=
    (Localization.algEquiv P.primeCompl R₁).bijective
  have hunder : (P.map (algebraMap S Sₘ)).under Rₘ = (P.under R).map (algebraMap R Rₘ) := by
    rw [← IsLocalization.map_under M Rₘ ((P.map (algebraMap S Sₘ)).under Rₘ)]
    congr 1
    have hc : Ideal.under S (P.map (algebraMap S Sₘ)) = P := hcomap
    rw [Ideal.under_under, ← Ideal.under_under (B := S), hc]
  have hcomp : (algebraMap R₂ R₁).comp (algebraMap R R₂) = (algebraMap Rₘ R₁).comp (algebraMap R Rₘ) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have key : (P.under R).map (algebraMap R R₂) =
      (((P.map (algebraMap S Sₘ)).under Rₘ).map (algebraMap Rₘ R₁)).comap (algebraMap R₂ R₁) := by
    rw [hunder, Ideal.map_map, ← hcomp, ← Ideal.map_map, Ideal.comap_map_of_bijective _ h]
  rw [Module.length_quotient, Module.length_quotient, key, Ideal.coheight_comap_of_surjective _ h.2]

end SGRDirect.NVLocal
