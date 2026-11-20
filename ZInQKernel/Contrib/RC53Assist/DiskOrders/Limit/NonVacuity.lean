import ZInQKernel.Contrib.RC53Assist.DiskOrders.Limit.PassageToLimit
import ZInQKernel.Contrib.OneProof.SelmerTwoPowerNonVacuity

/-!
# Non-vacuity of the finite-level statement

For `E : y² = x(x - 1)(x + 3)` over `ℚ`, the Kummer class of `(0, 0)` is a nonzero
finite Selmer class. There is also a finite cohomology class excluded by the real
local condition. These statements are transported to the fixed-geometric-point
model without changing its local conditions. The ellipticity hypothesis and the
imaginary quadratic field `ℚ(√(-1))` are inhabited as well.

Kinds: PROVED. Locators: Silverman X.4.2; the duplication formula at `(0, 0)`;
and complex conjugation in the real local condition.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.DiskOrders.Limit

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Manuscript.SelmerTwoPower.NonVacuity
open ZInQ.Manuscript.RC53Assist.QuadraticDescent

variable (E : WeierstrassCurve ℚ) (n : ℕ)

/-- For rational curves, finite Selmer membership is exactly infinite membership of
its coefficient image. Kind: PROVED; the two coefficient inclusions have the same composite. -/
theorem rational_finite_mem_iff (c : H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))) :
    explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))
      (torsionToTwoPower E n) continuous_of_discreteTopology c ∈ selmerTwoPower E ↔
      c ∈ selmerAt E n := by
  have hcomp : explicitCoeff1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (twoPowerCoeffIncl E)
      continuous_of_discreteTopology
      (explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))
        (torsionToTwoPower E n) continuous_of_discreteTopology c) =
      explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))
        (E.torsionCoeffIncl (2 ^ n)) continuous_of_discreteTopology c := by
    rw [← AddMonoidHom.comp_apply, ← explicitCoeff1_comp]
    rfl
  simp only [selmerTwoPower, AddSubgroup.mem_comap, hcomp, sha, selmerAt,
    AddSubgroup.mem_inf, WeierstrassCurve.mem_selmerGroup_iff]

/-- Restriction to `G_K` commutes with passage from finite to infinite coefficients.
Kind: PROVED; composition of the compatible group and coefficient maps. -/
theorem levelToInfinite_res (r : SeparableClosure ℚ)
    (c : H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))) :
    levelToInfinite r E n
      (explicitRes1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n)) (galK r) c) =
      explicitRes1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK r)
        (explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))
          (torsionToTwoPower E n) continuous_of_discreteTopology c) := by
  induction c using QuotientAddGroup.induction_on with
  | H c =>
    rw [levelToInfinite, explicitRes1_mk, explicitCoeff1_mk, explicitCoeff1_mk,
      explicitRes1_mk]
    apply congrArg (fun z : Z1 (galK r) (TwoPowerCoeff E) =>
      (z : H1 (galK r) (TwoPowerCoeff E)))
    apply Subtype.ext
    funext g
    exact Subtype.ext rfl

/-- The finite groups for the root `1` are the genuine rational finite Selmer groups.
Kind: PROVED; rational consistency and the commuting coefficient square. -/
theorem rational_selmerLevel_mem_iff
    (c : H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))) :
    explicitRes1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n)) (galK 1) c ∈
      selmerLevelK 1 E n ↔ c ∈ selmerAt E n := by
  let y := explicitCoeff1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n))
    (torsionToTwoPower E n) continuous_of_discreteTopology c
  calc
    _ ↔ explicitRes1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) (galK 1) y ∈ selmerK 1 E := by
      change levelIncl 1 E n
        (explicitRes1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n)) (galK 1) c) ∈ shaK 1 E ↔ _
      rw [← inclK_levelToInfinite, levelToInfinite_res]
      rfl
    _ ↔ y ∈ selmerTwoPower E :=
      (mem_selmerTwoPower_iff_res_mem_selmerK_one E y).symm
    _ ↔ c ∈ selmerAt E n := rational_finite_mem_iff E n c

/-- The elliptic curve in the examples is nonsingular.
Kind: PROVED; discriminant `2304`, the specialized ellipticity calculation. -/
theorem elliptic_example : (ZInQ.Manuscript.curve (1 : ℚ)).IsElliptic :=
  curve_isElliptic' one_ne_zero

/-- The finite Selmer group in the fixed-point model has a nonzero element.
Kind: PROVED; the Kummer class of `(0, 0)` and injectivity of rational restriction. -/
theorem finite_selmer_nonzero :
    ∃ c : selmerLevelK 1 (ZInQ.Manuscript.curve (1 : ℚ)) 1, c ≠ 0 := by
  obtain ⟨c, hc, hc0⟩ := selmerAt_curve_exists_ne_zero (ℓ := (1 : ℚ)) one_ne_zero
  have hcS := (rational_selmerLevel_mem_iff _ 1 c).2 hc
  refine ⟨⟨_, hcS⟩, ?_⟩
  intro hzero
  apply hc0
  apply explicitRes1_injective_of_forall_mem (galK 1)
    (fun g => mem_galK.2 (map_one g))
  exact (congrArg Subtype.val hzero).trans (map_zero _).symm

/-- The real local condition excludes a finite cohomology class.
Kind: PROVED; the complex-conjugation obstruction for `y² = x(x - 1)(x + 3)`. -/
theorem finite_selmer_proper :
    ∃ c : H1 (galK 1) ((ZInQ.Manuscript.curve (1 : ℚ)).TorsionCoeff (2 ^ 1)),
      c ∉ selmerLevelK 1 (ZInQ.Manuscript.curve (1 : ℚ)) 1 := by
  refine ⟨explicitRes1 _ _ (galK 1) (cls (ℓ := (1 : ℚ)) one_ne_zero), ?_⟩
  intro h
  exact cls_not_mem_selmerAt (ℓ := (1 : ℚ)) one_ne_zero
    ((rational_selmerLevel_mem_iff _ 1 _).1 h)

/-- The imaginary quadratic example has a genuine nontrivial Galois quotient.
Kind: PROVED; `-1` is not a rational square. -/
theorem imaginary_quadratic_nontrivial :
    ∃ g : AbsoluteGaloisGroup ℚ, g ∉ galK (sqrtK (-1)) :=
  exists_not_mem_galK (not_isSquare_of_neg (by norm_num))

/-- The literal finite PRINT specializes to the elliptic curve over `ℚ(√(-1))` at level one.
Kind: PROVED; an inhabited specialization of Silverman X.4.2. -/
theorem quadratic_level_example :
    letI := elliptic_example
    Function.Exact (levelKummer (sqrtK (-1)) (ZInQ.Manuscript.curve (1 : ℚ)) 1)
      (levelToSha (sqrtK (-1)) (ZInQ.Manuscript.curve (1 : ℚ)) 1) :=
  (silvermanX42TwoPowerLevelPrint (-1) _ elliptic_example 1).2.1

end ZInQ.Contrib.RC53Assist.DiskOrders.Limit
