import ZInQKernel.Contrib.RC53Assist.DiskOrders.Limit.CocycleLimit
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.DeltaNaturality

/-!
# Compatibility of the finite Kummer sequences

The transition on geometric torsion is inclusion `E[2^n] ⊆ E[2^(n+1)]`.
The transition on rational-point quotients is multiplication by two; the
transition on the finite Shafarevich–Tate terms is inclusion. Naturality of the
connecting map proves the commuting Kummer square. It also gives division
by two in the limiting Kummer image.

Kinds: definitions and PROVED. Locators: the coefficient Kummer sequence and
naturality of its degree-zero connecting map, Silverman X.4.2.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.DiskOrders.Limit

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Manuscript.RC53Assist.QuadraticDescent

variable (r : SeparableClosure ℚ) (E : WeierstrassCurve ℚ)

/-- Inclusion between consecutive geometric torsion levels.
Kind: definition; the two-power direct system. -/
def levelCoeffUp (n : ℕ) :
    E.TorsionCoeff (2 ^ n) →+[galK r] E.TorsionCoeff (2 ^ (n + 1)) where
  toFun P := ⟨P.1, AddSubgroup.torsionBy.nsmul_iff.2 (by
    have hP := AddSubgroup.torsionBy.nsmul_iff.1 P.2
    rw [pow_succ, mul_nsmul, hP, nsmul_zero])⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The map between consecutive finite cohomology levels.
Kind: definition; cohomology of torsion inclusion. -/
def levelNext (n : ℕ) : H1 (galK r) (E.TorsionCoeff (2 ^ n)) →+
    H1 (galK r) (E.TorsionCoeff (2 ^ (n + 1))) :=
  explicitCoeff1 (galK r) (E.TorsionCoeff (2 ^ n))
    (levelCoeffUp r E n) continuous_of_discreteTopology

/-- The maps from consecutive levels to infinite cohomology agree.
Kind: PROVED; composition of coefficient inclusions. -/
theorem levelToInfinite_next (n : ℕ)
    (c : H1 (galK r) (E.TorsionCoeff (2 ^ n))) :
    levelToInfinite r E (n + 1) (levelNext r E n c) = levelToInfinite r E n c := by
  change ((explicitCoeff1 (galK r) (E.TorsionCoeff (2 ^ (n + 1)))
      (levelCoeffToInfinite r E (n + 1)) continuous_of_discreteTopology).comp
    (explicitCoeff1 (galK r) (E.TorsionCoeff (2 ^ n)) (levelCoeffUp r E n)
      continuous_of_discreteTopology)) c = _
  rw [← explicitCoeff1_comp]
  rfl

/-- The finite inclusions into point cohomology agree under transition.
Kind: PROVED; the commuting right-hand square of the finite Kummer sequences. -/
theorem levelIncl_next (n : ℕ)
    (c : H1 (galK r) (E.TorsionCoeff (2 ^ n))) :
    levelIncl r E (n + 1) (levelNext r E n c) = levelIncl r E n c := by
  rw [← inclK_levelToInfinite, levelToInfinite_next, inclK_levelToInfinite]

/-- Consecutive-level transition preserves every local Selmer condition.
Kind: PROVED; the finite coefficient inclusions commute with point cohomology. -/
theorem levelNext_mem_selmer {n : ℕ}
    {c : H1 (galK r) (E.TorsionCoeff (2 ^ n))} (hc : c ∈ selmerLevelK r E n) :
    levelNext r E n c ∈ selmerLevelK r E (n + 1) := by
  change levelIncl r E (n + 1) (levelNext r E n c) ∈ shaK r E
  rw [levelIncl_next]
  exact hc

/-- Multiplication by two on geometric points, as a `G_K`-equivariant map.
Kind: definition; the source transition in the Kummer diagram. -/
def pointCoeffDouble : E.PointCoeff →+[galK r] E.PointCoeff :=
  { nsmulAddMonoidHom 2 with map_smul' g P := smul_comm (2 : ℕ) g P }

/-- The Kummer connecting maps commute with the transition on point quotients.
Kind: PROVED; naturality applied to inclusion, identity, and multiplication by two. -/
theorem levelNext_levelDelta [E.IsElliptic] (n : ℕ) (P : pointsK r E) :
    levelNext r E n (levelDelta r E n P) = levelDelta r E (n + 1) (2 • P) := by
  have h := (levelSequence r E n).explicitDelta0_coeffMap
    (levelSequence r E (n + 1)) (levelCoeffUp r E n)
    (DistribMulActionHom.id (galK r)) (pointCoeffDouble r E)
    (fun a => rfl) (fun b => by
      change (2 : ℕ) • ((2 ^ n) • b) = (2 ^ (n + 1)) • b
      rw [pow_succ, mul_nsmul]) P
  exact h

/-- Each limiting finite Kummer class has a half at the next finite level.
Kind: PROVED; the commuting Kummer square and additivity. -/
theorem infinite_levelDelta_half [E.IsElliptic] (n : ℕ) (P : pointsK r E) :
    (2 : ℕ) • levelToInfinite r E (n + 1) (levelDelta r E (n + 1) P) =
      levelToInfinite r E n (levelDelta r E n P) := by
  rw [← map_nsmul, ← map_nsmul, ← levelNext_levelDelta, levelToInfinite_next]

/-- Finite Kummer classes remain in the kernel after passage to infinite coefficients.
Kind: PROVED; exactness of the finite coefficient Kummer sequence. -/
theorem inclK_infinite_levelDelta [E.IsElliptic] (n : ℕ) (P : pointsK r E) :
    inclK r E (levelToInfinite r E n (levelDelta r E n P)) = 0 := by
  rw [inclK_levelToInfinite]
  have hP : levelDelta r E n P ∈ (levelDelta r E n).range := ⟨P, rfl⟩
  rw [levelDelta_range] at hP
  exact hP

end ZInQ.Contrib.RC53Assist.DiskOrders.Limit
