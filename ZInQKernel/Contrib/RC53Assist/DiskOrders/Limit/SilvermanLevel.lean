import ZInQKernel.Contrib.RC53Assist.DiskOrders.ShaBridge

/-!
# The finite multiplication-by-two-power descent sequence

Silverman, *The Arithmetic of Elliptic Curves*, second edition, Theorem X.4.2:
`0 → E'(K)/φ(E(K)) → S^(φ)(E/K) → Ш(E/K)[φ] → 0`.
Here `φ = [2^n]`, so `E' = E`. Locator: Theorem X.4.2(a), page 333 (the Selmer and
Shafarevich-Tate groups are defined on page 332; pages checked).

The field is `K = ℚ(r)` inside `ℚˢ`. Rational points are realized as fixed geometric
points, `H⁰(G_K, E(ℚˢ))`. The finite Selmer group uses the same localizations at all
finite and infinite places as the two-primary Selmer group.

Kinds: definitions, a PRINT statement proved below, and PROVED algebraic identifications.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.DiskOrders

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Manuscript.RC53Assist.QuadraticDescent

namespace Limit

variable (r : SeparableClosure ℚ) (E : WeierstrassCurve ℚ)

/-- `E(K)` in the fixed-geometric-point model. Kind: definition; Silverman X.4. -/
abbrev pointsK := H0 (galK r) E.PointCoeff

/-- The finite coefficient inclusion on `H¹(G_K, -)`.
Kind: definition; Silverman X.4.2. -/
def levelIncl (n : ℕ) :
    H1 (galK r) (E.TorsionCoeff (2 ^ n)) →+ H1 (galK r) E.PointCoeff :=
  explicitMap1 (galK r) (E.TorsionCoeff (2 ^ n)) (galK r) E.PointCoeff
    (ContinuousMonoidHom.id _) (E.torsionCoeffIncl (2 ^ n)).toAddMonoidHom
    continuous_of_discreteTopology
    (fun g P => (E.torsionCoeffIncl (2 ^ n)).map_smul
      (g : AbsoluteGaloisGroup ℚ) P)

/-- `Sel_{2^n}(E/K)`, with local triviality at every place of `K`.
Kind: definition; Silverman X.4. -/
def selmerLevelK (n : ℕ) : AddSubgroup (H1 (galK r) (E.TorsionCoeff (2 ^ n))) :=
  (shaK r E).comap (levelIncl r E n)

/-- `Ш(E/K)[2^n]`. Kind: definition; Silverman X.4.2. -/
abbrev shaLevelK (n : ℕ) := AddSubgroup.torsionBy (shaK r E) (2 ^ n : ℕ)

/-- The coefficient inclusion has image killed by `2^n`.
Kind: PROVED; exponent inheritance on cohomology. -/
theorem levelIncl_killed (n : ℕ) (c : H1 (galK r) (E.TorsionCoeff (2 ^ n))) :
    (2 ^ n) • levelIncl r E n c = 0 := by
  rw [← map_nsmul, nsmul_H1_eq_zero (fun P => AddSubgroup.torsionBy.nsmul P), map_zero]

/-- The canonical finite-level map `Sel_{2^n}(E/K) → Ш(E/K)[2^n]`.
Kind: definition; Silverman X.4.2. -/
def levelToSha (n : ℕ) : selmerLevelK r E n →+ shaLevelK r E n where
  toFun c := ⟨⟨levelIncl r E n c, c.2⟩,
    AddSubgroup.torsionBy.nsmul_iff.2 (Subtype.ext (levelIncl_killed r E n c))⟩
  map_zero' := Subtype.ext (Subtype.ext (map_zero _))
  map_add' c d := Subtype.ext (Subtype.ext (map_add _ c.1 d.1))

/-- The finite coefficient Kummer sequence restricted to `G_K`.
Kind: definition; `0 → E[2^n] → E → E → 0`, Silverman X.4.2. -/
def levelSequence [E.IsElliptic] (n : ℕ) :
    DiscreteShortExact (galK r) (E.TorsionCoeff (2 ^ n)) E.PointCoeff E.PointCoeff :=
  (E.kummerShortExact (2 ^ n) (isUnit_iff_ne_zero.2 (by positivity))).restrict (galK r)

/-- The finite Kummer map on rational points.
Kind: definition; the degree-zero connecting map, Silverman X.4.2. -/
def levelDelta [E.IsElliptic] (n : ℕ) :
    pointsK r E →+ H1 (galK r) (E.TorsionCoeff (2 ^ n)) :=
  (levelSequence r E n).explicitDelta0

/-- The kernel of the finite Kummer map on points is `2^n E(K)`.
Kind: PROVED; degree-zero exactness of the coefficient Kummer sequence. -/
theorem levelDelta_ker [E.IsElliptic] (n : ℕ) :
    (levelDelta r E n).ker = (nsmulAddMonoidHom (α := pointsK r E) (2 ^ n)).range := by
  have h := (levelSequence r E n).explicitLongExact_H0C
  have he : explicitCoeff0 (galK r) E.PointCoeff
      (levelSequence r E n).projDistribMulActionHom =
      nsmulAddMonoidHom (α := pointsK r E) (2 ^ n) := by
    ext P
    rfl
  rw [he] at h
  exact h.symm

/-- The image of the finite Kummer map is the kernel of the coefficient inclusion.
Kind: PROVED; degree-one exactness of the coefficient Kummer sequence. -/
theorem levelDelta_range [E.IsElliptic] (n : ℕ) :
    (levelDelta r E n).range = (levelIncl r E n).ker :=
  (levelSequence r E n).explicitLongExact_H1A

/-- The Kummer map on `E(K)/2^n E(K)` with values in finite cohomology.
Kind: definition; Silverman X.4.2. -/
def levelClass [E.IsElliptic] (n : ℕ) :
    pointsK r E ⧸ (nsmulAddMonoidHom (α := pointsK r E) (2 ^ n)).range →+
      H1 (galK r) (E.TorsionCoeff (2 ^ n)) :=
  QuotientAddGroup.lift _ (levelDelta r E n) (levelDelta_ker r E n).ge

/-- A finite Kummer class vanishes under inclusion into the geometric point module.
Kind: PROVED; exactness of the coefficient Kummer sequence. -/
theorem levelIncl_levelClass [E.IsElliptic] (n : ℕ)
    (P : pointsK r E ⧸ (nsmulAddMonoidHom (α := pointsK r E) (2 ^ n)).range) :
    levelIncl r E n (levelClass r E n P) = 0 := by
  induction P using QuotientAddGroup.induction_on with
  | H P =>
    change levelIncl r E n (levelDelta r E n P) = 0
    have hP : levelDelta r E n P ∈ (levelDelta r E n).range := ⟨P, rfl⟩
    rw [levelDelta_range] at hP
    exact hP

/-- The canonical finite Kummer map `E(K)/2^n E(K) → Sel_{2^n}(E/K)`.
Kind: definition; Silverman X.4.2. -/
def levelKummer [E.IsElliptic] (n : ℕ) :
    pointsK r E ⧸ (nsmulAddMonoidHom (α := pointsK r E) (2 ^ n)).range →+
      selmerLevelK r E n :=
  (levelClass r E n).codRestrict _ fun P => by
    change levelIncl r E n (levelClass r E n P) ∈ shaK r E
    rw [levelIncl_levelClass]
    exact zero_mem _

/-- The finite quotient Kummer map is injective.
Kind: PROVED; degree-zero exactness, Silverman X.4.2. -/
theorem levelKummer_injective [E.IsElliptic] (n : ℕ) :
    Function.Injective (levelKummer r E n) := by
  intro P Q h
  exact (QuotientAddGroup.injective_lift_iff _ _ _).2
    (levelDelta_ker r E n).symm (congrArg Subtype.val h)

/-- The finite sequence is exact at its Selmer term.
Kind: PROVED; degree-one exactness, Silverman X.4.2. -/
theorem levelKummer_exact [E.IsElliptic] (n : ℕ) :
    Function.Exact (levelKummer r E n) (levelToSha r E n) := by
  intro c
  have hker : levelToSha r E n c = 0 ↔ levelIncl r E n c = 0 := by
    constructor
    · intro h
      exact congrArg (fun x : shaLevelK r E n => ((x : shaK r E) : H1 (galK r) E.PointCoeff)) h
    · intro h
      exact Subtype.ext (Subtype.ext h)
  rw [hker, ← AddMonoidHom.mem_ker, ← levelDelta_range]
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨QuotientAddGroup.mk P, Subtype.ext hP⟩
  · rintro ⟨P, hP⟩
    induction P using QuotientAddGroup.induction_on with
    | H P => exact ⟨P, congrArg Subtype.val hP⟩

/-- The image of finite torsion cohomology in point cohomology is the finite torsion.
Kind: PROVED; degree-one exactness of the coefficient Kummer sequence. -/
theorem levelIncl_range [E.IsElliptic] (n : ℕ) :
    (levelIncl r E n).range = AddSubgroup.torsionBy (H1 (galK r) E.PointCoeff) (2 ^ n : ℕ) := by
  have h := (levelSequence r E n).explicitLongExact_H1B
  have hp : explicitCoeff1 (galK r) E.PointCoeff
      (levelSequence r E n).projDistribMulActionHom continuous_of_discreteTopology =
      nsmulAddMonoidHom (α := H1 (galK r) E.PointCoeff) (2 ^ n) := by
    apply AddMonoidHom.ext
    intro c
    exact explicitCoeff1_eq_nsmul (galK r) E.PointCoeff
      (levelSequence r E n).projDistribMulActionHom continuous_of_discreteTopology
      (fun P => rfl) c
  rw [hp] at h
  refine h.trans ?_
  ext c
  rw [AddMonoidHom.mem_ker, AddSubgroup.torsionBy.nsmul_iff]
  rfl

/-- Every class of `Ш(E/K)[2^n]` lifts to the finite Selmer group.
Kind: PROVED; the right end of Silverman X.4.2. -/
theorem levelToSha_surjective [E.IsElliptic] (n : ℕ) :
    Function.Surjective (levelToSha r E n) := by
  rintro ⟨⟨x, hx⟩, hxt⟩
  have hxt' : x ∈ AddSubgroup.torsionBy (H1 (galK r) E.PointCoeff) (2 ^ n : ℕ) :=
    AddSubgroup.torsionBy.nsmul_iff.2
      (congrArg Subtype.val (AddSubgroup.torsionBy.nsmul_iff.1 hxt))
  rw [← levelIncl_range] at hxt'
  obtain ⟨c, hc⟩ := hxt'
  refine ⟨⟨c, ?_⟩, Subtype.ext (Subtype.ext hc)⟩
  change levelIncl r E n c ∈ shaK r E
  rwa [hc]

end Limit

/-- **PRINT**: the literal finite-level exact sequence for `φ = [2^n]`, `E' = E`:
`0 → E(K)/2^n E(K) → Sel_{2^n}(E/K) → Ш(E/K)[2^n] → 0`, for `K = ℚ(√k)`.
All maps are the canonical finite Kummer and coefficient maps. Rational points
are realized as fixed geometric points; no direct-limit or divisibility claim is
part of this input. Kind: PRINT statement, proved below
(`silvermanX42TwoPowerLevelPrint`); Silverman, *The Arithmetic of Elliptic Curves*, second
edition, Theorem X.4.2(a), page 333. -/
def SilvermanX42TwoPowerLevelPrint : Prop :=
  ∀ (k : ℤ) (E : WeierstrassCurve ℚ) (hE : E.IsElliptic),
    letI := hE
    ∀ n : ℕ,
      Function.Injective (Limit.levelKummer (sqrtK k) E n) ∧
      Function.Exact (Limit.levelKummer (sqrtK k) E n) (Limit.levelToSha (sqrtK k) E n) ∧
      Function.Surjective (Limit.levelToSha (sqrtK k) E n)

/-- The finite PRINT is realized by the coefficient Kummer sequence and the
specified local conditions. Kind: PROVED; the cohomological proof of Silverman X.4.2. -/
theorem silvermanX42TwoPowerLevelPrint : SilvermanX42TwoPowerLevelPrint := by
  intro k E hE
  have := hE
  intro n
  exact ⟨Limit.levelKummer_injective (sqrtK k) E n,
    Limit.levelKummer_exact (sqrtK k) E n, Limit.levelToSha_surjective (sqrtK k) E n⟩

end ZInQ.Contrib.RC53Assist.DiskOrders
