import ZInQKernel.Contrib.RC53Assist.DiskOrders.Limit.SilvermanLevel

/-!
# Continuous cocycles and the two-power limit

A continuous cocycle on a compact group with values in a discrete two-primary
module has finite image. Its image is therefore killed by one power of two.
This realizes each two-primary cohomology class at a finite torsion level.
The coefficient inclusions preserve the specified local conditions.

Kinds: definitions and PROVED. Locators: the degree-one continuous cochain
complex, and the coefficient inclusions in Silverman X.4.2.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.DiskOrders.Limit

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Manuscript.RC53Assist.QuadraticDescent

/-- A finite set of two-primary elements has a common two-power exponent.
Kind: PROVED; finite-set induction. -/
theorem finite_twoPower_exponent {A : Type*} [AddCommGroup A]
    (s : Set A) (hs : s.Finite) (h : ∀ a ∈ s, ∃ n : ℕ, (2 ^ n) • a = 0) :
    ∃ n : ℕ, ∀ a ∈ s, (2 ^ n) • a = 0 := by
  classical
  revert h
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    intro h
    exact ⟨0, fun a ha => False.elim ha⟩
  | @insert a s ha hs ih =>
    intro h
    obtain ⟨m, hm⟩ := h a (Set.mem_insert a s)
    obtain ⟨n, hn⟩ := ih (fun b hb => h b (Set.mem_insert_of_mem a hb))
    refine ⟨m + n, fun b hb => ?_⟩
    rcases Set.mem_insert_iff.1 hb with rfl | hb
    · rw [pow_add, mul_smul, smul_comm (2 ^ m) (2 ^ n), hm, smul_zero]
    · rw [pow_add, mul_smul, hn b hb, smul_zero]

/-- A continuous two-primary-valued function on a compact space has bounded exponent.
Kind: PROVED; compact images in discrete spaces are finite. -/
theorem continuous_twoPower_exponent {X A : Type*} [TopologicalSpace X] [CompactSpace X]
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] (f : X → A)
    (hf : Continuous f) (h : ∀ x, ∃ n : ℕ, (2 ^ n) • f x = 0) :
    ∃ n : ℕ, ∀ x, (2 ^ n) • f x = 0 := by
  obtain ⟨n, hn⟩ := finite_twoPower_exponent (Set.range f)
    (isCompact_range hf).finite_of_discrete (by
      rintro a ⟨x, rfl⟩
      exact h x)
  exact ⟨n, fun x => hn _ ⟨x, rfl⟩⟩

/-- `G_K` is compact: it is an open, hence closed, subgroup of the absolute Galois group.
Kind: PROVED; compactness of closed subspaces. -/
theorem galK_compact (r : SeparableClosure ℚ) : CompactSpace (galK r) := by
  exact isCompact_iff_compactSpace.mp
    ((galK r).isClosed_of_isOpen (isOpen_galK r)).isCompact

variable (r : SeparableClosure ℚ) (E : WeierstrassCurve ℚ)

/-- The coefficient inclusion `E[2^n] → E[2^∞]`, restricted to `G_K`.
Kind: definition; the direct system of two-power torsion. -/
def levelCoeffToInfinite (n : ℕ) :
    E.TorsionCoeff (2 ^ n) →+[galK r] TwoPowerCoeff E :=
  { (torsionToTwoPower E n).toAddMonoidHom with
    map_smul' g P := (torsionToTwoPower E n).map_smul (g : AbsoluteGaloisGroup ℚ) P }

/-- The infinite coefficient inclusion, restricted to `G_K`.
Kind: definition; the two-primary coefficient Kummer sequence. -/
def infiniteCoeffIncl : TwoPowerCoeff E →+[galK r] E.PointCoeff :=
  { (twoPowerCoeffIncl E).toAddMonoidHom with
    map_smul' g P := (twoPowerCoeffIncl E).map_smul (g : AbsoluteGaloisGroup ℚ) P }

/-- The finite-to-infinite map on continuous first cohomology.
Kind: definition; functoriality of the coefficient inclusions. -/
def levelToInfinite (n : ℕ) :
    H1 (galK r) (E.TorsionCoeff (2 ^ n)) →+ H1 (galK r) (TwoPowerCoeff E) :=
  explicitCoeff1 (galK r) (E.TorsionCoeff (2 ^ n))
    (levelCoeffToInfinite r E n) continuous_of_discreteTopology

/-- Inclusion into point cohomology commutes with the finite-to-infinite maps.
Kind: PROVED; composition of coefficient inclusions. -/
theorem inclK_levelToInfinite (n : ℕ)
    (c : H1 (galK r) (E.TorsionCoeff (2 ^ n))) :
    inclK r E (levelToInfinite r E n c) = levelIncl r E n c := by
  change ((explicitCoeff1 (galK r) (TwoPowerCoeff E) (infiniteCoeffIncl r E)
    continuous_of_discreteTopology).comp (explicitCoeff1 (galK r)
      (E.TorsionCoeff (2 ^ n)) (levelCoeffToInfinite r E n)
        continuous_of_discreteTopology)) c = _
  rw [← explicitCoeff1_comp]
  rfl

/-- Every class in `H¹(G_K, E[2^∞])` comes from one finite torsion level.
Kind: PROVED; finite image of continuous cocycles and injective coefficient inclusion. -/
theorem infinite_class_from_level (y : H1 (galK r) (TwoPowerCoeff E)) :
    ∃ (n : ℕ) (c : H1 (galK r) (E.TorsionCoeff (2 ^ n))), levelToInfinite r E n c = y := by
  have := galK_compact r
  induction y using QuotientAddGroup.induction_on with
  | H c =>
    obtain ⟨n, hn⟩ := continuous_twoPower_exponent (c : galK r → TwoPowerCoeff E)
      (mem_Z1_iff.1 c.2).1 (fun g => by
        obtain ⟨n, hn⟩ := AddCommGroup.mem_primaryComponent.1 (c.1 g).2
        exact ⟨n, Subtype.ext hn⟩)
    let f : galK r → E.TorsionCoeff (2 ^ n) := fun g =>
      ⟨(c.1 g).1, AddSubgroup.torsionBy.nsmul_iff.2 (congrArg Subtype.val (hn g))⟩
    have hf : f ∈ Z1 (galK r) (E.TorsionCoeff (2 ^ n)) :=
      mem_Z1_of_injective_comp_mem_Z1
        (φ := (levelCoeffToInfinite r E n).toAddMonoidHom)
        (fun P Q h => Subtype.ext
          (congrArg (fun x : TwoPowerCoeff E => (x : E.PointCoeff)) h))
        (fun g P => (levelCoeffToInfinite r E n).map_smul g P)
        (fun g => Subtype.ext rfl) c.2
    refine ⟨n, (⟨f, hf⟩ : Z1 (galK r) (E.TorsionCoeff (2 ^ n))), ?_⟩
    rw [levelToInfinite, explicitCoeff1_mk]
    apply congrArg (fun z : Z1 (galK r) (TwoPowerCoeff E) =>
      (z : H1 (galK r) (TwoPowerCoeff E)))
    apply Subtype.ext
    funext g
    exact Subtype.ext rfl

/-- Continuous first cohomology with these coefficients is itself two-primary.
Kind: PROVED; the finite-level realization and exponent inheritance. -/
theorem infinite_class_twoPrimary (y : H1 (galK r) (TwoPowerCoeff E)) :
    ∃ n : ℕ, (2 ^ n) • y = 0 := by
  obtain ⟨n, c, rfl⟩ := infinite_class_from_level r E y
  refine ⟨n, ?_⟩
  rw [← map_nsmul, nsmul_H1_eq_zero (fun P => AddSubgroup.torsionBy.nsmul P), map_zero]

/-- The finite coefficient inclusion sends finite Selmer classes to infinite Selmer classes.
Kind: PROVED; compatibility with the same local-triviality condition. -/
theorem levelToInfinite_mem_selmer {n : ℕ}
    {c : H1 (galK r) (E.TorsionCoeff (2 ^ n))} (hc : c ∈ selmerLevelK r E n) :
    levelToInfinite r E n c ∈ selmerK r E := by
  change inclK r E (levelToInfinite r E n c) ∈ shaK r E
  rw [inclK_levelToInfinite]
  exact hc

/-- Every infinite Selmer class comes from a finite Selmer level.
Kind: PROVED; finite cocycle image, with all local conditions retained. -/
theorem selmer_class_from_level (y : selmerK r E) :
    ∃ (n : ℕ) (c : selmerLevelK r E n), levelToInfinite r E n c = y.1 := by
  obtain ⟨n, c, hc⟩ := infinite_class_from_level r E y.1
  have hcS : c ∈ selmerLevelK r E n := by
    change levelIncl r E n c ∈ shaK r E
    rw [← inclK_levelToInfinite, hc]
    exact y.2
  exact ⟨n, ⟨c, hcS⟩, hc⟩

end ZInQ.Contrib.RC53Assist.DiskOrders.Limit
