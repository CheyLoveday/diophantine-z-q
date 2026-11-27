import Mathlib

/-!
# Frobenius generation over a prime field

The finite theorem identifies every automorphism with a power of Frobenius.
The infinite theorem uses the closed-subgroup fixed-field correspondence:
an element fixed by Frobenius satisfies `x ^ p = x` and belongs to the prime field.

Kinds: definitions and proved statements only.
Locator: Serre, *Local Fields*, I, §8, and the infinite Galois correspondence.
This book is not the chapter in Cassels--Fröhlich with the same author.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

/-- **PROVED**: a subgroup containing Frobenius in a finite field extension is all
of the automorphism group. Locator: finite-field Frobenius generation. -/
theorem finite_frobenius_subgroup_eq_top (k L : Type*) [Field k] [Fintype k]
    [Field L] [Finite L] [Algebra k L] (H : Subgroup (L ≃ₐ[k] L))
    (hF : FiniteField.frobeniusAlgEquivOfAlgebraic k L ∈ H) : H = ⊤ := by
  apply top_unique
  intro σ _
  obtain ⟨n, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2 σ
  exact H.pow_mem hF n.val

/-- **PROVED**: every algebraic extension of a finite field is Galois.
Locator: every finite simple subextension is a finite field and is Galois. -/
theorem finiteField_isGalois_algebraic (k L : Type*) [Field k] [Finite k]
    [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] : IsGalois k L := by
  have hnormal : Normal k L := by
    refine { toIsAlgebraic := inferInstance, splits' := ?_ }
    intro x
    let E := IntermediateField.adjoin k ({x} : Set L)
    haveI : FiniteDimensional k E :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    haveI : Finite E := Module.finite_of_finite k
    haveI : IsGalois k E := inferInstance
    let y : E := IntermediateField.AdjoinSimple.gen k x
    have hm : minpoly k y = minpoly k x :=
      (minpoly.algHom_eq E.val E.val.injective y).symm
    have hs := (IsGalois.splits k y).map (algebraMap E L)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, hm] at hs
    exact hs
  exact { to_isSeparable := inferInstance, to_normal := hnormal }

/-- **PROVED**: in a Galois extension of the prime field, a closed subgroup
containing the `p`-power automorphism is all of the Galois group.
Locator: Serre, *Local Fields*, I, §8; the closed-subgroup Galois correspondence. -/
theorem primeField_closed_subgroup_eq_top (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra (ZMod p) L] [IsGalois (ZMod p) L]
    (φ : L ≃ₐ[ZMod p] L) (hφ : ∀ x : L, φ x = x ^ p)
    (H : Subgroup (L ≃ₐ[ZMod p] L)) (hH : IsClosed (H : Set (L ≃ₐ[ZMod p] L)))
    (hF : φ ∈ H) : H = ⊤ := by
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  let C : ClosedSubgroup (L ≃ₐ[ZMod p] L) := ⟨H, hH⟩
  have hfixed : IntermediateField.fixedField H = ⊥ := by
    apply bot_unique
    intro x hx
    have hxF : φ x = x := by
      rw [IntermediateField.mem_fixedField_iff] at hx
      exact hx φ hF
    rw [hφ] at hxF
    have hx0 : x ∈ (⊥ : Subfield L) :=
      (Subfield.mem_bot_iff_pow_eq_self L p).mpr hxF
    obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p L).mp hx0
    apply IntermediateField.mem_bot.mpr
    exact ⟨(n : ZMod p), by simpa only [map_intCast] using hn⟩
  have hcor := InfiniteGalois.fixingSubgroup_fixedField C
  change (IntermediateField.fixedField H).fixingSubgroup = H at hcor
  rw [hfixed, IntermediateField.fixingSubgroup_bot] at hcor
  exact hcor.symm

/-- **PROVED**: the same conclusion for an open subgroup; normality is not required.
Locator: open subgroups of topological groups are closed. -/
theorem primeField_open_subgroup_eq_top (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra (ZMod p) L] [IsGalois (ZMod p) L]
    (φ : L ≃ₐ[ZMod p] L) (hφ : ∀ x : L, φ x = x ^ p)
    (H : Subgroup (L ≃ₐ[ZMod p] L)) (hH : IsOpen (H : Set (L ≃ₐ[ZMod p] L)))
    (hF : φ ∈ H) : H = ⊤ :=
  primeField_closed_subgroup_eq_top p L φ hφ H (H.isClosed_of_isOpen hH) hF

/-- **PROVED NON-VACUITY**: the arithmetic Frobenius exists on the algebraic
closure of every prime field. Locator: algebraic-extension Frobenius. -/
theorem primeField_frobenius_nonvacuity (p : ℕ) [Fact p.Prime] :
    ∃ φ : AlgebraicClosure (ZMod p) ≃ₐ[ZMod p] AlgebraicClosure (ZMod p),
      ∀ x, φ x = x ^ p := by
  refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) _, ?_⟩
  intro x
  change x ^ Fintype.card (ZMod p) = x ^ p
  rw [ZMod.card]

/-- **PROVED NON-VACUITY**: the open-subgroup hypotheses are realized over the
algebraic closure, rather than over a trivial field. Locator: Frobenius above. -/
theorem primeField_open_subgroup_nonvacuity (p : ℕ) [Fact p.Prime] :
    ∃ (φ : AlgebraicClosure (ZMod p) ≃ₐ[ZMod p] AlgebraicClosure (ZMod p))
      (H : Subgroup (AlgebraicClosure (ZMod p) ≃ₐ[ZMod p] AlgebraicClosure (ZMod p))),
      (∀ x, φ x = x ^ p) ∧
        IsOpen (H : Set (AlgebraicClosure (ZMod p) ≃ₐ[ZMod p]
          AlgebraicClosure (ZMod p))) ∧ φ ∈ H := by
  obtain ⟨φ, hφ⟩ := primeField_frobenius_nonvacuity p
  exact ⟨φ, ⊤, hφ, isOpen_univ, Subgroup.mem_top φ⟩

end ZInQ.Contrib.RC53Assist.TateCurve
