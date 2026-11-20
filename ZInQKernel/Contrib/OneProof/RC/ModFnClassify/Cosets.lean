import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Coset.Card
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_card_projectiveLine_zmod

/-! The right cosets used in the analytic orbit polynomial. Provenance (c). -/

noncomputable section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
open ModularCurve

namespace ZInQ.Manuscript.RC.ModFnClassify

abbrev LevelCosets (N : ℕ) :=
  Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 N))

private def lowerRow (N : ℕ) (A : SL(2, ℤ)) : UnimodularRow (ZMod N) :=
  ⟨((A 1 0 : ZMod N), (A 1 1 : ZMod N)), by
    refine ⟨(-(A 0 1 : ZMod N)), (A 0 0 : ZMod N), ?_⟩
    have hd := congrArg (Int.castRingHom (ZMod N)) A.property
    simp only [det_fin_two, map_sub, map_mul, map_one] at hd
    linear_combination hd⟩

private theorem lowerRow_rel_iff (N : ℕ) (A B : SL(2, ℤ)) :
    unimodularRowSetoid (ZMod N) (lowerRow N A) (lowerRow N B) ↔
      B * A⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  constructor
  · rintro ⟨u, h0, h1⟩
    change (u : ZMod N) * (A 1 0 : ZMod N) = (B 1 0 : ZMod N) at h0
    change (u : ZMod N) * (A 1 1 : ZMod N) = (B 1 1 : ZMod N) at h1
    rw [CongruenceSubgroup.Gamma0_mem]
    simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_inv, adjugate_fin_two,
      Int.cast_add, Int.cast_mul, Fin.isValue]
    change (B 1 0 : ZMod N) * (A 1 1 : ZMod N) +
      (B 1 1 : ZMod N) * ((-(A 1 0) : ℤ) : ZMod N) = 0
    rw [Int.cast_neg]
    rw [← h0, ← h1]
    ring
  · intro h
    let C := B * A⁻¹
    have hC : C * A = B := inv_mul_cancel_right B A
    have hz : (C 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.mp h
    have hd := congrArg (Int.castRingHom (ZMod N)) C.property
    simp only [det_fin_two, map_sub, map_mul, map_one] at hd
    change (C 0 0 : ZMod N) * (C 1 1 : ZMod N) -
      (C 0 1 : ZMod N) * (C 1 0 : ZMod N) = 1 at hd
    rw [hz, mul_zero, sub_zero, mul_comm] at hd
    let u := Units.mkOfMulEqOne (C 1 1 : ZMod N) (C 0 0 : ZMod N) hd
    refine ⟨u, ?_, ?_⟩
    all_goals
      change (C 1 1 : ZMod N) * (A 1 _ : ZMod N) = (B 1 _ : ZMod N)
      rw [← hC]
      simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul, hz,
        zero_mul, zero_add, Fin.isValue]

/-- Reduction of the bottom row modulo `N` injects the right cosets
of `Γ₀(N)` into the projective line over `ℤ/Nℤ`. -/
def cosetsToProjectiveLine (N : ℕ) : LevelCosets N ↪ ProjectiveLine (ZMod N) where
  toFun := Quotient.map (lowerRow N) fun A B h =>
    (lowerRow_rel_iff N A B).mpr (QuotientGroup.rightRel_apply.mp h)
  inj' := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | _ A =>
      induction b using Quotient.inductionOn with
      | _ B =>
        exact Quotient.sound (QuotientGroup.rightRel_apply.mpr
          ((lowerRow_rel_iff N A B).mp (Quotient.exact hab)))

instance finiteLevelCosets (N : ℕ) [NeZero N] : Finite (LevelCosets N) :=
  Finite.of_injective _ (cosetsToProjectiveLine N).injective

/-- At most `ψ(N)` factors occur in the orbit polynomial. This is the
direction of the index computation needed for the field degree bound. -/
theorem card_levelCosets_le (N : ℕ) [NeZero N] :
    Nat.card (LevelCosets N) ≤ dedekindPsi N := by
  rw [← card_projectiveLine_zmod N (NeZero.ne N)]
  exact Nat.card_le_card_of_injective _ (cosetsToProjectiveLine N).injective

#print axioms lowerRow_rel_iff
#print axioms card_levelCosets_le

end ZInQ.Manuscript.RC.ModFnClassify
