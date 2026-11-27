import ZInQKernel.Contrib.CloudB3E1Torsion.ConeContraction
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18RetainedChain

/-!
# The comparison of two models lifted to the augmented complexes

Manuscript `diophantine_zq.tex`, tex 3877–3892 and 4189–4193. Lemma `ex:arith-common-coordinate`
compares the coordinate of `[z] ⊗ [λ]` in two homotopy equivalent finite free models.

Let `E : HEMat R …` be exact homotopy-equivalence data `f : A ⇄ B : g` between two four-term
models, with homotopies `h_A`, `h_B`. Take a cycle `z` of `A` and a closed functional `λ` on `A`.
The transported class is `f₁ z` and the transported functional is `λ g₂`. This file lifts `E` to
the augmented complexes `aug(A, z, λ)` and `aug(B, f₁ z, λ g₂)`:
* **`augF`** (definition): `f` extended by `1` on the augmentation lines. Its degree-three
  augmentation row is `μ = λ h_{A,3}`, since `(λ g₂) f₂ = λ + μ d₂`.
* **`augG`** (definition): `g` extended by `1`. Its degree-zero augmentation column is
  `c = h_{A,1} z`, since `g₁ f₁ z = z + d₀ c`.
* **`augHomotopyData`** (definition): `HomotopyData (augF E hE z λ)` for lane E1's cone
  contraction. The homotopy `h_A` (extended by zero) is exact on `aug A`. The homotopy `h_B` leaves
  the square-zero errors `w = f₀ c − h_{B,1} f₁ z` (degree zero) and `r = μ g₃ − (λ g₂) h_{B,3}`
  (degree three).
* `torsion_cone_augF_isUnit` (PROVED): over a domain, the torsion of the cone of `augF` is a
  unit.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC.Wiring (HEMat matIn_bot_iff)

variable {R : Type} [CommRing R] {A0 A1 A2 A3 B0 B1 B2 B3 : Type} [Fintype A0] [Fintype A1]
  [Fintype A2] [Fintype A3] [Fintype B0] [Fintype B1] [Fintype B2] [Fintype B3] [DecidableEq A0]
  [DecidableEq A1] [DecidableEq A2] [DecidableEq A3] [DecidableEq B0] [DecidableEq B1]
  [DecidableEq B2] [DecidableEq B3]
  (E : HEMat R A0 A1 A2 A3 B0 B1 B2 B3) (hE : E.Holds ⊥)

/-! ### The identities of exact data -/

section Identities

include hE

theorem he_f0 : E.f1 * E.dA0 = E.dB0 * E.f0 := sub_eq_zero.mp ((matIn_bot_iff _).1 hE.hf0)
theorem he_f1 : E.f2 * E.dA1 = E.dB1 * E.f1 := sub_eq_zero.mp ((matIn_bot_iff _).1 hE.hf1)
theorem he_f2 : E.f3 * E.dA2 = E.dB2 * E.f2 := sub_eq_zero.mp ((matIn_bot_iff _).1 hE.hf2)
theorem he_g0 : E.g1 * E.dB0 = E.dA0 * E.g0 := sub_eq_zero.mp ((matIn_bot_iff _).1 hE.hg0)
theorem he_g1 : E.g2 * E.dB1 = E.dA1 * E.g1 := sub_eq_zero.mp ((matIn_bot_iff _).1 hE.hg1)
theorem he_g2 : E.g3 * E.dB2 = E.dA2 * E.g2 := sub_eq_zero.mp ((matIn_bot_iff _).1 hE.hg2)
theorem he_hA0 : E.g0 * E.f0 = 1 + E.hA1 * E.dA0 := by
  have := (matIn_bot_iff _).1 hE.hhA0; rw [sub_sub, sub_eq_zero] at this; exact this
theorem he_hA1 : E.g1 * E.f1 = 1 + (E.dA0 * E.hA1 + E.hA2 * E.dA1) := by
  have := (matIn_bot_iff _).1 hE.hhA1; rw [sub_sub, sub_eq_zero] at this; exact this
theorem he_hA2 : E.g2 * E.f2 = 1 + (E.dA1 * E.hA2 + E.hA3 * E.dA2) := by
  have := (matIn_bot_iff _).1 hE.hhA2; rw [sub_sub, sub_eq_zero] at this; exact this
theorem he_hA3 : E.g3 * E.f3 = 1 + E.dA2 * E.hA3 := by
  have := (matIn_bot_iff _).1 hE.hhA3; rw [sub_sub, sub_eq_zero] at this; exact this
theorem he_hB0 : E.f0 * E.g0 = 1 + E.hB1 * E.dB0 := by
  have := (matIn_bot_iff _).1 hE.hhB0; rw [sub_sub, sub_eq_zero] at this; exact this
theorem he_hB1 : E.f1 * E.g1 = 1 + (E.dB0 * E.hB1 + E.hB2 * E.dB1) := by
  have := (matIn_bot_iff _).1 hE.hhB1; rw [sub_sub, sub_eq_zero] at this; exact this
theorem he_hB2 : E.f2 * E.g2 = 1 + (E.dB1 * E.hB2 + E.hB3 * E.dB2) := by
  have := (matIn_bot_iff _).1 hE.hhB2; rw [sub_sub, sub_eq_zero] at this; exact this
theorem he_hB3 : E.f3 * E.g3 = 1 + E.dB2 * E.hB3 := by
  have := (matIn_bot_iff _).1 hE.hhB3; rw [sub_sub, sub_eq_zero] at this; exact this

end Identities

/-! ### The augmented maps -/

variable {z : A1 → R} {lam : A2 → R} (hz : E.dA1 *ᵥ z = 0) (hlam : lam ᵥ* E.dA1 = 0)

/-- The source augmented complex `aug(A, z, λ)`. Kind: definition. -/
abbrev augA := ((E.cxA hE).aug z lam hz hlam).toBased

/-- The target augmented complex `aug(B, f₁ z, λ g₂)`. Kind: definition. -/
abbrev augB := ((E.cxB hE).aug (E.f1 *ᵥ z) (lam ᵥ* E.g2) (E.transport_cycle hE hz)
  (E.transport_closed hE hlam)).toBased

/-- The degree-three correction `μ = λ h_{A,3}`. Kind: definition. -/
abbrev muA (lam : A2 → R) : A3 → R := lam ᵥ* E.hA3

/-- The degree-zero correction `c = h_{A,1} z`. Kind: definition. -/
abbrev cA (z : A1 → R) : A0 → R := E.hA1 *ᵥ z

include hE hlam in
/-- `(λ g₂) f₂ = λ + μ d₂`. Kind: PROVED. -/
theorem lam_g2_f2 : (lam ᵥ* E.g2) ᵥ* E.f2 = muA E lam ᵥ* E.dA2 + lam := by
  rw [vecMul_vecMul, he_hA2 E hE, vecMul_add, vecMul_add, vecMul_one, ← vecMul_vecMul, hlam,
    zero_vecMul, ← vecMul_vecMul]
  abel

include hE hz in
/-- `g₁ f₁ z = d₀ c + z`. Kind: PROVED. -/
theorem g1_f1_z : E.g1 *ᵥ (E.f1 *ᵥ z) = E.dA0 *ᵥ cA E z + z := by
  rw [mulVec_mulVec, he_hA1 E hE, add_mulVec, add_mulVec, one_mulVec,
    show (E.hA2 * E.dA1) *ᵥ z = E.hA2 *ᵥ (E.dA1 *ᵥ z) from (mulVec_mulVec _ _ _).symm, hz,
    mulVec_zero, add_zero,
    show (E.dA0 * E.hA1) *ᵥ z = E.dA0 *ᵥ (E.hA1 *ᵥ z) from (mulVec_mulVec _ _ _).symm]
  abel

/-- **`f` on the augmented complexes**. Kind: definition (PROVED fields). -/
def augF : ChainMapR (augA E hE hz hlam) (augB E hE hz hlam) where
  fE := fromBlocks (fromBlocks E.f0 0 0 1) 0 0 E.f2
  fO := fromBlocks E.f1 0 0 (fromBlocks E.f3 0 (replicateRow Unit (muA E lam)) 1)
  deg_fE := by
    rintro ((i | i) | i) ((j | j) | j) h
    all_goals first | rfl | exact absurd (by simp) h
  deg_fO := by
    rintro (i | (i | i)) (j | (j | j)) h
    all_goals first | rfl | exact absurd (by simp) h
  commOE := by
    have h1 := he_f0 E hE
    have h2 := he_f2 E hE
    have hv := lam_g2_f2 E hE hlam
    ext i j
    rcases i with i | (i | i) <;> rcases j with (j | j) | j <;>
      simp [FourCx.toBased_dOE, FourCx.aug, HEMat.cxA, HEMat.cxB, mul_apply,
        Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, fromRows_apply_inl,
        fromRows_apply_inr, replicateCol, replicateRow, mulVec, vecMul, dotProduct]
    all_goals first
      | simpa [mul_apply] using (congrFun (congrFun h1 i) j).symm
      | simpa [mul_apply] using (congrFun (congrFun h2 i) j).symm
      | (have hj := congrFun hv j
         simp only [muA, vecMul, dotProduct, Pi.add_apply] at hj
         exact hj)
  commEO := by
    have h1 := he_f1 E hE
    ext i j
    rcases i with (i | i) | i <;> rcases j with j | (j | j) <;>
      simp [FourCx.toBased_dEO, FourCx.aug, HEMat.cxA, HEMat.cxB, mul_apply,
        Fintype.sum_sum_type]
    all_goals simpa [mul_apply] using (congrFun (congrFun h1 i) j).symm

/-- **`g` on the augmented complexes**. Kind: definition (PROVED fields). -/
def augG : ChainMapR (augB E hE hz hlam) (augA E hE hz hlam) where
  fE := fromBlocks (fromBlocks E.g0 (replicateCol Unit (cA E z)) 0 1) 0 0 E.g2
  fO := fromBlocks E.g1 0 0 (fromBlocks E.g3 0 0 1)
  deg_fE := by
    rintro ((i | i) | i) ((j | j) | j) h
    all_goals first | rfl | exact absurd (by simp) h
  deg_fO := by
    rintro (i | (i | i)) (j | (j | j)) h
    all_goals first | rfl | exact absurd (by simp) h
  commOE := by
    have h1 := he_g0 E hE
    have h2 := he_g2 E hE
    have hv := g1_f1_z E hE hz
    ext i j
    rcases i with i | (i | i) <;> rcases j with (j | j) | j <;>
      simp [FourCx.toBased_dOE, FourCx.aug, HEMat.cxA, HEMat.cxB, mul_apply,
        Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, fromRows_apply_inl,
        fromRows_apply_inr, replicateCol, replicateRow, mulVec, vecMul, dotProduct]
    all_goals first
      | simpa [mul_apply] using (congrFun (congrFun h1 i) j).symm
      | simpa [mul_apply] using (congrFun (congrFun h2 i) j).symm
      | (have hi := congrFun hv i
         simp only [cA, mulVec, dotProduct, Pi.add_apply] at hi
         exact hi.symm)
  commEO := by
    have h1 := he_g1 E hE
    ext i j
    rcases i with (i | i) | i <;> rcases j with j | (j | j) <;>
      simp [FourCx.toBased_dEO, FourCx.aug, HEMat.cxA, HEMat.cxB, mul_apply,
        Fintype.sum_sum_type]
    all_goals simpa [mul_apply] using (congrFun (congrFun h1 i) j).symm

/-- The degree-zero error `w = f₀ c − h_{B,1} f₁ z`. Kind: definition. -/
abbrev errW (z : A1 → R) : B0 → R := E.f0 *ᵥ cA E z - E.hB1 *ᵥ (E.f1 *ᵥ z)

/-- The degree-three error `r = μ g₃ − (λ g₂) h_{B,3}`. Kind: definition. -/
abbrev errR (lam : A2 → R) : B3 → R := muA E lam ᵥ* E.g3 - (lam ᵥ* E.g2) ᵥ* E.hB3

/-- **The homotopy data of the augmented comparison** (tex 4189–4193): `g` on the augmented
complexes, `h_A` extended by zero (exact), `h_B` extended by zero with the square-zero errors `w`
and `r`. Kind: definition (PROVED fields). -/
def augHomotopyData : HomotopyData (augF E hE hz hlam) where
  g := augG E hE hz hlam
  kCOE := fromBlocks 0 E.hA2 0 0
  kCEO := fromBlocks (fromRows E.hA1 0) 0 0 (fromCols E.hA3 0)
  deg_kCOE := by
    rintro (i | (i | i)) ((j | j) | j) h
    all_goals first | rfl | exact absurd (by simp) h
  deg_kCEO := by
    rintro ((i | i) | i) (j | (j | j)) h
    all_goals first | rfl | exact absurd (by simp) h
  gfE := by
    have h0 := he_hA0 E hE
    have h2 := he_hA2 E hE
    ext i j
    rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
      simp [augF, augG, FourCx.toBased_dOE, FourCx.toBased_dEO, FourCx.aug, HEMat.cxA,
        mul_apply, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr,
        fromRows_apply_inl, fromRows_apply_inr, replicateCol, replicateRow, mulVec, vecMul,
        dotProduct, one_apply]
    all_goals first
      | simpa [mul_apply, one_apply, add_assoc] using congrFun (congrFun h0 i) j
      | simpa [mul_apply, one_apply, add_assoc] using congrFun (congrFun h2 i) j
  gfO := by
    have h1 := he_hA1 E hE
    have h3 := he_hA3 E hE
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [augF, augG, FourCx.toBased_dOE, FourCx.toBased_dEO, FourCx.aug, HEMat.cxA,
        mul_apply, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr,
        fromRows_apply_inl, fromRows_apply_inr, replicateCol, replicateRow, mulVec, vecMul,
        dotProduct, one_apply]
    all_goals first
      | simpa [mul_apply, one_apply, add_assoc] using congrFun (congrFun h1 i) j
      | simpa [mul_apply, one_apply, add_assoc] using congrFun (congrFun h3 i) j
  kDOE := fromBlocks 0 E.hB2 0 0
  kDEO := fromBlocks (fromRows E.hB1 0) 0 0 (fromCols E.hB3 0)
  deg_kDOE := by
    rintro (i | (i | i)) ((j | j) | j) h
    all_goals first | rfl | exact absurd (by simp) h
  deg_kDEO := by
    rintro ((i | i) | i) (j | (j | j)) h
    all_goals first | rfl | exact absurd (by simp) h
  errE := fromBlocks (fromBlocks 0 (replicateCol Unit (errW E z)) 0 0) 0 0 0
  errO := fromBlocks 0 0 0 (fromBlocks 0 0 (replicateRow Unit (errR E lam)) 0)
  fgE := by
    have h0 := he_hB0 E hE
    have h2 := he_hB2 E hE
    ext i j
    rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
      simp [augF, augG, FourCx.toBased_dOE, FourCx.toBased_dEO, FourCx.aug,
        HEMat.cxB, mul_apply, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr,
        fromRows_apply_inl, fromRows_apply_inr, replicateCol, replicateRow, mulVec, vecMul,
        dotProduct, one_apply]
    all_goals first
      | simpa [mul_apply, one_apply, add_assoc] using congrFun (congrFun h0 i) j
      | simpa [mul_apply, one_apply, add_assoc] using congrFun (congrFun h2 i) j
  fgO := by
    have h1 := he_hB1 E hE
    have h3 := he_hB3 E hE
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [augF, augG, FourCx.toBased_dOE, FourCx.toBased_dEO, FourCx.aug,
        HEMat.cxB, mul_apply, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr,
        fromRows_apply_inl, fromRows_apply_inr, replicateCol, replicateRow, mulVec, vecMul,
        dotProduct, one_apply]
    all_goals first
      | simpa [mul_apply, one_apply, add_assoc] using congrFun (congrFun h1 i) j
      | simpa [mul_apply, one_apply, add_assoc] using congrFun (congrFun h3 i) j
  errE_sq := by
    ext i j
    rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
      simp [mul_apply, Fintype.sum_sum_type, replicateCol]
  errO_sq := by
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [mul_apply, Fintype.sum_sum_type, replicateRow]

/-- **The torsion of the cone of the augmented comparison is a unit** (over a domain).
Kind: PROVED. -/
theorem isUnit_torsion_cone_augF [IsDomain R]
    (σ : ((B0 ⊕ Unit) ⊕ B2) ⊕ (A1 ⊕ (A3 ⊕ Unit)) ≃ (B1 ⊕ (B3 ⊕ Unit)) ⊕ ((A0 ⊕ Unit) ⊕ A2)) :
    IsUnit (torsion (BasedCx.coneR (augF E hE hz hlam)) σ) :=
  isUnit_torsion_coneR (augHomotopyData E hE hz hlam) σ

end ZInQ.Contrib.CloudB3E1Torsion
