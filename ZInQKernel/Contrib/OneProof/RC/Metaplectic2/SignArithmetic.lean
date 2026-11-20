import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Relations
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-! The scalar Hilbert signs in tex 8691–8722 and 8761–8787.
We use the explicit valuation and residue formulas (on-the-spot (c)),
without taking a norm-form index theorem as an input. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Visibility WeilIndex GaussSign

private def bitExp (x : ZMod 2) : ZMod 8 := if x = 0 then 0 else 4

private theorem bitExp_add (x y : ZMod 2) : bitExp (x + y) = bitExp x + bitExp y := by
  fin_cases x <;> fin_cases y <;> decide

private theorem bitExp_double (x : ZMod 2) : bitExp x + bitExp x = 0 := by
  fin_cases x <;> decide

private def characterBit (z : ℤ) : ZMod 2 := if z = -1 then 1 else 0

private theorem characterBit_mul {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    characterBit (x * y) = characterBit x + characterBit y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

private def parity (p : Place) (x : ℚ_[p.val]ˣ) : ZMod 2 := valAt p x

private theorem parity_mul (p : Place) (x y : ℚ_[p.val]ˣ) :
    parity p (x * y) = parity p x + parity p y := by
  simp [parity, valAt_mul]

private theorem parity_zero_iff (p : Place) (x : ℚ_[p.val]ˣ) :
    parity p x = 0 ↔ valAt p x % 2 = 0 := by
  rw [parity, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.dvd_iff_emod_eq_zero

private theorem valAt_neg_one (p : Place) : valAt p (-1) = 0 := by
  change ((-1 : ℤ) : ℚ_[p.val]).valuation = 0
  rw [Padic.valuation_intCast]
  simp [padicValInt]

private theorem parity_neg_one (p : Place) : parity p (-1) = 0 := by
  simp [parity, valAt_neg_one]

private theorem unitAt_one (p : Place) : unitAt p 1 = 1 := by
  apply Units.ext
  apply Subtype.ext
  simp [unitAt_coe, valAt]

private theorem unitAt_neg_one (p : Place) : unitAt p (-1) = -1 := by
  apply Units.ext
  apply Subtype.ext
  simp [unitAt_coe, valAt_neg_one]

private def oddBit (p : Place) (x : ℚ_[p.val]ˣ) : ZMod 2 :=
  characterBit (quadraticChar (ZMod p.val) (oddUnitResidue p x : ZMod p.val))

private def oddPrimeBit (p : Place) : ZMod 2 := characterBit (ZMod.χ₄ (p.val : ZMod 4))

private theorem oddBit_mul (p : Place) (x y : ℚ_[p.val]ˣ) :
    oddBit p (x * y) = oddBit p x + oddBit p y := by
  rw [oddBit, oddUnitResidue_mul, Units.val_mul, map_mul]
  exact characterBit_mul (quadraticChar_dichotomy (oddUnitResidue p x).ne_zero)
    (quadraticChar_dichotomy (oddUnitResidue p y).ne_zero)

private theorem oddBit_neg_one (p : Place) (hp : p ≠ dyadicPlace) :
    oddBit p (-1) = oddPrimeBit p := by
  have hp₂ : p.val ≠ 2 := fun h => hp (Subtype.ext h)
  have h : ringChar (ZMod p.val) ≠ 2 := by simpa [ZMod.ringChar_zmod_n] using hp₂
  unfold oddBit oddPrimeBit oddUnitResidue
  rw [unitAt_neg_one]
  change characterBit (quadraticChar (ZMod p.val) (PadicInt.toZMod (-1))) = _
  simp [quadraticChar_neg_one h, ZMod.card]

private def oddTable (k e z : ZMod 2) : ZMod 8 :=
  if e = 0 then 0 else (if k = 0 then 0 else 6) + bitExp z

private theorem oddTable_defect (k e f x y : ZMod 2) :
    oddTable k e x + oddTable k f y - oddTable k (e + f) (x + y) =
      bitExp (e * f * k + e * y + f * x) := by
  fin_cases k <;> fin_cases e <;> fin_cases f <;> fin_cases x <;> fin_cases y <;> decide

private theorem oddTable_neg (k e x : ZMod 2) :
    oddTable k e (k + x) = -oddTable k e x := by
  fin_cases k <;> fin_cases e <;> fin_cases x <;> decide

private theorem oddExponent_table (p : Place) (x : ℚ_[p.val]ˣ) :
    oddExponent p x = oddTable (oddPrimeBit p) (parity p x) (oddBit p x) := by
  simp [oddExponent, oddTable, parity_zero_iff, oddBase, oddBit, oddPrimeBit, characterBit,
    bitExp, signExponent]

private def dyadicFour (u : ZMod 8) : ZMod 2 := characterBit (ZMod.χ₄ (ZMod.cast u))
private def dyadicEight (u : ZMod 8) : ZMod 2 := characterBit (ZMod.χ₈ u)

private theorem dyadicFour_mul (x y : ZMod 8) (hx : x.val % 2 = 1) (hy : y.val % 2 = 1) :
    dyadicFour (x * y) = dyadicFour x + dyadicFour y := by
  revert hx hy
  fin_cases x <;> fin_cases y <;> decide

private theorem dyadicEight_mul (x y : ZMod 8) (hx : x.val % 2 = 1) (hy : y.val % 2 = 1) :
    dyadicEight (x * y) = dyadicEight x + dyadicEight y := by
  revert hx hy
  fin_cases x <;> fin_cases y <;> decide

private def dyadicTable (e : ZMod 2) (x : ZMod 8) : ZMod 8 :=
  dyadicExponent (decide (e ≠ 0)) x

private theorem dyadicTable_defect (e f : ZMod 2) (x y : ZMod 8)
    (hx : x.val % 2 = 1) (hy : y.val % 2 = 1) :
    dyadicTable e x + dyadicTable f y - dyadicTable 0 1 -
      dyadicTable (e + f) (x * y) =
      bitExp (dyadicFour x * dyadicFour y + e * dyadicEight y + f * dyadicEight x) := by
  revert hx hy
  fin_cases e <;> fin_cases f <;> fin_cases x <;> fin_cases y <;> decide

private theorem dyadicTable_neg (e : ZMod 2) (x : ZMod 8) (hx : x.val % 2 = 1) :
    dyadicTable e (-x) = -dyadicTable e x := by
  revert hx
  fin_cases e <;> fin_cases x <;> decide

private theorem dyadic_residue_odd (x : ℚ_[dyadicPlace.val]ˣ) :
    (dyadicUnitResidue x : ZMod 8).val % 2 = 1 := by
  have h := ((dyadicUnitResidue x).isUnit.map
    (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2))).ne_zero
  change (ZMod.cast (dyadicUnitResidue x : ZMod 8) : ZMod 2) ≠ 0 at h
  generalize (dyadicUnitResidue x : ZMod 8) = u at h ⊢
  revert h
  fin_cases u <;> decide

private theorem dyadicExponent_table (x : ℚ_[dyadicPlace.val]ˣ) :
    finiteExponent dyadicPlace x = dyadicTable (parity dyadicPlace x) (dyadicUnitResidue x) := by
  simp [finiteExponent_dyadic, dyadicTable, parity_zero_iff]

/-- The Hilbert sign in eighth-root exponents, via the explicit local formulas.
At odd primes this uses valuation parities and the two Legendre symbols;
at two it uses the two unit characters modulo four and eight. -/
def hilbertExponent (p : Place) (x y : ℚ_[p.val]ˣ) : ZMod 8 :=
  if h : p = dyadicPlace then by
    subst p
    exact bitExp (dyadicFour (dyadicUnitResidue x) * dyadicFour (dyadicUnitResidue y) +
      parity dyadicPlace x * dyadicEight (dyadicUnitResidue y) +
      parity dyadicPlace y * dyadicEight (dyadicUnitResidue x))
  else bitExp (parity p x * parity p y * oddPrimeBit p +
    parity p x * oddBit p y + parity p y * oddBit p x)

private theorem hilbertExponent_dyadic (x y : ℚ_[dyadicPlace.val]ˣ) :
    hilbertExponent dyadicPlace x y =
      bitExp (dyadicFour (dyadicUnitResidue x) * dyadicFour (dyadicUnitResidue y) +
        parity dyadicPlace x * dyadicEight (dyadicUnitResidue y) +
        parity dyadicPlace y * dyadicEight (dyadicUnitResidue x)) := by
  rw [hilbertExponent, dite_eq_left (show dyadicPlace = dyadicPlace from rfl)]

def hilbertSign (p : Place) (x y : ℚ_[p.val]ˣ) : ℂˣ :=
  exponentRoot (hilbertExponent p x y)

theorem hilbertSign_cases (p : Place) (x y : ℚ_[p.val]ˣ) :
    hilbertSign p x y = 1 ∨ hilbertSign p x y = -1 := by
  unfold hilbertSign
  by_cases hp : p = dyadicPlace
  · subst p
    rw [hilbertExponent_dyadic]
    unfold bitExp
    split
    · exact Or.inl exponentRoot_zero
    · exact Or.inr zetaEight_pow_four
  · rw [hilbertExponent, dite_eq_right hp]
    unfold bitExp
    split
    · exact Or.inl exponentRoot_zero
    · exact Or.inr zetaEight_pow_four

theorem hilbertExponent_double (p : Place) (x y : ℚ_[p.val]ˣ) :
    hilbertExponent p x y + hilbertExponent p x y = 0 := by
  by_cases hp : p = dyadicPlace
  · subst p
    simp only [hilbertExponent_dyadic, bitExp_double]
  · simp only [hilbertExponent, dite_eq_right hp, bitExp_double]

theorem hilbertExponent_mul_left (p : Place) (x y z : ℚ_[p.val]ˣ) :
    hilbertExponent p (x * y) z = hilbertExponent p x z + hilbertExponent p y z := by
  by_cases hp : p = dyadicPlace
  · subst p
    simp only [hilbertExponent_dyadic]
    rw [dyadicUnitResidue_mul x y, Units.val_mul, parity_mul dyadicPlace x y,
      dyadicFour_mul _ _ (dyadic_residue_odd x) (dyadic_residue_odd y),
      dyadicEight_mul _ _ (dyadic_residue_odd x) (dyadic_residue_odd y)]
    rw [← bitExp_add]
    congr 1
    ring
  · simp only [hilbertExponent, dite_eq_right hp, parity_mul, oddBit_mul]
    rw [← bitExp_add]
    congr 1
    ring

theorem finiteExponent_defect (p : Place) (x y : ℚ_[p.val]ˣ) :
    finiteExponent p x + finiteExponent p y - finiteExponent p 1 -
      finiteExponent p (x * y) = hilbertExponent p x y := by
  by_cases hp : p = dyadicPlace
  · subst p
    simp only [hilbertExponent_dyadic, dyadicExponent_table]
    rw [parity_mul dyadicPlace x y, dyadicUnitResidue_mul x y, Units.val_mul]
    have h₁ : parity dyadicPlace 1 = 0 := by simp [parity, valAt]
    have h₂ : (dyadicUnitResidue 1 : ZMod 8) = 1 := by rw [dyadicUnitResidue, unitAt_one, map_one, Units.val_one]
    rw [h₁, h₂]
    exact dyadicTable_defect _ _ _ _ (dyadic_residue_odd x) (dyadic_residue_odd y)
  · simp only [hilbertExponent, dite_eq_right hp, finiteExponent_odd p hp, oddExponent_table,
      parity_mul, oddBit_mul]
    have h₁ : parity p 1 = 0 := by simp [parity, valAt]
    rw [h₁, show oddTable (oddPrimeBit p) 0 (oddBit p 1) = 0 by simp [oddTable], sub_zero]
    exact oddTable_defect _ _ _ _ _

theorem hilbertExponent_comm (p : Place) (x y : ℚ_[p.val]ˣ) :
    hilbertExponent p x y = hilbertExponent p y x := by
  rw [← finiteExponent_defect, ← finiteExponent_defect, mul_comm x y, add_comm (finiteExponent p x)]

theorem finiteExponent_neg (p : Place) (x : ℚ_[p.val]ˣ) :
    finiteExponent p (-x) = -finiteExponent p x := by
  by_cases hp : p = dyadicPlace
  · subst p
    have h : (dyadicUnitResidue (-1) : ZMod 8) = -1 := by
      rw [dyadicUnitResidue, unitAt_neg_one]
      change (PadicInt.toZModPow (p := 2) 3) (-1) = -1
      simp
    rw [← neg_one_mul, dyadicExponent_table, dyadicExponent_table, parity_mul, parity_neg_one,
      zero_add, dyadicUnitResidue_mul, Units.val_mul, h, neg_one_mul]
    exact dyadicTable_neg _ _ (dyadic_residue_odd x)
  · rw [← neg_one_mul, finiteExponent_odd p hp, finiteExponent_odd p hp, oddExponent_table,
      oddExponent_table, parity_mul, parity_neg_one, zero_add, oddBit_mul, oddBit_neg_one p hp]
    exact oddTable_neg _ _ _

#print axioms bitExp_add
#print axioms bitExp_double
#print axioms characterBit_mul
#print axioms parity_mul
#print axioms parity_zero_iff
#print axioms valAt_neg_one
#print axioms parity_neg_one
#print axioms unitAt_one
#print axioms unitAt_neg_one
#print axioms oddBit_mul
#print axioms oddBit_neg_one
#print axioms oddTable_defect
#print axioms oddTable_neg
#print axioms oddExponent_table
#print axioms dyadicFour_mul
#print axioms dyadicEight_mul
#print axioms dyadicTable_defect
#print axioms dyadicTable_neg
#print axioms dyadic_residue_odd
#print axioms dyadicExponent_table
#print axioms hilbertExponent_dyadic
#print axioms hilbertSign_cases
#print axioms hilbertExponent_double
#print axioms hilbertExponent_mul_left
#print axioms finiteExponent_defect
#print axioms hilbertExponent_comm
#print axioms finiteExponent_neg

end ZInQ.Manuscript.RC.Metaplectic2
