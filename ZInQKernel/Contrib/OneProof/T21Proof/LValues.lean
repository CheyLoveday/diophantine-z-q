import ZInQKernel.Contrib.OneProof.T21Proof.LKernel

/-!
# t21-proof: `L(C_1, 1)` and `L(C_3, 1)` to within explicit bounds

Task t21-proof. `L(C_d, 1) = Σ_j c_j (π/M) Λ_{j/M}(1)` (`M = 4d`, `c = twChar d`, Hecke's continuation
of `Contrib/HeckeFE`); `Λ_{a,b}(1) = mainL a b + O(1)` (`LKernel.lean`); the main sum is a finite
sum `Σ q_x E^{N_x}`, `E = e^{−π/M²}`, bounded with a kernel-checked rational certificate (`decide`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open Complex Real Set MeasureTheory HurwitzZeta ZInQ.Contrib.HeckeFE ZInQ.Contrib.TYZLcal
open ZInQ.Contrib.HeckeAll

/-! ## The continuation of `L(C_3, s)` -/

theorem isLContinuation_twChar {d : ℕ} (hsq : Squarefree d) [NeZero d] [NeZero (4 * d)] :
    ZInQ.Literature.IsLContinuation (ZInQ.Contrib.TYZDecomp.curveC d) (Fexp (4 * d) (twChar d)) := by
  refine ⟨differentiable_Fexp _ _, fun s hs => ?_⟩
  have hD1 : DeuringCd 1 := deuringCd_of_gaussPointCount (by norm_num) squarefree_one
    ZInQ.Contrib.GaussFE.gaussPointCount
  rw [Fexp_eq_twistedL _ _ hs, ZInQ.Contrib.TYZDecomp.curveC, LSeries_cd_eq' hsq s]
  refine (LSeries_eq_twistedL (4 * d) (twChar d) _ (fun n hn => ?_) hs).symm
  rw [cdCoeff_twist d hn, hD1 n hn, heckeCoeff, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [twChar_intCast hq, jacobiSym.one_right]
  push_cast
  ring

instance : NeZero (4 * 3) := ⟨by norm_num⟩

/-- **`L(C_3, 1)` as a finite combination of the `Λ_{a,b}(1)`.** -/
theorem lValOne_three_eq : ZInQ.Contrib.TYZDecomp.lValOne 3 =
    ∑ j : Fin 12 × Fin 12, twChar 3 (((j.1 : ℤ) : ZMod (4 * 3)), ((j.2 : ℤ) : ZMod (4 * 3))) *
      (1 / 12) * ((π : ℂ) * gaussLambda (((j.1 : ℝ) / 12 : ℝ) : UnitAddCircle)
        (((j.2 : ℝ) / 12 : ℝ) : UnitAddCircle) 1) := by
  rw [ZInQ.Contrib.TYZDecomp.lValOne_eq (isLContinuation_twChar (d := 3) Nat.prime_three.squarefree), Fexp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [cpow_one, Complex.Gamma_one, inv_one, mul_one]
  push_cast
  norm_num

/-! ## Coefficient tables -/

/-- `Re (4 · unitOf)` on residues mod 4. -/
def uRe (a b : ℕ) : ℤ :=
  if (a % 4, b % 4) = (1, 0) ∨ (a % 4, b % 4) = (3, 2) then 1
  else if (a % 4, b % 4) = (3, 0) ∨ (a % 4, b % 4) = (1, 2) then -1 else 0

/-- `Im (unitOf)` on residues mod 4. -/
def uIm (a b : ℕ) : ℤ :=
  if (a % 4, b % 4) = (0, 3) ∨ (a % 4, b % 4) = (2, 1) then 1
  else if (a % 4, b % 4) = (0, 1) ∨ (a % 4, b % 4) = (2, 3) then -1 else 0

/-- `(3/n)` for odd `n`, by `n mod 12`. -/
def jac12 (n : ℕ) : ℤ :=
  if n % 12 = 1 ∨ n % 12 = 11 then 1 else if n % 12 = 5 ∨ n % 12 = 7 then -1 else 0

theorem unitOf_cast (a b : ℕ) :
    unitOf (((a : ℤ) : ZMod 4), ((b : ℤ) : ZMod 4)) = (uRe a b : ℂ) + (uIm a b : ℂ) * I := by
  have ha : ((a : ℤ) : ZMod 4) = ((a % 4 : ℕ) : ZMod 4) := by
    rw [Int.cast_natCast, ZMod.natCast_mod]
  have hb : ((b : ℤ) : ZMod 4) = ((b % 4 : ℕ) : ZMod 4) := by
    rw [Int.cast_natCast, ZMod.natCast_mod]
  have hu : uRe a b = uRe (a % 4) (b % 4) := by simp [uRe, Nat.mod_mod]
  have hv : uIm a b = uIm (a % 4) (b % 4) := by simp [uIm, Nat.mod_mod]
  rw [ha, hb, hu, hv]
  have h4a : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h4b : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize a % 4 = r at h4a ⊢
  generalize b % 4 = t at h4b ⊢
  interval_cases r <;> interval_cases t <;> simp (config := {decide := true}) [unitOf, uRe, uIm]

end ZInQ.Contrib.T21Proof
