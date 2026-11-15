import ZInQKernel.Contrib.OneProof.FHNonvanishing.FE
import ZInQKernel.Contrib.OneProof.FHPrinted.LocalNorm

open HeckeRing.GL2

namespace ZInQ.FHPrinted

open ZInQ.GZDecomp ZInQ.GZFH

/-! ## The printed objects -/

/-- **The local component `χ_{d,v}` of the quadratic idele class character of `ℚ(√d)`** at a
place `v` with completion `K = ℚ_v`: the character of `K^×` whose kernel is the norm group
`N(K(√d)^×)` (local class field theory), i.e. the Hilbert symbol `(d, ·)_v`:
`χ_{d,v}(x) = 1` if `x = y² − d z²` with `y, z ∈ K`, and `−1` otherwise. -/
noncomputable def localChar (K : Type*) [Field K] (d : ℤ) (x : Kˣ) : ℤ := by
  classical
  exact if IsLocalNorm K d (x : K) then 1 else -1

/-- The Dirichlet coefficients `aₙ(f) χ_d(n)` of `L(s, π_f ⊗ χ_d)` (classical normalization
`s ↦ s − ½`), with `χ_d(n)` the Dirichlet coefficient of the idele class character of `ℚ(√d)`
(`idelicChar`). -/
noncomputable def printedTwistCoeff {N : ℕ} [NeZero N] (f : Newform N 2) (d : ℤ) (n : ℕ) : ℂ :=
  coeff f n * (idelicChar d n : ℂ)

/-- **`ε(½, π_f ⊗ χ_{D₀}) = 1`**: the completed L-function of `π_f ⊗ χ_{D₀}`,
`Λ(s) = q^{s/2} (2π)^{−s} Γ(s) L(s − ½, π_f ⊗ χ_{D₀})` (`ZInQ.Literature.completedL`, the entire
continuation `G` of `∑ aₙ(f) χ_{D₀}(n) n^{−s}`), satisfies the functional equation
`Λ(2 − s) = Λ(s)` (sign `+1`) for some conductor `q ≥ 1`, on the strip `0 < Re s < 2`. -/
def RootNumberTwistEqOne {N : ℕ} [NeZero N] (f : Newform N 2) (D₀ : ℤ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∃ G : ℂ → ℂ, IsEntireCont (printedTwistCoeff f D₀) 2 G ∧
    ∀ s : ℂ, 0 < s.re → s.re < 2 →
      ZInQ.Literature.completedL q G (2 - s) = ZInQ.Literature.completedL q G s

/-- **`L(½, π_f ⊗ χ_d) ≠ 0`**, read classically: the entire continuation `G` of
`∑ aₙ(f) χ_d(n) n^{−s}` does not vanish at the centre `s = 1`. -/
def CentralValueNeZero {N : ℕ} [NeZero N] (f : Newform N 2) (d : ℤ) : Prop :=
  ∀ G : ℂ → ℂ, IsEntireCont (printedTwistCoeff f d) 2 G → G 1 ≠ 0

/-- **Friedberg–Hoffstein 1995, Theorem B, printed form** (specialized). -/
def FriedbergHoffsteinB_Printed : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
  ∀ S : Finset ℕ, (∀ p : ℕ, p.Prime → p ∣ 2 * N → p ∈ S) →
  ∀ D₀ : ℤ, IsOddFundDisc D₀ → (∀ p ∈ S, ¬ (p : ℤ) ∣ D₀) →
    RootNumberTwistEqOne f D₀ →
    Set.Infinite {d : ℤ | Squarefree d ∧ d ≠ 1 ∧
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → localChar ℚ_[p] d = localChar ℚ_[p] D₀) ∧
      localChar ℝ d = localChar ℝ D₀ ∧ CentralValueNeZero f d}

/-! ## The dictionary -/

theorem localNorm_iff_of_localChar_eq {K : Type*} [Field K] {d D : ℤ}
    (h : localChar K d = localChar K D) {x : K} (hx : x ≠ 0) :
    IsLocalNorm K d x ↔ IsLocalNorm K D x := by
  have := congrFun h (Units.mk0 x hx)
  simp only [localChar, Units.val_mk0] at this
  by_cases h1 : IsLocalNorm K d x <;> by_cases h2 : IsLocalNorm K D x <;>
    simp only [h1, h2, if_true, if_false, iff_true, iff_false, not_true, not_false_eq_true] at this ⊢
  · norm_num at this
  · norm_num at this

theorem printedTwistCoeff_eq {N : ℕ} [NeZero N] (f : Newform N 2) {d : ℤ} (hd : IsOddFundDisc d)
    {n : ℕ} (hn : n ≠ 0) : printedTwistCoeff f d n = twistCoeff f d n := by
  rw [printedTwistCoeff, twistCoeff, chiD, idelicChar_eq_jacobiSym hd.2.1 hd.2.2 n hn]

theorem exists_natAbs_gt_of_infinite {s : Set ℤ} (hs : s.Infinite) (B : ℕ) :
    ∃ d ∈ s, B < d.natAbs := by
  obtain ⟨d, hd, hdB⟩ := hs.exists_notMem_finset (Finset.Icc (-(B : ℤ)) B)
  refine ⟨d, hd, ?_⟩
  rw [Finset.mem_Icc] at hdB
  omega

/-- **The dictionary: the printed form of Friedberg–Hoffstein gives the functional-equation
form.** -/
theorem friedbergHoffsteinB_FE_of_printed (h : FriedbergHoffsteinB_Printed) :
    FriedbergHoffsteinB_FE := by
  intro N _ f hχ S hS D₀ hD₀ hSD₀ ⟨G, hG, hFE⟩ B
  have hD₀0 : D₀ ≠ 0 := by have := hD₀.2.1; omega
  have hroot : RootNumberTwistEqOne f D₀ :=
    ⟨N * D₀.natAbs ^ 2, by have := NeZero.pos N; positivity, G,
      isEntireCont_congr (fun n hn => (printedTwistCoeff_eq f hD₀ hn).symm) hG, hFE⟩
  obtain ⟨d, ⟨hdsq, hd1, hloc, hinf, hL⟩, hdB⟩ :=
    exists_natAbs_gt_of_infinite (h N f hχ S hS D₀ hD₀ hSD₀ hroot) B
  have h2S : 2 ∈ S := hS 2 Nat.prime_two (dvd_mul_right 2 N)
  obtain ⟨hd4, hsq2⟩ := isSquare_div_two_of_localNorm_iff hdsq hD₀.2.1
    (fun x hx => localNorm_iff_of_localChar_eq (hloc 2 h2S) hx)
  have hdf : IsOddFundDisc d := ⟨hd1, hd4, hdsq⟩
  refine ⟨d, hdB, hdf, ?_, ?_, ?_⟩
  · exact pos_mul_of_real_iff hdsq.ne_zero hD₀0
      (localNorm_iff_of_localChar_eq hinf (by norm_num))
  · intro p _ hpS
    by_cases hp2 : p = 2
    · subst hp2; exact hsq2
    · exact isSquare_div_of_localNorm_iff hp2 hdsq (hSD₀ p hpS)
        (fun x hx => localNorm_iff_of_localChar_eq (hloc p hpS) hx)
  · intro G' hG'
    exact hL G' (isEntireCont_congr (fun n hn => (printedTwistCoeff_eq f hdf hn).symm) hG')

end ZInQ.FHPrinted

#print axioms ZInQ.FHPrinted.friedbergHoffsteinB_FE_of_printed
