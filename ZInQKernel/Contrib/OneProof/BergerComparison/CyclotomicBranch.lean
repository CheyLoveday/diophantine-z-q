import ZInQKernel.Contrib.OneProof.BergerComparison.LogLiftIndependence

/-! Characterize the normalized cyclotomic coordinate by the local
multiplication and power rules for the logarithm. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst FontaineSt BmaxOne
open PanBergerSplit (Ainf)
open ZInQ.Contrib.G9.BdrKer.Cp

variable (p : ℕ) [hp : Fact p.Prime]

private abbrev Tilt := PreTilt 𝓞_ℂ_[p] p

/-- The residue logarithm restricts to the usual Fontaine-kernel
logarithm when the denominator has residue exactly one. -/
theorem logSmallTeich_eq_logTeich {x : Tilt p} (hx : x.untilt = 1)
    (hsmall : (p : 𝓞_ℂ_[p]) ∣ x.untilt - 1) :
    logSmallTeich p x hsmall = logTeich p hx := by
  have h : WittVector.teichmuller p x - 1 ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) :=
    PanBergerSplit.theta_teich_sub_one p hx
  rw [ker_fontaineTheta_Cp, Ideal.mem_span_singleton] at h
  obtain ⟨b, hb⟩ := h
  rw [logSmallTeich_eq_residueLog p x hsmall (a := 0) (b := b)
    (by simpa only [mul_zero, add_zero, one_mul] using sub_eq_iff_eq_add'.mp hb)]
  unfold residueLog
  rw [pLog_zero, map_zero, zero_add]
  refine evalB_congr' p _ _ ?_ _
  exact congrArg (algebraMap (Ainf p) _) hb.symm

/-- The cyclotomic coordinate is forced by the multiplication and power
rules and the two prescribed local logarithms. No ring comparison is
needed for this characterization. -/
theorem cyclotomicCoordinate_eq_of_normalized {ε : Tilt p} (hε : IsGenEps p ε)
    (L : Tilt p → BdR p)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → L (x*y) = L x + L y)
    (hpow : ∀ x (n : ℕ), x ≠ 0 → L (x^n) = (n : ℚ_[p]) • L x)
    (hpFlat : L (pFlat p) = toBdR p (logPTilde p))
    (hsmall : ∀ x (hx : (p : 𝓞_ℂ_[p]) ∣ x.untilt - 1),
      L x = toBdR p (logSmallTeich p x hx)) :
    cyclotomicCoordinate p hε = L (ε - 1) := by
  let h := exists_cyclotomic_small_unit p hε
  let u := Classical.choose h
  let m := Classical.choose (Classical.choose_spec h)
  obtain ⟨hm, he, hu⟩ := Classical.choose_spec (Classical.choose_spec h)
  have hε0 : ε - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_isGenEps p hε)
  have hev : (pFlat p)^p * u ≠ 0 := he ▸ pow_ne_zero _ hε0
  have hp0 : pFlat p ≠ 0 := by
    intro h0
    exact hev (by simp [h0, hp.out.ne_zero])
  have hu0 : u ≠ 0 := by
    intro h0
    exact hev (by simp [h0])
  have hr := congrArg L he
  rw [hpow _ _ hε0, hmul _ _ (pow_ne_zero _ hp0) hu0, hpow _ _ hp0, hpFlat,
    Nat.cast_sub hp.out.one_le, Nat.cast_one] at hr
  have hr' := hsmall (u^m) hu
  rw [hpow _ _ hu0] at hr'
  have hm0 : (m : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hp1 : ((p : ℚ_[p]) - 1) ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_sub hp.out.one_le]
    exact Nat.cast_ne_zero.mpr (by have := hp.out.two_le; omega)
  change coordinateFromUnit p (u^m) hu m = _
  unfold coordinateFromUnit
  rw [← hr', smul_smul, inv_mul_cancel₀ hm0, one_smul, ← hr, smul_smul,
    inv_mul_cancel₀ hp1, one_smul]

end ZInQ.Manuscript.BergerComparison
