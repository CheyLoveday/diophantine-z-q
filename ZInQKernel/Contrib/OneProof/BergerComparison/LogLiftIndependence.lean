import ZInQKernel.Contrib.OneProof.BergerComparison.WittLogAdd
import ZInQKernel.Contrib.OneProof.BergerComparison.CyclotomicUnit

/-! Changing the Witt lift of the residue denominator preserves the
near-one logarithm. The ratio of the two lifts is in 1 + pξ A_inf,
where the two analytic definitions agree. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst FontaineSt
open PanBergerSplit (Ainf AinfP)
open ZInQ.Contrib.G9.BdrKer.Cp

variable (p : ℕ) [hp : Fact p.Prime]

set_option maxHeartbeats 1200000

private abbrev loc := algebraMap (Ainf p) (AinfP p)

private theorem logArg_mem (b : Ainf p) : loc p (xi p * b) ∈ Ith p := by
  rw [map_mul]
  exact (Ith p).mul_mem_right _ (algebraMap_mem_ith p (theta_xi' p))

private theorem one_add_p_isUnit (a : Ainf p) : IsUnit (1 + (p : Ainf p)*a) := by
  have h : (p : Ainf p) ∈ (⊥ : Ideal (Ainf p)).jacobson :=
    (IsAdicComplete.le_jacobson_bot (I := Ideal.span {(p : Ainf p)}))
      (Ideal.mem_span_singleton_self _)
  rw [Ideal.mem_jacobson_bot] at h
  simpa only [add_comm] using h a

private theorem logXi_add (b d : Ainf p) :
    logPlus p (logArg_mem p (b+d+xi p*b*d)) =
      logPlus p (logArg_mem p b) + logPlus p (logArg_mem p d) := by
  have h : loc p (xi p * (b+d+xi p*b*d)) =
      loc p (xi p*b) + loc p (xi p*d) + loc p (xi p*b)*loc p (xi p*d) := by
    simp only [map_add, map_mul]
    ring
  have he {x y : AinfP p} (hxy : x = y) (hx : x ∈ Ith p) (hy : y ∈ Ith p) :
      logPlus p hx = logPlus p hy := by subst y; rfl
  exact (he h _ _).trans (logPlus_add p (logArg_mem p b) (logArg_mem p d))

/-- The two logarithms of a Teichmüller factorization depend only on
the product, not on the Witt lift of the denominator. -/
theorem residueLog_independent_of_lift (a b a' b' : Ainf p)
    (h : (1 + (p : Ainf p)*a) * (1 + xi p*b) =
      (1 + (p : Ainf p)*a') * (1 + xi p*b')) :
    residueLog p a b = residueLog p a' b' := by
  obtain ⟨u, hu⟩ := one_add_p_isUnit p a
  let c := (a' - a) * (↑u⁻¹ : Ainf p)
  have hc : (1 + (p : Ainf p)*a') = (u : Ainf p)*(1 + p*c) := by
    have he : (u : Ainf p)*((p : Ainf p)*c) = (p : Ainf p)*(a'-a) := by
      dsimp only [c]
      calc
        _ = (p : Ainf p)*(a'-a)*((u : Ainf p)*(↑u⁻¹ : Ainf p)) := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
    rw [mul_add, mul_one, he, hu]
    ring
  let θ := WittVector.fontaineTheta 𝓞_ℂ_[p] p
  have hθ : θ (1 + (p : Ainf p)*a) = θ (1 + (p : Ainf p)*a') := by
    have hh := congrArg θ h
    simpa only [map_mul, map_add, map_one, show θ (xi p) = 0 from theta_xi' p,
      zero_mul, add_zero, mul_one] using hh
  have hθc : θ c = 0 := by
    have hh : θ (1 + (p : Ainf p)*a') = θ (1 + (p : Ainf p)*a) * θ (1+p*c) := by
      rw [hc, map_mul, hu]
    rw [← hθ] at hh
    have huθ : θ (1 + (p : Ainf p)*a) ≠ 0 := by
      rw [← hu]
      exact ((u.isUnit).map θ).ne_zero
    have hc' := mul_left_cancel₀ huθ (by simpa only [mul_one] using hh.symm :
      θ (1 + (p : Ainf p)*a) * θ (1+p*c) = θ (1 + (p : Ainf p)*a) * 1)
    rw [map_add, map_one, map_mul, map_natCast, add_eq_left] at hc'
    exact (mul_eq_zero.mp hc').resolve_left (ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p)
  have hdMem : c ∈ RingHom.ker θ := hθc
  rw [ker_fontaineTheta_Cp, Ideal.mem_span_singleton] at hdMem
  obtain ⟨d, hd⟩ := hdMem
  rw [hd, hu] at hc
  have ha' : a' = a + xi p*d + (p : Ainf p)*a*(xi p*d) := by
    apply mul_left_cancel₀ (witt_p_ne_zero p)
    linear_combination hc
  have hB : 1 + xi p*b = (1 + (p : Ainf p)*(xi p*d))*(1 + xi p*b') := by
    apply mul_left_cancel₀ (one_add_p_isUnit p a).ne_zero
    rw [← mul_assoc, ← hc]
    exact h
  have hb : b = (p : Ainf p)*d + b' + xi p*((p : Ainf p)*d)*b' := by
    apply mul_left_cancel₀ (xi_ne_zero p)
    linear_combination hB
  have hOverlap :
      ofLoc p (loc p (pLog p (xi p*d))) = logPlus p (logArg_mem p ((p : Ainf p)*d)) := by
    have he : loc p ((p : Ainf p)*(xi p*d)) = loc p (xi p*((p : Ainf p)*d)) :=
      congrArg (loc p) (mul_left_comm _ _ _)
    have hh := pLog_agrees_logPlus_on_overlap p d (he.symm ▸ logArg_mem p ((p : Ainf p)*d))
    have same {x y : AinfP p} (e : x = y) (hx : x ∈ Ith p) (hy : y ∈ Ith p) :
        logPlus p hx = logPlus p hy := by subst y; rfl
    exact hh.trans (same he _ _)
  change ofLoc p (loc p (pLog p a)) + logPlus p (logArg_mem p b) =
    ofLoc p (loc p (pLog p a')) + logPlus p (logArg_mem p b')
  rw [ha', pLog_add, (show logPlus p (logArg_mem p b) =
    logPlus p (logArg_mem p ((p : Ainf p)*d)) + logPlus p (logArg_mem p b') from by
      rw [hb, logXi_add])]
  rw [map_add, map_add, hOverlap, add_assoc]

/-- The chosen-lift definition agrees with the logarithm obtained from
any Witt lift of the same residue denominator. -/
theorem logSmallTeich_eq_residueLog (x : PreTilt 𝓞_ℂ_[p] p) (hx : (p : 𝓞_ℂ_[p]) ∣ x.untilt - 1)
    {a b : Ainf p} (h : WittVector.teichmuller p x = (1+p*a)*(1+xi p*b)) :
    logSmallTeich p x hx = residueLog p a b := by
  let hh := exists_residue_factors p x hx
  change residueLog p (Classical.choose hh) (Classical.choose (Classical.choose_spec hh)) = _
  exact residueLog_independent_of_lift p _ _ _ _
    ((Classical.choose_spec (Classical.choose_spec hh)).symm.trans h)

/-- The near-one logarithm respects multiplication for all three
arguments for which the input residue is one modulo p. -/
theorem logSmallTeich_mul (x y : PreTilt 𝓞_ℂ_[p] p)
    (hx : (p : 𝓞_ℂ_[p]) ∣ x.untilt - 1) (hy : (p : 𝓞_ℂ_[p]) ∣ y.untilt - 1)
    (hxy : (p : 𝓞_ℂ_[p]) ∣ (x*y).untilt - 1) :
    logSmallTeich p (x*y) hxy = logSmallTeich p x hx + logSmallTeich p y hy := by
  obtain ⟨a, b, h⟩ := exists_residue_factors p x hx
  obtain ⟨c, d, h'⟩ := exists_residue_factors p y hy
  rw [logSmallTeich_eq_residueLog p x hx h, logSmallTeich_eq_residueLog p y hy h']
  rw [logSmallTeich_eq_residueLog p (x*y) hxy
    (a := a+c+(p : Ainf p)*a*c) (b := b+d+xi p*b*d) (by rw [map_mul, h, h']; ring)]
  change ofLoc p (loc p (pLog p (a+c+(p : Ainf p)*a*c))) +
    logPlus p (logArg_mem p (b+d+xi p*b*d)) =
    ofLoc p (loc p (pLog p a)) + logPlus p (logArg_mem p b) +
      (ofLoc p (loc p (pLog p c)) + logPlus p (logArg_mem p d))
  rw [pLog_add, logXi_add, map_add, map_add]
  abel

end ZInQ.Manuscript.BergerComparison
