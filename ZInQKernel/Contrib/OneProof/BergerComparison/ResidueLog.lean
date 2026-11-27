import ZInQKernel.Contrib.OneProof.BergerReroute.BergerReroute

/-!
# A logarithm using a lift of the residue denominator

For `x^♯ ∈ 1 + p 𝓞_ℂₚ`, lift the denominator to a Witt unit `1 + pa`.
Its logarithm is a p-adic sum in the Witt ring, and the logarithm of the
remaining quotient is a kernel-adic sum in `B_dR^+`.
-/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4
open BergerBst BmaxOne FontaineSt PanBergerSplit
open PowerSeries Ideal WittVector
open scoped BigOperators

variable (p : ℕ) [hp : Fact p.Prime]

private abbrev xi := ZInQ.Contrib.G9.BdrKer.Cp.xi p

private abbrev P : Ideal (Ainf p) := Ideal.span {(p : Ainf p)}
private abbrev intoPlus : Ainf p →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
  (algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p))).comp (algebraMap (Ainf p) (AinfP p))

/-- The signed n-th term of the p-adic logarithm of `1 + pa`. -/
def pLogTerm (a : Ainf p) (n : ℕ) : Ainf p :=
  if n = 0 then 0 else (-1) ^ (n + 1) * zpToW p (logCoeff p n) * a ^ n

private theorem dvd_pLogTerm (a : Ainf p) {k n : ℕ} (h : 2 * k ≤ n) :
    (p : Ainf p) ^ k ∣ pLogTerm p a n := by
  by_cases hn : n = 0
  · simp [pLogTerm, hn]
  rw [pLogTerm, ite_eq_right hn]
  obtain ⟨d, hd⟩ := (logCoeff_spec p hn).2 k h
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ⟨zpToW p d, ?_⟩ _) _
  rw [hd, map_mul, map_pow, map_natCast]

/-- Witt completeness supplies the p-adic sum: the first `2 k` terms determine the
answer modulo `p^k`. -/
theorem exists_pLog (a : Ainf p) :
    ∃ L : Ainf p, ∀ k, (p : Ainf p) ^ k ∣ (∑ n ∈ Finset.range (2 * k), pLogTerm p a n) - L := by
  let s : ℕ → Ainf p := fun k => ∑ n ∈ Finset.range (2 * k), pLogTerm p a n
  have hc : ∀ {m n}, m ≤ n → s m ≡ s n [SMOD ((P p) ^ m • ⊤ : Submodule (Ainf p) (Ainf p))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    change _ ∣ s m - s n
    have hle : 2 * m ≤ 2 * n := Nat.mul_le_mul_left 2 hmn
    have hs : s n = s m + ∑ i ∈ Finset.range (2 * n - 2 * m), pLogTerm p a (2 * m + i) := by
      dsimp only [s]
      conv_lhs => rw [← Nat.add_sub_of_le hle, Finset.sum_range_add]
    rw [hs, sub_add_cancel_left, dvd_neg]
    exact Finset.dvd_sum fun i _ => dvd_pLogTerm p a (Nat.le_add_right _ _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := P p) (M := Ainf p) inferInstance hc
  refine ⟨L, fun k => ?_⟩
  simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] using hL k

/-- The p-adic logarithm of `1 + pa`, computed before mapping into the period ring. -/
def pLog (a : Ainf p) : Ainf p := Classical.choose (exists_pLog p a)

theorem pLog_spec (a : Ainf p) (k : ℕ) :
    (p : Ainf p) ^ k ∣ (∑ n ∈ Finset.range (2 * k), pLogTerm p a n) - pLog p a :=
  Classical.choose_spec (exists_pLog p a) k

theorem pLog_zero : pLog p 0 = 0 := by
  rw [IsHausdorff.eq_iff_smodEq (I := P p)]
  intro k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    sub_zero]
  have ht (n : ℕ) : pLogTerm p 0 n = 0 := by
    by_cases hn : n = 0
    · simp [pLogTerm, hn]
    · simp [pLogTerm, hn, zero_pow hn]
  simpa only [ht, Finset.sum_const_zero, zero_sub, dvd_neg] using pLog_spec p 0 k

private theorem intoPlus_mem_amax (a : Ainf p) : intoPlus p a ∈ Amax p := by
  refine ⟨PowerSeries.C a, C_mem_restricted p a, ?_⟩
  rw [RingHom.comp_apply, PowerSeries.map_C]
  exact psEval_C _ (omegaP_mem p) _

/-- Dividing a Teichmüller lift by a suitably chosen Witt unit leaves a quotient
congruent to one modulo `ker θ`. Both factors are in the Witt ring. -/
theorem exists_residue_factors (x : PreTilt 𝓞_ℂ_[p] p)
    (hx : (p : 𝓞_ℂ_[p]) ∣ x.untilt - 1) :
    ∃ a b : Ainf p, WittVector.teichmuller p x = (1 + p * a) * (1 + xi p * b) := by
  obtain ⟨r, hr⟩ := hx
  obtain ⟨a, ha⟩ := ZInQ.Contrib.G9.BdrKer.Cp.fontaineTheta_surjective p r
  let θ := WittVector.fontaineTheta 𝓞_ℂ_[p] p
  have ht : θ (WittVector.teichmuller p x) = θ (1 + (p : Ainf p) * a) := by
    rw [WittVector.fontaineTheta_teichmuller, map_add, map_one, map_mul, map_natCast, ha]
    exact sub_eq_iff_eq_add'.mp hr
  have hpJ : (p : Ainf p) ∈ (⊥ : Ideal (Ainf p)).jacobson :=
    (IsAdicComplete.le_jacobson_bot (I := P p)) (Ideal.mem_span_singleton_self _)
  have hu : IsUnit (1 + (p : Ainf p) * a) := by
    rw [Ideal.mem_jacobson_bot] at hpJ
    simpa only [add_comm] using hpJ a
  let u := hu.unit
  have hd : θ (WittVector.teichmuller p x * ↑u⁻¹ - 1) = 0 := by
    rw [map_sub, map_one, sub_eq_zero, map_mul, ht]
    change θ (u : Ainf p) * θ (↑u⁻¹ : Ainf p) = 1
    rw [← map_mul, Units.mul_inv, map_one]
  have hk : WittVector.teichmuller p x * ↑u⁻¹ - 1 ∈ RingHom.ker θ := hd
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton] at hk
  obtain ⟨b, hb⟩ := hk
  refine ⟨a, b, ?_⟩
  change _ = (u : Ainf p) * (1 + xi p * b)
  rw [← hb, add_sub_cancel, ← mul_assoc, mul_comm (u : Ainf p), mul_assoc, Units.mul_inv, mul_one]

private def wLocArg (b : Ainf p) := algebraMap (Ainf p) (AinfP p) (xi p * b)

private theorem xiMul_mem (b : Ainf p) : wLocArg p b ∈ Ith p := by
  rw [wLocArg, map_mul]
  exact Ideal.mul_mem_right _ _ (algebraMap_mem_ith p (theta_xi' p))

/-- The logarithm given a Witt lift of the residue and the corresponding correction
in `1 + ker θ`. In the factorization `[x] = (1+pa)(1+ξb)`, the two terms are
`log(1+pa)` and `log([x]/(1+pa))`. -/
def residueLog (a b : Ainf p) : BDeRhamPlus 𝓞_ℂ_[p] p :=
  intoPlus p (pLog p a) + logPlus p (xiMul_mem p b)

/-- The kernel-adic logarithm of `1 + ξb` is also the restricted series with
coefficients `(-1)^(n+1) (p^n/n) b^n` in the variable `ξ/p`. -/
theorem logXi_mem_amax (b : Ainf p) : logPlus p (xiMul_mem p b) ∈ Amax p := by
  let f : (Ainf p)⟦X⟧ := PowerSeries.mk (pLogTerm p b)
  have hf : f ∈ restricted p := fun k => ⟨2 * k, fun n hn => by
    change (p : Ainf p) ^ k ∣ PowerSeries.coeff n f
    rw [PowerSeries.coeff_mk]
    exact dvd_pLogTerm p b hn⟩
  refine ⟨f, hf, ?_⟩
  rw [RingHom.comp_apply, logPlus]
  apply psEval_eq_of_terms
  intro n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, logSeries, PowerSeries.coeff_mk, pLogTerm]
  by_cases hn : n = 0
  · simp [hn]
  rw [ite_eq_right hn, ite_eq_right hn]
  have key : ((n : ℚ_[p]))⁻¹ = (logCoeff p n : ℚ_[p]) * ((p : ℚ_[p])⁻¹) ^ n := by
    have h1 := (logCoeff_spec p hn).1
    have hn' : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hp' : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
    have he : (logCoeff p n : ℚ_[p]) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h1
      exact pow_ne_zero _ hp' h1.symm
    rw [inv_pow, ← h1, mul_inv, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
  have hq : qpToLoc p (logCoeff p n : ℚ_[p]) = algebraMap _ _ (zpToW p (logCoeff p n)) :=
    qpToLoc_algebraMap p _
  rw [key]
  simp only [map_mul, map_pow, map_neg, map_one]
  rw [← hq, omegaP, ZInQ.Contrib.G9.BdrKer.Cp.xi']
  simp only [wLocArg, map_mul, mul_pow]
  ring

theorem residueLog_mem_amax (a b : Ainf p) : residueLog p a b ∈ Amax p :=
  (Amax p).add_mem (intoPlus_mem_amax p (pLog p a)) (logXi_mem_amax p b)

private theorem logPlus_congr {y z : AinfP p} (h : y = z) {hy : y ∈ Ith p} {hz : z ∈ Ith p} :
    logPlus p hy = logPlus p hz := by
  subst z
  rfl

/-- Multiplication by a kernel unit changes only the kernel-adic part of the
logarithm. The same residue lift is used on both sides. -/
theorem residueLog_mul_kernelUnit (a b c : Ainf p) :
    residueLog p a (b + c + xi p * b * c) =
      residueLog p a b + logPlus p (xiMul_mem p c) := by
  let y := wLocArg p b
  let z := wLocArg p c
  have he : wLocArg p (b + c + xi p * b * c) = y + z + y * z := by
    simp only [wLocArg, y, z, map_mul, map_add]
    ring
  unfold residueLog
  calc
    _ = intoPlus p (pLog p a) + (logPlus p (xiMul_mem p b) + logPlus p (xiMul_mem p c)) := by
      apply congrArg (fun L => intoPlus p (pLog p a) + L)
      exact (logPlus_congr p he).trans (logPlus_add p (xiMul_mem p b) (xiMul_mem p c))
    _ = _ := (add_assoc _ _ _).symm

/-- Select a residue lift and evaluate the two convergent series, for a tilt element
whose residue is one modulo `p`. -/
def logSmallTeich (x : PreTilt 𝓞_ℂ_[p] p) (hx : (p : 𝓞_ℂ_[p]) ∣ x.untilt - 1) :
    BDeRhamPlus 𝓞_ℂ_[p] p :=
  residueLog p (Classical.choose (exists_residue_factors p x hx))
    (Classical.choose (Classical.choose_spec (exists_residue_factors p x hx)))

theorem logSmallTeich_mem_amax (x : PreTilt 𝓞_ℂ_[p] p) (hx : (p : 𝓞_ℂ_[p]) ∣ x.untilt - 1) :
    logSmallTeich p x hx ∈ Amax p :=
  residueLog_mem_amax p _ _

/-- The coordinate obtained from a small unit correction to the chosen
`log [p̃]`. If `π̄^(p-1) = p̃^p · v` and `x = v^m` for `m > 0`, the formula is the one
prescribed by multiplicativity and the normalization `log(p) = 0`. This
definition alone does not identify the coordinate with Berger's branch. -/
def coordinateFromUnit (x : PreTilt 𝓞_ℂ_[p] p)
    (hx : (p : 𝓞_ℂ_[p]) ∣ x.untilt - 1) (m : ℕ) : BdR p :=
  ((p : ℚ_[p]) - 1)⁻¹ •
    ((p : ℚ_[p]) • toBdR p (logPTilde p) +
      (m : ℚ_[p])⁻¹ • toBdR p (logSmallTeich p x hx))

/-- The unit correction is bounded in `B_max^+`, so the resulting coordinate
generates the same semistable ring over `B_max`. -/
theorem coordinateFromUnit_adjoin_eq (x : PreTilt 𝓞_ℂ_[p] p)
    (hx : (p : 𝓞_ℂ_[p]) ∣ x.untilt - 1) (m : ℕ) :
    Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {coordinateFromUnit p x hx m}) =
      BergerBst.Bst p := by
  apply bmax_adjoin_eq_bst p _ 0
  unfold coordinateFromUnit
  have hp1 : ((p : ℚ_[p]) - 1) ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_sub hp.out.one_le]
    exact Nat.cast_ne_zero.mpr (by have := hp.out.two_le; omega)
  rw [smul_smul, mul_inv_cancel₀ hp1, one_smul, map_zero, zero_add, add_sub_cancel_left]
  exact (BmaxPlus p).smul_mem
    (Algebra.subset_adjoin ⟨_, logSmallTeich_mem_amax p x hx, rfl⟩) _

end ZInQ.Manuscript.BergerComparison
