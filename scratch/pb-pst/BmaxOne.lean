import ZInQKernel.Contrib.OneProof.PanBergerDict

/-!
# pb-pst (a): `B_max = B_max^+[1/t]` for one `t = log [ε₀]`

bst-construct's `Bmax` inverts `log [ε]` for every `ε ∈ 𝓞_ℂ_p♭` with `ε^♯ = 1`, `ε ≠ 1` (`tInvSet`).
Here: for a generator `ε₀ = (1, ζ_p, ζ_{p²}, …)` (`ζ_p ≠ 1`) every such `log [ε]` is `a · log [ε₀]`
with `a ∈ ℤ_p ∖ 0`, so bst-construct's `Bmax`, `Bst` are `B_max^+[1/t]`, `B_max^+[1/t][log [p̃]]` with
`t = log [ε₀]`.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace BmaxOne

open Module PowerSeries Ideal
open scoped TensorProduct
open BergerBst
open PanBergerSplit (Ainf AinfP theta)

variable (p : ℕ) [Fact p.Prime]

/-! ## §1. `A_inf / ξ^m` is `p`-adically separated -/

theorem theta_xi : theta p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
  change ZInQ.Contrib.G9.BdrKer.Cp.xi p ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p)
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
  exact Ideal.mem_span_singleton_self _

theorem mem_xi_of_forall (w : Ainf p)
    (h : ∀ k : ℕ, ∃ a b : Ainf p, w = (p : Ainf p) ^ k * a + ZInQ.Contrib.G9.BdrKer.Cp.xi p * b) :
    w ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p} := by
  rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
  change theta p w = 0
  apply IsHausdorff.haus' (I := span {(p : 𝓞_ℂ_[p])})
  intro k
  obtain ⟨a, b, rfl⟩ := h k
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, map_add, map_mul, map_mul, map_pow, map_natCast, theta_xi, zero_mul,
    add_zero]
  exact dvd_mul_right _ _

/-- `⋂_k (p^k A_inf + ξ^m A_inf) = ξ^m A_inf`. -/
theorem mem_xi_pow_of_forall (m : ℕ) : ∀ w : Ainf p,
    (∀ k : ℕ, ∃ a b : Ainf p, w = (p : Ainf p) ^ k * a + ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m * b) →
    w ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} := by
  induction m with
  | zero => intro w _; rw [pow_zero, Ideal.span_singleton_one]; trivial
  | succ m ih =>
    intro w h
    have h1 : w ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} := ih w fun k => by
      obtain ⟨a, b, hab⟩ := h k
      exact ⟨a, ZInQ.Contrib.G9.BdrKer.Cp.xi p * b, by rw [hab, pow_succ]; ring⟩
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp h1
    have h2 : z ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p} := mem_xi_of_forall p z fun k => by
      obtain ⟨a, b, hab⟩ := h k
      rw [pow_succ] at hab
      have ha : (p : Ainf p) ^ k * a ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} :=
        Ideal.mem_span_singleton'.mpr ⟨z - ZInQ.Contrib.G9.BdrKer.Cp.xi p * b, by
          linear_combination hab⟩
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (mem_xi_pow_of_p_pow_mul p m k a ha)
      refine ⟨c, b, ?_⟩
      apply mul_left_cancel₀ (pow_ne_zero m (ZInQ.Contrib.G9.BdrKer.Cp.xi_ne_zero p))
      rw [← hc] at hab
      linear_combination hab
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp h2
    exact Ideal.mem_span_singleton'.mpr ⟨d, by rw [pow_succ]; ring⟩

/-! ## §2. `A_max` is `p`-adically separated inside `B_dR^+` -/

theorem ith_pow (m : ℕ) : Ith p ^ m =
    span {algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ m} := by
  rw [Ith, ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineThetaInvertP_Cp, Ideal.span_singleton_pow]
  rfl

/-- `B_dR^+ → A_inf[1/p] / (ker θ)^m` (Mathlib's `B_dR^+` is the `ker θ`-adic completion). -/
def evB (m : ℕ) : BDeRhamPlus 𝓞_ℂ_[p] p →+* AinfP p ⧸ Ith p ^ m :=
  (AdicCompletion.evalₐ (Ith p) m).toRingHom

theorem evB_evalB {x : AinfP p} (hx : x ∈ Ith p) (f : (AinfP p)⟦X⟧) (m : ℕ) :
    evB p m (evalB p hx f) = Ideal.Quotient.mk (Ith p ^ m) ((trunc m f).eval x) :=
  evalₐ_psEval (Ith p) hx f m

theorem ext_evB {x y : BDeRhamPlus 𝓞_ℂ_[p] p} (h : ∀ m, evB p m x = evB p m y) : x = y :=
  AdicCompletion.ext_evalₐ h

/-- Modulo `(ker θ)^m`, `p^m` times an element of `A_max` comes from `A_inf`. -/
theorem amax_mod {y : BDeRhamPlus 𝓞_ℂ_[p] p} (hy : y ∈ Amax p) (m : ℕ) :
    ∃ w : Ainf p, evB p m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m * y) =
      Ideal.Quotient.mk _ (algebraMap (Ainf p) (AinfP p) w) := by
  obtain ⟨f, -, rfl⟩ := hy
  refine ⟨∑ i ∈ Finset.range m, PowerSeries.coeff i f * ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ i *
    (p : Ainf p) ^ (m - i), ?_⟩
  change evB p m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m *
    evalB p (omegaP_mem p) (PowerSeries.map (algebraMap (Ainf p) (AinfP p)) f)) = _
  rw [map_mul, evB_evalB, map_pow, map_natCast, ← map_natCast (Ideal.Quotient.mk _),
    ← map_pow, ← map_mul]
  congr 1
  rw [Polynomial.eval, eval₂_trunc_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := (Finset.mem_range.mp hi).le
  simp only [RingHom.id_apply, PowerSeries.coeff_map, map_mul, map_pow, map_natCast]
  have hpq : (p : AinfP p) * qpToLoc p ((p : ℚ_[p])⁻¹) = 1 :=
    natCast_mul_qp p p (Fact.out : p.Prime).ne_zero
  have hm : (p : AinfP p) ^ m = (p : AinfP p) ^ (m - i) * (p : AinfP p) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  have hx : ZInQ.Contrib.G9.BdrKer.Cp.xi' p =
      algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) := rfl
  rw [hm, omegaP, hx]
  calc (p : AinfP p) ^ (m - i) * (p : AinfP p) ^ i *
        (algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff i f) *
          (algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) *
            qpToLoc p ((p : ℚ_[p])⁻¹)) ^ i)
      = (p : AinfP p) ^ (m - i) * ((p : AinfP p) * qpToLoc p ((p : ℚ_[p])⁻¹)) ^ i *
        (algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff i f) *
          algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i) := by ring
    _ = _ := by rw [hpq, one_pow]; ring

/-- **`A_max ⊆ B_dR^+` is `p`-adically separated**: an element of `B_dR^+` lying in `p^k A_max`
for every `k` is `0`. -/
theorem amax_sep (x : BDeRhamPlus 𝓞_ℂ_[p] p)
    (h : ∀ k : ℕ, ∃ y ∈ Amax p, x = (p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ k * y) : x = 0 := by
  refine ext_evB p fun m => ?_
  rw [map_zero]
  choose y hy hxy using h
  choose w hw using fun k => amax_mod p (hy k) m
  have hk : ∀ k, evB p m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m * x) =
      Ideal.Quotient.mk _ (algebraMap (Ainf p) (AinfP p) ((p : Ainf p) ^ k * w k)) := by
    intro k
    rw [hxy k, mul_left_comm, map_mul, hw k, map_pow, map_natCast, map_mul, map_pow, map_natCast,
      map_mul, map_pow, map_natCast]
  have hw0 : w 0 ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} := by
    refine mem_xi_pow_of_forall p m (w 0) fun k => ?_
    have e := (hk 0).symm.trans (hk k)
    rw [Ideal.Quotient.eq, ← map_sub, ith_pow] at e
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (mem_xi_pow_of_algebraMap p m _ e)
    exact ⟨w k, b, by rw [pow_zero, one_mul] at hb; linear_combination -hb⟩
  have h0 : evB p m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m * x) = 0 := by
    rw [hk 0, pow_zero, one_mul, Ideal.Quotient.eq_zero_iff_mem, ith_pow]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hw0
    exact Ideal.mem_span_singleton'.mpr ⟨algebraMap (Ainf p) (AinfP p) c, by
      rw [← hc, map_mul, map_pow]⟩
  rw [map_mul, map_pow, map_natCast] at h0
  have hu : IsUnit ((p : AinfP p ⧸ Ith p ^ m) ^ m) := by
    refine IsUnit.pow _ ?_
    have := IsLocalization.Away.algebraMap_isUnit (S := AinfP p) (p : Ainf p)
    rw [map_natCast] at this
    simpa using this.map (Ideal.Quotient.mk (Ith p ^ m))
  exact (hu.mul_right_eq_zero).mp h0

/-! ## §3. The tilt: `ε = ε₀^b · η^{p^k}` and `log [ε] ≡ b log [ε₀] mod p^k A_max` -/

open ZInQ.Contrib.G9.BdrKer.Cp (root root_pow root_succ_pow)

/-- **A generator of `ℤ_p(1)` in the tilt**: `ε₀ ∈ 𝓞_ℂ_p♭` with `ε₀^♯ = 1` and `ε₀^{(1)} = ζ_p ≠ 1`, i.e.
`ε₀ = (1, ζ_p, ζ_{p²}, …)` for a compatible system of primitive `p^n`-th roots of unity; `t = log [ε₀]`. -/
def IsGenEps (ε₀ : PreTilt 𝓞_ℂ_[p] p) : Prop := PreTilt.untilt ε₀ = 1 ∧ root ε₀ 1 ≠ 1

theorem iter_mul (n : ℕ) (x y : PreTilt 𝓞_ℂ_[p] p) :
    ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) (x * y) =
      ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) x *
        ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      map_mul]

theorem iter_one (n : ℕ) : ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_one]

theorem iter_pow (k : ℕ) (x : PreTilt 𝓞_ℂ_[p] p) :
    ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[k] x) ^ p ^ k = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p, ih]

theorem root_mul (x y : PreTilt 𝓞_ℂ_[p] p) (n : ℕ) : root (x * y) n = root x n * root y n := by
  simp only [ZInQ.Contrib.G9.BdrKer.Cp.root, iter_mul, map_mul]

theorem root_one (n : ℕ) : root (1 : PreTilt 𝓞_ℂ_[p] p) n = 1 := by
  simp only [ZInQ.Contrib.G9.BdrKer.Cp.root, iter_one, map_one]

theorem root_npow (x : PreTilt 𝓞_ℂ_[p] p) (n c : ℕ) : root (x ^ c) n = root x n ^ c := by
  induction c with
  | zero => rw [pow_zero, pow_zero, root_one]
  | succ c ih => rw [pow_succ, root_mul, ih, pow_succ]

theorem root_zero (x : PreTilt 𝓞_ℂ_[p] p) : root x 0 = PreTilt.untilt x := rfl

theorem root_add_pow (x : PreTilt 𝓞_ℂ_[p] p) (j m : ℕ) : root x (j + m) ^ p ^ m = root x j := by
  induction m with
  | zero => simp
  | succ m ih => rw [← Nat.add_assoc, pow_succ', pow_mul, root_succ_pow, ih]

theorem isPrimitiveRoot_root {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (k : ℕ) :
    IsPrimitiveRoot (root ε₀ k) (p ^ k) := by
  rcases k with _ | k
  · rw [pow_zero, IsPrimitiveRoot.one_right_iff, root_zero]
    exact h.1
  · rw [IsPrimitiveRoot.iff_orderOf]
    apply orderOf_eq_prime_pow
    · rw [show k + 1 = 1 + k by ring, root_add_pow]
      exact h.2
    · rw [root_pow]
      exact h.1

theorem exists_pow_eq {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {ε : PreTilt 𝓞_ℂ_[p] p}
    (hε : PreTilt.untilt ε = 1) (k : ℕ) : ∃ b < p ^ k, root ε₀ k ^ b = root ε k := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  exact (isPrimitiveRoot_root p h k).eq_pow_of_pow_eq_one (by rw [root_pow, hε])

theorem logTeich_congr {x y : PreTilt 𝓞_ℂ_[p] p} (hxy : x = y) (hx : PreTilt.untilt x = 1)
    (hy : PreTilt.untilt y = 1) : logTeich p hx = logTeich p hy := by
  subst hxy
  rfl

theorem logTeich_mul {x y : PreTilt 𝓞_ℂ_[p] p} (hx : PreTilt.untilt x = 1)
    (hy : PreTilt.untilt y = 1) (hxy : PreTilt.untilt (x * y) = 1) :
    logTeich p hxy = logTeich p hx + logTeich p hy := by
  have e := logPlus_add p (teich_sub_one_mem p hx) (teich_sub_one_mem p hy)
  change logPlus p (teich_sub_one_mem p hxy) = logPlus p _ + logPlus p _
  rw [← e]
  refine evalB_congr' p _ _ ?_ (logSeries p)
  rw [map_mul (WittVector.teichmuller p)]
  simp only [map_sub, map_mul, map_one]
  ring

theorem logTeich_one (h : PreTilt.untilt (1 : PreTilt 𝓞_ℂ_[p] p) = 1) : logTeich p h = 0 := by
  have h0 : (0 : AinfP p) ∈ Ith p := Ideal.zero_mem _
  change evalB p (teich_sub_one_mem p h) (logSeries p) = 0
  rw [evalB_congr' p _ h0 (by simp) (logSeries p)]
  rw [show evalB p h0 (logSeries p) = evalB p h0 0 from
    psEval_eq_of_terms (Ith p) h0 h0 _ _ (fun k => ?_), map_zero]
  rcases k with _ | k
  · simp [logSeries]
  · simp

theorem logTeich_pow {x : PreTilt 𝓞_ℂ_[p] p} (hx : PreTilt.untilt x = 1) (n : ℕ)
    (hxn : PreTilt.untilt (x ^ n) = 1) :
    logTeich p hxn = (n : BDeRhamPlus 𝓞_ℂ_[p] p) * logTeich p hx := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul, logTeich_congr p (pow_zero x) hxn (map_one _)]
    exact logTeich_one p _
  | succ n ih =>
    have hxn' : PreTilt.untilt (x ^ n) = 1 := by rw [map_pow, hx, one_pow]
    rw [logTeich_congr p (pow_succ x n) hxn (by rw [map_mul, hxn', hx, one_mul]),
      logTeich_mul p hxn' hx, ih hxn']
    push_cast
    ring

/-- **`log [ε] = b log [ε₀] + p^k z`, `z ∈ A_max`**, when `ε^{(k)} = (ε₀^{(k)})^b`, `b ≤ p^k`:
`ε ε₀^{p^k − b} = η^{p^k}` with `η^♯ = 1`. -/
theorem log_decomp {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {ε : PreTilt 𝓞_ℂ_[p] p}
    (hε : PreTilt.untilt ε = 1) (k b : ℕ) (hbk : b ≤ p ^ k) (hb : root ε₀ k ^ b = root ε k) :
    ∃ z ∈ Amax p, logTeich p hε =
      (b : BDeRhamPlus 𝓞_ℂ_[p] p) * logTeich p h.1 + (p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ k * z := by
  set c := p ^ k - b with hc
  set x := ε * ε₀ ^ c with hx
  set η := (frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[k] x with hη
  have hc0 : PreTilt.untilt (ε₀ ^ c) = 1 := by rw [map_pow, h.1, one_pow]
  have hx1 : PreTilt.untilt x = 1 := by rw [hx, map_mul, hε, hc0, one_mul]
  have hη1 : PreTilt.untilt η = 1 := by
    change root x k = 1
    rw [hx, root_mul, root_npow, ← hb, ← pow_add, hc, Nat.add_sub_cancel' hbk, root_pow, h.1]
  have hηp : η ^ p ^ k = x := iter_pow p k x
  have hηp1 : PreTilt.untilt (η ^ p ^ k) = 1 := by rw [hηp]; exact hx1
  have e1 : logTeich p hx1 = logTeich p hε + (c : BDeRhamPlus 𝓞_ℂ_[p] p) * logTeich p h.1 := by
    rw [logTeich_mul p hε hc0 hx1, logTeich_pow p h.1 c hc0]
  have e2 : logTeich p hηp1 = ((p ^ k : ℕ) : BDeRhamPlus 𝓞_ℂ_[p] p) * logTeich p hη1 :=
    logTeich_pow p hη1 (p ^ k) hηp1
  rw [logTeich_congr p hηp hηp1 hx1] at e2
  refine ⟨logTeich p hη1 - logTeich p h.1,
    Subring.sub_mem _ (logTeich_mem_amax p hη1) (logTeich_mem_amax p h.1), ?_⟩
  have hcast : (c : BDeRhamPlus 𝓞_ℂ_[p] p) = (p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ k - b := by
    rw [hc, Nat.cast_sub hbk]
    push_cast
    ring
  rw [hcast] at e1
  push_cast at e2
  linear_combination (-1 : BDeRhamPlus 𝓞_ℂ_[p] p) * (e2.symm.trans e1)

/-! ## §4. The `p`-adic limit of the exponents -/

omit [Fact p.Prime] in
theorem modEq_of_le (b : ℕ → ℕ) (hb : ∀ k, b (k + 1) ≡ b k [MOD p ^ k]) {k m : ℕ} (hkm : k ≤ m) :
    b m ≡ b k [MOD p ^ k] := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    exact ((hb m).of_dvd (pow_dvd_pow p hkm)).trans ih

theorem exists_padic_limit (b : ℕ → ℕ) (hb : ∀ k, b (k + 1) ≡ b k [MOD p ^ k]) :
    ∃ a : ℤ_[p], ∀ k, a - (b k : ℤ_[p]) ∈ span {(p : ℤ_[p]) ^ k} := by
  have hmem : ∀ k m, k ≤ m → (b m : ℤ_[p]) - (b k : ℤ_[p]) ∈ span {(p : ℤ_[p]) ^ k} := by
    intro k m hkm
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd.mp (modEq_of_le p b hb hkm))
    refine Ideal.mem_span_singleton'.mpr ⟨-(c : ℤ_[p]), ?_⟩
    have := congrArg (fun z : ℤ => (z : ℤ_[p])) hc
    push_cast at this
    linear_combination this
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hcs : CauchySeq (fun k => (b k : ℤ_[p])) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    calc ‖(b n : ℤ_[p]) - b N‖ ≤ (p : ℝ) ^ (-(N : ℤ)) :=
          (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr (hmem N n hn)
      _ = (p : ℝ)⁻¹ ^ N := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ < ε := hN
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨a, fun k => ?_⟩
  rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
  exact le_of_tendsto (ha.sub_const (b k : ℤ_[p])).norm
    (Filter.eventually_atTop.mpr ⟨k, fun m hm =>
      (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr (hmem k m hm)⟩)

/-! ## §5. `log [ε] = a · log [ε₀]`, `a ∈ ℤ_p` -/

/-- `ℤ_p → W(𝓞_ℂ_p♭) → B_dR^+`. -/
def zpB : ℤ_[p] →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
  (ofLoc p).comp ((algebraMap (Ainf p) (AinfP p)).comp (zpToW p))

theorem zpB_mem (c : ℤ_[p]) : zpB p c ∈ Amax p := by
  refine ⟨PowerSeries.C (zpToW p c), fun k => ⟨1, fun n hn => ?_⟩, ?_⟩
  · beta_reduce
    rw [PowerSeries.coeff_C, ite_eq_right (by omega)]
    exact dvd_zero _
  · change evalB p (omegaP_mem p) (PowerSeries.map (algebraMap (Ainf p) (AinfP p))
      (PowerSeries.C (zpToW p c))) = _
    rw [PowerSeries.map_C]
    exact psEval_C (Ith p) (omegaP_mem p) _

theorem logTeich_eq_mul {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {ε : PreTilt 𝓞_ℂ_[p] p}
    (hε : PreTilt.untilt ε = 1) : ∃ a : ℤ_[p], logTeich p hε = zpB p a * logTeich p h.1 := by
  choose b hblt hb using fun k => exists_pow_eq p h hε k
  have hcompat : ∀ k, b (k + 1) ≡ b k [MOD p ^ k] := by
    intro k
    have hP := isPrimitiveRoot_root p h k
    have hfin : IsOfFinOrder (root ε₀ k) :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ k, pow_pos (Fact.out : p.Prime).pos k, hP.pow_eq_one⟩
    rw [hP.eq_orderOf]
    apply hfin.pow_eq_pow_iff_modEq.mp
    rw [hb k, ← root_succ_pow ε k, ← hb (k + 1), ← root_succ_pow ε₀ k, ← pow_mul, ← pow_mul,
      mul_comm]
  obtain ⟨a, ha⟩ := exists_padic_limit p b hcompat
  refine ⟨a, sub_eq_zero.mp (amax_sep p _ fun k => ?_)⟩
  obtain ⟨z, hz, hlog⟩ := log_decomp p h hε k (b k) (hblt k).le (hb k)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (ha k)
  have hac : a = (b k : ℤ_[p]) + c * (p : ℤ_[p]) ^ k := by linear_combination -hc
  refine ⟨z - zpB p c * logTeich p h.1,
    Subring.sub_mem _ hz (Subring.mul_mem _ (zpB_mem p c) (logTeich_mem_amax p h.1)), ?_⟩
  rw [hlog, hac, map_add, map_mul, map_pow, map_natCast, map_natCast]
  ring

end BmaxOne
end PkgI4
end HDec
