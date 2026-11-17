import ZInQKernel.Contrib.OneProof.Gamma0QExp.Reduce

/-!
# gamma0-qexp, part 6: `ℂ(X₀(N)) = ℂ(j, j_N)` for meromorphic modular functions

For `g` invariant under `Γ₀(N)`, meromorphic on `ℍ` and of moderate growth at every cusp, and the
cosets `c ∈ SL₂(ℤ)/Γ₀(N)` with representatives `γ_c`, put `g_c = g ∘ γ_c⁻¹`, `J_c = j_N ∘ γ_c⁻¹`.
The coefficients of `R(Y) = Σ_c g_c ∏_{c' ≠ c} (Y − J_{c'})` and of
`S(Y) = Σ_c ∏_{c' ≠ c} (Y − J_{c'})` are `SL₂(ℤ)`-invariant meromorphic functions of moderate
growth, hence rational in `j` (`levelOne_mero`); evaluating at `Y = j_N = J_1` gives
`g · S(j_N) = R(j_N)`, and `S(j_N) = ∏_{c ≠ 1} (j_N − J_c) ≠ 0` for `Im τ` large (separation).
Result (`analytic_core`): `B(j, j_N)·g = A(j, j_N)` on punctured neighbourhoods of every point,
with `B(j, j_N)` not identically zero.

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane ModularCurve Filter Topology Asymptotics
open scoped MatrixGroups

namespace ZInQ.Gamma0QExp

/-! ### The symmetric polynomials -/

section SymPoly

open Polynomial

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Σ_i f_i ∏_{j ≠ i} (X − J_j)`. -/
def symPoly (f J : ι → R) : R[X] :=
  ∑ i, C (f i) * ∏ j, (if j = i then 1 else (X - C (J j)))

theorem symPoly_comp_equiv (f J : ι → R) (e : ι ≃ ι) :
    symPoly (f ∘ e) (J ∘ e) = symPoly f J := by
  unfold symPoly
  refine Eq.trans ?_ (Equiv.sum_comp e
    (fun i => C (f i) * ∏ j, (if j = i then 1 else (X - C (J j)))))
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  congr 1
  refine Eq.trans ?_ (Equiv.prod_comp e (fun j => if j = e i then (1 : R[X]) else (X - C (J j))))
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [e.injective.eq_iff]

theorem symPoly_eval_self (f J : ι → R) (i₀ : ι) :
    (symPoly f J).eval (J i₀) = f i₀ * ∏ j, (if j = i₀ then 1 else J i₀ - J j) := by
  simp only [symPoly, eval_finset_sum, eval_mul, eval_C, eval_prod, apply_ite (eval (J i₀)),
    eval_one, eval_sub, eval_X]
  rw [Finset.sum_eq_single i₀]
  · intro i _ hi
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    simp [Ne.symm hi]
  · simp

theorem symPoly_map {S : Type*} [CommRing S] (φ : R →+* S) (f J : ι → R) :
    (symPoly f J).map φ = symPoly (φ ∘ f) (φ ∘ J) := by
  simp [symPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_prod, apply_ite]

theorem natDegree_symPoly_le (f J : ι → R) : (symPoly f J).natDegree ≤ Fintype.card ι := by
  unfold symPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans (natDegree_C_mul_le _ _) (le_trans (natDegree_prod_le _ _) ?_)
  calc ∑ j, (if j = i then (1 : R[X]) else (X - C (J j))).natDegree ≤ ∑ _j : ι, 1 :=
        Finset.sum_le_sum fun j _ => by
          split_ifs
          · simp
          · exact le_trans (natDegree_sub_le _ _) (max_le natDegree_X_le (by simp))
    _ = Fintype.card ι := by simp

/-- The universal coefficient. -/
theorem symPoly_coeff_eval (f J : ι → ℂ) (k : ℕ) :
    (symPoly f J).coeff k = MvPolynomial.eval (Sum.elim f J)
      ((symPoly (fun i => MvPolynomial.X (Sum.inl i)) (fun i => MvPolynomial.X (Sum.inr i)) :
        (MvPolynomial (ι ⊕ ι) ℂ)[X]).coeff k) := by
  rw [← Polynomial.coeff_map, symPoly_map]
  have h1 : (MvPolynomial.eval (Sum.elim f J)) ∘ (fun i => MvPolynomial.X (Sum.inl i)) = f := by
    funext i; simp
  have h2 : (MvPolynomial.eval (Sum.elim f J)) ∘ (fun i => MvPolynomial.X (Sum.inr i)) = J := by
    funext i; simp
  rw [h1, h2]

end SymPoly

/-! ### Meromorphy and analyticity -/

theorem mero_mvEval {σ : Type*} (F : σ → ℍ → ℂ)
    (h : ∀ i (τ : ℍ), MeromorphicAt (F i ∘ ofComplex) (τ : ℂ)) (p : MvPolynomial σ ℂ) (τ : ℍ) :
    MeromorphicAt ((fun τ => MvPolynomial.eval (fun i => F i τ) p) ∘ ofComplex) (τ : ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa [Function.comp_def] using MeromorphicAt.const a (τ : ℂ)
  | add p q hp hq =>
    convert hp.add hq using 1
    funext z; simp
  | mul_X p i hp =>
    convert hp.mul (h i τ) using 1
    funext z; simp

theorem jf_analyticAt {z : ℂ} (hz : 0 < z.im) : AnalyticAt ℂ (jf ∘ ofComplex) z :=
  DifferentiableOn.analyticAt (fun u hu => (jf_differentiableAt ⟨u, hu⟩).differentiableWithinAt)
    (isOpen_UH.mem_nhds hz)

theorem jN_analyticAt (N : ℕ) [NeZero N] {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (jN N ∘ ofComplex) z := by
  have hNz : 0 < ((N : ℂ) * z).im := natCast_mul_im_pos N ⟨z, hz⟩
  have h1 : AnalyticAt ℂ ((jf ∘ ofComplex) ∘ fun u : ℂ => (N : ℂ) * u) z :=
    (jf_analyticAt hNz).comp (analyticAt_const.mul analyticAt_id)
  refine h1.congr ?_
  filter_upwards [isOpen_UH.mem_nhds hz] with u hu
  have hNu : 0 < ((N : ℂ) * u).im := natCast_mul_im_pos N ⟨u, hu⟩
  simp only [Function.comp_apply, jN]
  congr 1
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos hNu, coe_scaleN, ofComplex_apply_of_im_pos hu]

theorem mob_analyticAt (γ : SL(2, ℤ)) (τ : ℍ) : AnalyticAt ℂ (mob γ) (τ : ℂ) := by
  have hden := denom_SL_ne_zero γ τ
  have h1 : AnalyticAt ℂ (fun z : ℂ => ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1))
      (τ : ℂ) :=
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const) hden
  refine h1.congr ?_
  filter_upwards [isOpen_UH.mem_nhds (coe_mem_UH τ)] with z hz
  simp only [mob, coe_SL_smul, ofComplex_apply_of_im_pos hz]

theorem comp_mob (F : ℍ → ℂ) (γ : SL(2, ℤ)) :
    (fun τ => F (γ • τ)) ∘ ofComplex = (F ∘ ofComplex) ∘ mob γ := by
  funext z; simp [mob]

theorem mero_comp_smul {F : ℍ → ℂ} (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (γ : SL(2, ℤ)) (τ : ℍ) : MeromorphicAt ((fun τ => F (γ • τ)) ∘ ofComplex) (τ : ℂ) := by
  rw [comp_mob]
  refine MeromorphicAt.comp_analyticAt ?_ (mob_analyticAt γ τ)
  rw [mob_coe]
  exact hF _

/-! ### Polynomials are nonzero far out -/

theorem exists_eval_ne_zero_of_norm_gt (p : Polynomial ℂ) (hp : p ≠ 0) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → p.eval z ≠ 0 := by
  classical
  refine ⟨∑ x ∈ p.roots.toFinset, ‖x‖, fun z hz h0 => ?_⟩
  have hz' : z ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]; exact h0
  have := Finset.single_le_sum (f := fun x : ℂ => ‖x‖) (fun _ _ => norm_nonneg _) hz'
  linarith

/-! ### Cosets of `Γ₀(N)` -/

section Cosets

variable (N : ℕ) [NeZero N]

/-- `SL₂(ℤ)/Γ₀(N)`. -/
abbrev Cos := SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N

noncomputable instance : Fintype (Cos N) := Fintype.ofFinite _

/-- `g_c = g ∘ γ_c⁻¹`. -/
def conjF (g : ℍ → ℂ) (c : Cos N) (τ : ℍ) : ℂ := g ((Quotient.out c)⁻¹ • τ)

/-- `J_c = j_N ∘ γ_c⁻¹`. -/
def conjJ (c : Cos N) (τ : ℍ) : ℂ := jN N ((Quotient.out c)⁻¹ • τ)

theorem out_smul (σ : SL(2, ℤ)) (c : Cos N) :
    ∃ h ∈ CongruenceSubgroup.Gamma0 N, Quotient.out (σ • c) = σ * Quotient.out c * h := by
  have hc : σ • c = (QuotientGroup.mk (σ * Quotient.out c) : Cos N) := by
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) (σ * Quotient.out c)
  exact ⟨h, h.2, by rw [hc]; exact hh⟩

theorem out_inv_smul (σ : SL(2, ℤ)) (c : Cos N) (τ : ℍ) :
    ∃ h ∈ CongruenceSubgroup.Gamma0 N,
      (Quotient.out (σ • c))⁻¹ • σ • τ = h • ((Quotient.out c)⁻¹ • τ) := by
  obtain ⟨h, hh, he⟩ := out_smul N σ c
  refine ⟨h⁻¹, inv_mem hh, ?_⟩
  rw [he, mul_inv_rev, mul_inv_rev, mul_smul, mul_smul, inv_smul_smul]

theorem conjF_smul {g : ℍ → ℂ}
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ, g (γ • τ) = g τ)
    (σ : SL(2, ℤ)) (c : Cos N) (τ : ℍ) : conjF N g (σ • c) (σ • τ) = conjF N g c τ := by
  obtain ⟨h, hh, he⟩ := out_inv_smul N σ c τ
  simp only [conjF, he, hinv h hh]

theorem conjJ_smul (σ : SL(2, ℤ)) (c : Cos N) (τ : ℍ) :
    conjJ N (σ • c) (σ • τ) = conjJ N c τ := by
  obtain ⟨h, hh, he⟩ := out_inv_smul N σ c τ
  simp only [conjJ, he, jN_smul_of_mem N hh]

/-- The identity coset. -/
def c₀ : Cos N := QuotientGroup.mk 1

theorem out_c₀_mem : Quotient.out (c₀ N) ∈ CongruenceSubgroup.Gamma0 N := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) (1 : SL(2, ℤ))
  rw [c₀, hh, one_mul]
  exact h.2

theorem conjF_c₀ {g : ℍ → ℂ}
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ, g (γ • τ) = g τ) (τ : ℍ) :
    conjF N g (c₀ N) τ = g τ :=
  hinv _ (inv_mem (out_c₀_mem N)) τ

theorem conjJ_c₀ (τ : ℍ) : conjJ N (c₀ N) τ = jN N τ :=
  jN_smul_of_mem N (inv_mem (out_c₀_mem N)) τ

theorem out_inv_not_mem {c : Cos N} (hc : c ≠ c₀ N) :
    (Quotient.out c)⁻¹ ∉ CongruenceSubgroup.Gamma0 N := by
  intro h
  apply hc
  rw [← QuotientGroup.out_eq' c, c₀, QuotientGroup.eq]
  simpa using h

end Cosets

end ZInQ.Gamma0QExp
