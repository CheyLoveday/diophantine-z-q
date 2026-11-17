import ZInQKernel.Contrib.OneProof.DegEqDetTate.Algebra

/-!
# charpoly-p: the algebra of Mumford §19 Thm 4 without finiteness of `End(A)` (Mathlib + deg-det)

Task charpoly-p (2026-11-17), report `docs/research/charpoly-p.md`, scratch `scratch/charpoly-p/`.

deg-det's `det_eq_deg_abstract_le` needs `φ` integral over `ℤ` (a monic `R ∈ ℤ[X]` with `R(φ) = 0`), which
the tree gets from `End(A)` finite over `ℤ` (Mumford §19 Thm 3). This file removes that input: it works with
the polynomial function `N` on polynomials of degree `≤ D` in `φ` (no relation needed) and proves

* `NtD_mul`, `NtD_eq_Rs`: `N` is multiplicative on pairs of total degree `≤ D` over every `ℚ`-algebra
  (Combinatorial Nullstellensatz), hence `N(F) = ∏_{P₀(a)=0} F(a)` for `deg F ≤ D` over an algebraically
  closed field, `P₀(t) = N(t − X)`;
* `eq_of_norm_RsZ_le_bdd`: deg-det's one-sided comparison lemma with test polynomials of degree
  `≤ deg P` only;
* `charpoly_eq_P0D`: `charpoly ρ(φ) = P₀` (any `D ≥ n`);
* `int_of_Rs_pow_sub`: a monic `P ∈ ℚ[X]` such that `∏_{P(a)=0} (a^m − q)` is an integer for every prime
  `q` and every `m` lies in `ℤ[X]` (roots of `q`-adic absolute value `> 1` would make the product large).
-/

open Polynomial Filter Topology

noncomputable section

namespace ZInQ.Contrib.OneProof.CharPolyCharP

open ZInQ.Contrib.OneProof.DegDet

/-! ## 1. Products over roots, truncated -/

section Roots

variable {L : Type*} [Field L] [IsAlgClosed L]

theorem Rs_mul_right (P F G : L[X]) : Rs P (F * G) = Rs P F * Rs P G := by
  unfold Rs
  simp only [eval_mul]
  exact Multiset.prod_map_mul

theorem Rs_C (P : L[X]) (c : L) : Rs P (C c) = c ^ (Multiset.card P.roots) := by
  unfold Rs
  simp only [eval_C, Multiset.map_const', Multiset.prod_replicate]

theorem Rs_X_sub_C (P : L[X]) (hPm : P.Monic) (r : L) :
    Rs P (X - C r) = (-1) ^ (Multiset.card P.roots) * P.eval r := by
  unfold Rs
  rw [(IsAlgClosed.splits P).eval_eq_prod_roots_of_monic hPm r, ← prod_map_neg']
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp only [eval_sub, eval_X, eval_C]
  ring

/-- **Truncated abstract lemma.** `Φ : L[X] → L` multiplicative on pairs of total degree `≤ D`, with
`Φ(c) = cⁿ` and `Φ(X − r) = (−1)ⁿ P(r)` (`P` monic of degree `n`), is `F ↦ ∏_{P(a)=0} F(a)` on
polynomials of degree `≤ D`. -/
theorem eq_Rs_of_mul_trunc (Φ : L[X] → L) (D n : ℕ) (P : L[X]) (hPm : P.Monic)
    (hPd : P.natDegree = n)
    (hmul : ∀ F G : L[X], F.natDegree + G.natDegree ≤ D → Φ (F * G) = Φ F * Φ G)
    (hC : ∀ c, Φ (C c) = c ^ n) (hlin : ∀ r, Φ (X - C r) = (-1) ^ n * P.eval r)
    (F : L[X]) (hF : F.natDegree ≤ D) : Φ F = Rs P F := by
  have hcard : Multiset.card P.roots = n := by
    rw [← hPd, (IsAlgClosed.splits P).natDegree_eq_card_roots]
  have key : ∀ s : Multiset L, Multiset.card s ≤ D → ∀ c : L,
      Φ (C c * (s.map (fun r => X - C r)).prod) = Rs P (C c * (s.map (fun r => X - C r)).prod) := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      intro _ c
      simp only [Multiset.map_zero, Multiset.prod_zero, mul_one]
      rw [hC, Rs_C, hcard]
    | cons r s ih =>
      intro hs c
      rw [Multiset.card_cons] at hs
      rw [Multiset.map_cons, Multiset.prod_cons, mul_left_comm]
      have hdeg2 : (C c * (s.map (fun r => X - C r)).prod).natDegree ≤ Multiset.card s :=
        (natDegree_C_mul_le _ _).trans (natDegree_multiset_prod_X_sub_C_eq_card s).le
      have hdeg : (X - C r : L[X]).natDegree + (C c * (s.map (fun r => X - C r)).prod).natDegree
          ≤ D := by
        rw [natDegree_X_sub_C]; omega
      rw [hmul _ _ hdeg, ih (by omega) c, Rs_mul_right, hlin, Rs_X_sub_C P hPm, hcard]
  rw [(IsAlgClosed.splits F).eq_prod_roots]
  apply key
  rw [← (IsAlgClosed.splits F).natDegree_eq_card_roots]
  exact hF

end Roots

/-! ## 2. A polynomial function on polynomials of degree `≤ D` -/

theorem eq_sum_fin {S : Type*} [Semiring S] (F : S[X]) (a : ℕ) (hF : F.natDegree ≤ a) :
    F = ∑ i : Fin (a + 1), C (F.coeff i) * X ^ (i : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => C (F.coeff i) * X ^ i)]
  conv_lhs => rw [as_sum_range' F (a + 1) (Nat.lt_succ_of_le hF)]
  simp_rw [C_mul_X_pow_eq_monomial]

theorem natDegree_sum_fin_le {S : Type*} [Semiring S] (a : ℕ) (c : Fin (a + 1) → S) :
    (∑ i : Fin (a + 1), C (c i) * X ^ (i : ℕ)).natDegree ≤ a :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.2)

section PolyFn

variable {D : ℕ} (N : MvPolynomial (Fin (D + 1)) ℚ)

/-- `N` read on the coefficients `0, …, D` of a polynomial. -/
def NtD (S : Type*) [CommRing S] [Algebra ℚ S] (F : S[X]) : S :=
  MvPolynomial.aeval (fun i : Fin (D + 1) => F.coeff i) N

theorem NtD_map {S S' : Type*} [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S']
    (f : S →ₐ[ℚ] S') (F : S[X]) : NtD N S' (F.map (f : S →+* S')) = f (NtD N S F) := by
  unfold NtD
  rw [MvPolynomial.comp_aeval_apply]
  simp_rw [coeff_map]
  rfl

theorem NtD_C_mul {n : ℕ} (hN : N.IsHomogeneous n) (S : Type*) [CommRing S] [Algebra ℚ S] (c : S)
    (F : S[X]) : NtD N S (C c * F) = c ^ n * NtD N S F := by
  unfold NtD
  simp_rw [coeff_C_mul]
  exact aeval_mul_of_isHomogeneous hN c _

/-- `N` on integer polynomials. -/
abbrev NtDZ (F : ℤ[X]) : ℚ := NtD N ℚ (F.map (Int.castRingHom ℚ))

/-- **Generic multiplicativity, truncated.** -/
theorem NtD_mul (a b : ℕ) (hab : a + b ≤ D) (h1 : NtDZ N 1 = 1)
    (hmulZ : ∀ F G : ℤ[X], F.natDegree ≤ a → G.natDegree ≤ b → NtDZ N F ≠ 0 → NtDZ N G ≠ 0 →
      NtDZ N (F * G) = NtDZ N F * NtDZ N G)
    (S : Type*) [CommRing S] [Algebra ℚ S] (F G : S[X]) (hF : F.natDegree ≤ a)
    (hG : G.natDegree ≤ b) : NtD N S (F * G) = NtD N S F * NtD N S G := by
  classical
  let σ := Fin (a + 1) ⊕ Fin (b + 1)
  let Fg : (MvPolynomial σ ℚ)[X] := ∑ i : Fin (a + 1), C (MvPolynomial.X (Sum.inl i)) * X ^ (i : ℕ)
  let Gg : (MvPolynomial σ ℚ)[X] := ∑ i : Fin (b + 1), C (MvPolynomial.X (Sum.inr i)) * X ^ (i : ℕ)
  have hmapF : ∀ (T : Type) [CommRing T] [Algebra ℚ T] (x : σ → T),
      Fg.map (MvPolynomial.aeval x : MvPolynomial σ ℚ →ₐ[ℚ] T).toRingHom =
        ∑ i : Fin (a + 1), C (x (Sum.inl i)) * X ^ (i : ℕ) := by
    intro T _ _ x
    simp [Fg, Polynomial.map_sum]
  have hmapG : ∀ (T : Type) [CommRing T] [Algebra ℚ T] (x : σ → T),
      Gg.map (MvPolynomial.aeval x : MvPolynomial σ ℚ →ₐ[ℚ] T).toRingHom =
        ∑ i : Fin (b + 1), C (x (Sum.inr i)) * X ^ (i : ℕ) := by
    intro T _ _ x
    simp [Gg, Polynomial.map_sum]
  set S2 := MvPolynomial σ ℚ
  set A := NtD N S2 Fg
  set B := NtD N S2 Gg
  set AB := NtD N S2 (Fg * Gg)
  have hev : ∀ x : σ → ℚ, ∀ H : S2[X],
      MvPolynomial.eval x (NtD N S2 H) =
        NtD N ℚ (H.map (MvPolynomial.aeval x : S2 →ₐ[ℚ] ℚ).toRingHom) := by
    intro x H
    rw [← MvPolynomial.coe_aeval_eq_eval]
    exact (NtD_map N (MvPolynomial.aeval x : S2 →ₐ[ℚ] ℚ) H).symm
  have hint : ∀ y : σ → ℕ, MvPolynomial.eval (fun i => (y i : ℚ)) ((AB - A * B) * (A * B)) = 0 := by
    intro y
    set Fy : ℤ[X] := ∑ i : Fin (a + 1), C ((y (Sum.inl i) : ℕ) : ℤ) * X ^ (i : ℕ)
    set Gy : ℤ[X] := ∑ i : Fin (b + 1), C ((y (Sum.inr i) : ℕ) : ℤ) * X ^ (i : ℕ)
    have hF' : Fg.map (MvPolynomial.aeval (fun i => (y i : ℚ)) : S2 →ₐ[ℚ] ℚ).toRingHom =
        Fy.map (Int.castRingHom ℚ) := by
      rw [hmapF]; simp [Fy, Polynomial.map_sum]
    have hG' : Gg.map (MvPolynomial.aeval (fun i => (y i : ℚ)) : S2 →ₐ[ℚ] ℚ).toRingHom =
        Gy.map (Int.castRingHom ℚ) := by
      rw [hmapG]; simp [Gy, Polynomial.map_sum]
    simp only [map_mul, map_sub]
    rw [hev, hev, hev, Polynomial.map_mul, hF', hG', ← Polynomial.map_mul]
    change (NtDZ N (Fy * Gy) - NtDZ N Fy * NtDZ N Gy) * (NtDZ N Fy * NtDZ N Gy) = 0
    by_cases hFy : NtDZ N Fy = 0
    · rw [hFy]; ring
    by_cases hGy : NtDZ N Gy = 0
    · rw [hGy]; ring
    rw [hmulZ Fy Gy (natDegree_sum_fin_le a _) (natDegree_sum_fin_le b _) hFy hGy, sub_self,
      zero_mul]
  have hK : (AB - A * B) * (A * B) = 0 := by
    set K := (AB - A * B) * (A * B)
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset K
      (fun i => (Finset.range (K.degreeOf i + 1)).image (fun k : ℕ => (k : ℚ))) (fun i => ?_) ?_
    · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
      exact Nat.lt_succ_self _
    · intro x hx
      choose y _ hy using fun i => Finset.mem_image.mp (hx i)
      have : x = fun i => (y i : ℚ) := funext fun i => (hy i).symm
      rw [this]
      exact hint y
  -- `A, B ≠ 0`: evaluate at the coefficients of `1`
  set u : ℕ → ℚ := fun i => (1 : ℚ[X]).coeff i
  have hone : ∀ c : ℕ, ∑ i : Fin (c + 1), C (u i) * X ^ (i : ℕ) = (1 : ℚ[X]) := fun c =>
    (eq_sum_fin (1 : ℚ[X]) c (by rw [natDegree_one]; exact Nat.zero_le _)).symm
  have hNt1 : NtD N ℚ (1 : ℚ[X]) = 1 := by
    rw [← h1, NtDZ, Polynomial.map_one]
  have hA : A ≠ 0 := by
    intro hA0
    have := hev (Sum.elim (fun i => u i) (fun i => u i)) Fg
    rw [hmapF] at this
    simp only [Sum.elim_inl] at this
    rw [hone, hNt1, hA0, map_zero] at this
    exact zero_ne_one this
  have hB : B ≠ 0 := by
    intro hB0
    have := hev (Sum.elim (fun i => u i) (fun i => u i)) Gg
    rw [hmapG] at this
    simp only [Sum.elim_inr] at this
    rw [hone, hNt1, hB0, map_zero] at this
    exact zero_ne_one this
  have hAB : AB = A * B := by
    rcases mul_eq_zero.mp hK with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (mul_ne_zero hA hB)
  set x : σ → S := Sum.elim (fun i => F.coeff i) (fun i => G.coeff i)
  set f : S2 →ₐ[ℚ] S := MvPolynomial.aeval x
  have hFx : Fg.map f.toRingHom = F := by
    rw [hmapF]; exact (eq_sum_fin F a hF).symm
  have hGx : Gg.map f.toRingHom = G := by
    rw [hmapG]; exact (eq_sum_fin G b hG).symm
  rw [← hFx, ← hGx, ← Polynomial.map_mul]
  change NtD N S ((Fg * Gg).map (f : S2 →+* S)) = NtD N S (Fg.map (f : S2 →+* S)) *
    NtD N S (Gg.map (f : S2 →+* S))
  rw [NtD_map N, NtD_map N, NtD_map N]
  change f AB = f A * f B
  rw [hAB, map_mul]

/-- `P₀(t) = N(t − X)`. -/
def P0D : ℚ[X] := NtD N ℚ[X] (C X - X)

theorem NtD_C_sub_X (S : Type*) [CommRing S] [Algebra ℚ S] (t : S) :
    NtD N S (C t - X) = ((P0D N).map (algebraMap ℚ S)).eval t := by
  have h := NtD_map N (Polynomial.aeval t : ℚ[X] →ₐ[ℚ] S) (C X - X)
  rw [Polynomial.map_sub, map_C, map_X] at h
  simp only [AlgHom.coe_toRingHom, aeval_X] at h
  rw [h, P0D, aeval_def, eval₂_eq_eval_map]

theorem P0D_monic {n : ℕ} (hN : N.IsHomogeneous n) (h1 : NtDZ N 1 = 1) :
    (P0D N).Monic ∧ (P0D N).natDegree = n := by
  set u : Fin (D + 1) → ℚ := fun i => (1 : ℚ[X]).coeff i
  set v : Fin (D + 1) → ℚ := fun i => (X : ℚ[X]).coeff i
  have hu : MvPolynomial.eval u N = 1 := by
    rw [← h1, NtDZ, NtD, Polynomial.map_one, ← MvPolynomial.coe_aeval_eq_eval]
  have hcoord : ∀ i : Fin (D + 1), (C X - X : ℚ[X][X]).coeff i = C (u i) * X - C (v i) := by
    intro i
    simp only [u, v, coeff_sub, coeff_C, coeff_X, coeff_one]
    split_ifs <;> simp
  have := monic_aeval_lin hN u v hu
  unfold P0D NtD
  simp_rw [hcoord]
  exact this

end PolyFn

/-! ## 3. The comparison lemma with test polynomials of bounded degree -/

section Compare

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem mult_le_of_norm_Rs_le_bdd {μ P1 Q1 : ℚ_[ℓ][X]} (hμ : Irreducible μ) (hμm : μ.Monic)
    (hP1 : P1 ≠ 0) (hQ1 : Q1 ≠ 0) (hPμ : ¬ μ ∣ P1) (hQμ : ¬ μ ∣ Q1) (e f : ℕ)
    (h : ∀ F : ℤ[X], F.natDegree ≤ μ.natDegree → RsZ (μ ^ e * P1) F ≠ 0 → ‖RsZ (μ ^ e * P1) F‖ ≤ ‖RsZ (μ ^ f * Q1) F‖) :
    f ≤ e := by
  classical
  set ι := algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) with hι
  set d := μ.natDegree with hd_def
  have hd : 0 < d := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hμ)
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  set a : ℝ := (ℓ : ℝ)⁻¹ with ha_def
  have ha0 : 0 < a := inv_pos.mpr (zero_lt_one.trans hℓ1)
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hℓ1
  -- scaling `μ` into `ℤ_ℓ[X]`
  obtain ⟨s, hs⟩ : ∃ s : ℕ, ∀ i, ‖(ℓ : ℚ_[ℓ]) ^ s * μ.coeff i‖ ≤ 1 := by
    obtain ⟨s, hsM⟩ := pow_unbounded_of_one_lt (∑ i ∈ Finset.range (d + 1), ‖μ.coeff i‖) hℓ1
    refine ⟨s, fun i => ?_⟩
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    have hci : ‖μ.coeff i‖ ≤ ∑ i ∈ Finset.range (d + 1), ‖μ.coeff i‖ := by
      by_cases hi : i ≤ d
      · exact Finset.single_le_sum (f := fun i => ‖μ.coeff i‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), norm_zero]
        exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hpos : (0 : ℝ) < (ℓ : ℝ) ^ s := pow_pos (zero_lt_one.trans hℓ1) s
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hci.trans hsM.le
  set c : ℕ → ℤ_[ℓ] := fun i => ⟨(ℓ : ℚ_[ℓ]) ^ s * μ.coeff i, hs i⟩ with hc
  set μ0 : ℚ_[ℓ][X] := C ((ℓ : ℚ_[ℓ]) ^ s) * μ with hμ0
  have hμ0nd : (μ0.map ι).natDegree < d + 1 := by
    refine Nat.lt_succ_of_le ((natDegree_map_le).trans ?_)
    exact (natDegree_C_mul_le _ _).trans le_rfl
  have hμ0ev : ∀ w, (μ0.map ι).eval w = ∑ i ∈ Finset.range (d + 1), ι (c i) * w ^ i := by
    intro w
    rw [eval_eq_sum_range' hμ0nd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, hμ0, coeff_C_mul]
  have hμ0μ : ∀ w, (μ0.map ι).eval w = ι ((ℓ : ℚ_[ℓ]) ^ s) * (μ.map ι).eval w := by
    intro w
    rw [hμ0, Polynomial.map_mul, map_C, eval_mul, eval_C]
  -- the test polynomials
  set Fn : ℕ → ℤ[X] := fun n => ∑ i ∈ Finset.range (d + 1),
    C ((PadicInt.appr (c i) (2 * n) : ℕ) : ℤ) * X ^ i + C ((ℓ : ℤ) ^ n) with hFn
  have hFdeg : ∀ n, (Fn n).natDegree ≤ d := by
    intro n
    refine (natDegree_add_le _ _).trans (max_le ?_ (by rw [natDegree_C]; exact Nat.zero_le _))
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hFev : ∀ n w, ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
      ∑ i ∈ Finset.range (d + 1), ((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) * w ^ i +
        (ℓ : PadicAlgCl ℓ) ^ n := by
    intro n w
    simp [hFn, Polynomial.map_sum, eval_finsetSum]
  have happr : ∀ n i, ‖((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) - ι (c i)‖ ≤
      a ^ (2 * n) := by
    intro n i
    have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr (PadicInt.appr_spec (2 * n) (c i))
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h1
    rw [← map_natCast ι, ← map_sub, hι, PadicAlgCl.norm_extends ℓ, norm_sub_rev]
    convert h1 using 1
    rw [ha_def, zpow_neg, zpow_natCast, inv_pow]
  have herr : ∀ n w (B : ℝ), 1 ≤ B → ‖w‖ ≤ B →
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
        (ℓ : PadicAlgCl ℓ) ^ n‖ ≤ a ^ (2 * n) * B ^ d := by
    intro n w B hB hw
    have hrw : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
        (ℓ : PadicAlgCl ℓ) ^ n = ∑ i ∈ Finset.range (d + 1),
          (((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) - ι (c i)) * w ^ i := by
      rw [hFev, hμ0ev]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      ring
    rw [hrw]
    exact norm_sum_range_le d _ w _ B (pow_nonneg ha0.le _) hB hw fun i _ => happr n i
  -- roots
  have hμmap : μ.map ι ≠ 0 := (hμm.map ι).ne_zero
  have hP1map : P1.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hP1
  have hQ1map : Q1.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hQ1
  have hcardμ : Multiset.card (μ.map ι).roots = d := by
    rw [← (IsAlgClosed.splits (μ.map ι)).natDegree_eq_card_roots, natDegree_map]
  have hμroot : ∀ w ∈ (μ.map ι).roots, (μ.map ι).eval w = 0 := fun w hw =>
    (mem_roots hμmap).mp hw
  have hnotroot : ∀ (R : ℚ_[ℓ][X]), R ≠ 0 → ¬ μ ∣ R → ∀ w ∈ (R.map ι).roots,
      (μ.map ι).eval w ≠ 0 := by
    intro R hR hRμ w hw hμw
    have hRw : aeval w R = 0 := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact (mem_roots ((Polynomial.map_ne_zero_iff ι.injective).mpr hR)).mp hw
    have hμw' : aeval w μ = 0 := by rw [aeval_def, eval₂_eq_eval_map]; exact hμw
    have hmin := minpoly.eq_of_irreducible_of_monic hμ hμw' hμm
    exact hRμ (hmin ▸ minpoly.dvd ℚ_[ℓ] w hRw)
  have hℓs : ι ((ℓ : ℚ_[ℓ]) ^ s) ≠ 0 := by
    rw [map_ne_zero_iff _ ι.injective]
    exact pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero)
  have hμ0ne : ∀ (R : ℚ_[ℓ][X]), R ≠ 0 → ¬ μ ∣ R → ∀ w ∈ (R.map ι).roots,
      0 < ‖(μ0.map ι).eval w‖ := by
    intro R hR hRμ w hw
    rw [norm_pos_iff, hμ0μ]
    exact mul_ne_zero hℓs (hnotroot R hR hRμ w hw)
  -- the bound `B`
  set Z : Finset (PadicAlgCl ℓ) :=
    ((μ.map ι).roots + (P1.map ι).roots + (Q1.map ι).roots).toFinset with hZ
  set B : ℝ := 1 + ∑ w ∈ Z, ‖w‖ with hB
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hBw : ∀ w ∈ Z, ‖w‖ ≤ B := fun w hw =>
    (Finset.single_le_sum (f := fun w => ‖w‖) (fun _ _ => norm_nonneg _) hw).trans
      (le_add_of_nonneg_left zero_le_one)
  have hmemZ1 : ∀ w ∈ (μ.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl hw)))
  have hmemZ2 : ∀ w ∈ (P1.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr hw)))
  have hmemZ3 : ∀ w ∈ (Q1.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inr hw)
  -- eventually
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1
  have ev1 : ∀ᶠ n in atTop, a ^ n * B ^ d < 1 := by
    have hBd : 0 < B ^ d := pow_pos (zero_lt_one.trans_le hB1) d
    filter_upwards [hlim.eventually (gt_mem_nhds (inv_pos.mpr hBd))] with n hn
    calc a ^ n * B ^ d < (B ^ d)⁻¹ * B ^ d := mul_lt_mul_of_pos_right hn hBd
      _ = 1 := inv_mul_cancel₀ hBd.ne'
  set S : Finset (PadicAlgCl ℓ) := (P1.map ι).roots.toFinset ∪ (Q1.map ι).roots.toFinset with hS
  have hSpos : ∀ w ∈ S, 0 < ‖(μ0.map ι).eval w‖ := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact hμ0ne P1 hP1 hPμ w (Multiset.mem_toFinset.mp hw)
    · exact hμ0ne Q1 hQ1 hQμ w (Multiset.mem_toFinset.mp hw)
  have ev2 : ∀ᶠ n in atTop, ∀ w ∈ S, a ^ n < ‖(μ0.map ι).eval w‖ := by
    rw [eventually_all_finset]
    intro w hw
    exact hlim.eventually (gt_mem_nhds (hSpos w hw))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ev1.and ev2)
  -- values of `F_n` at the roots
  have hsmall : ∀ n, N ≤ n → ∀ w ∈ Z, ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w -
      (μ0.map ι).eval w - (ℓ : PadicAlgCl ℓ) ^ n‖ < a ^ n := by
    intro n hn w hw
    refine (herr n w B hB1 (hBw w hw)).trans_lt ?_
    have := (hN n hn).1
    calc a ^ (2 * n) * B ^ d = a ^ n * (a ^ n * B ^ d) := by rw [two_mul, pow_add]; ring
      _ < a ^ n * 1 := mul_lt_mul_of_pos_left this (pow_pos ha0 n)
      _ = a ^ n := mul_one _
  have V1 : ∀ n, N ≤ n → ∀ w ∈ (μ.map ι).roots,
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w‖ = a ^ n := by
    intro n hn w hw
    set E := ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
      (ℓ : PadicAlgCl ℓ) ^ n with hE
    have hval : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
        (ℓ : PadicAlgCl ℓ) ^ n + E := by
      rw [hE, hμ0μ, hμroot w hw, mul_zero]; ring
    have hEl := hsmall n hn w (hmemZ1 w hw)
    rw [← hE] at hEl
    rw [hval, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_natCast_prime_pow]
    · exact max_eq_left hEl.le
    · rw [norm_natCast_prime_pow]; exact hEl.ne'
  have V2 : ∀ n, N ≤ n → ∀ w ∈ S,
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w‖ = ‖(μ0.map ι).eval w‖ := by
    intro n hn w hw
    have hwZ : w ∈ Z := by
      rcases Finset.mem_union.mp hw with hw | hw
      · exact hmemZ2 w (Multiset.mem_toFinset.mp hw)
      · exact hmemZ3 w (Multiset.mem_toFinset.mp hw)
    set E := ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
      (ℓ : PadicAlgCl ℓ) ^ n with hE
    have hval : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
        (μ0.map ι).eval w + ((ℓ : PadicAlgCl ℓ) ^ n + E) := by
      rw [hE]; ring
    have hEl := hsmall n hn w hwZ
    rw [← hE] at hEl
    have hsm : ‖(ℓ : PadicAlgCl ℓ) ^ n + E‖ < ‖(μ0.map ι).eval w‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt ?_
      rw [norm_natCast_prime_pow]
      exact max_lt ((hN n hn).2 w hw) (hEl.trans ((hN n hn).2 w hw))
    rw [hval, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsm.ne', max_eq_left hsm.le]
  -- the norms of the products
  have hRsP : ∀ (R : ℚ_[ℓ][X]) (k : ℕ), R ≠ 0 → ¬ μ ∣ R →
      (∀ w ∈ (R.map ι).roots, w ∈ S) → ∀ n, N ≤ n →
      ‖RsZ (μ ^ k * R) (Fn n)‖ = ((a ^ n) ^ d) ^ k *
        ((R.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod := by
    intro R k hR hRμ hRS n hn
    have hRmap : R.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hR
    unfold RsZ
    rw [Polynomial.map_mul, Polynomial.map_pow, Rs_mul_left (pow_ne_zero _ hμmap) hRmap,
      Rs_pow_left, norm_mul, norm_pow]
    unfold Rs
    rw [norm_multiset_prod_map, norm_multiset_prod_map]
    congr 2
    · rw [Multiset.map_congr rfl (V1 n hn), Multiset.map_const', Multiset.prod_replicate, hcardμ]
    · exact Multiset.map_congr rfl fun w hw => V2 n hn w (hRS w hw)
  have hP1S : ∀ w ∈ (P1.map ι).roots, w ∈ S := fun w hw =>
    Finset.mem_union.mpr (Or.inl (Multiset.mem_toFinset.mpr hw))
  have hQ1S : ∀ w ∈ (Q1.map ι).roots, w ∈ S := fun w hw =>
    Finset.mem_union.mpr (Or.inr (Multiset.mem_toFinset.mpr hw))
  set CP := ((P1.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod with hCP
  set CQ := ((Q1.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod with hCQ
  have hCPpos : 0 < CP := Multiset.prod_pos fun x hx => by
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
    exact hμ0ne P1 hP1 hPμ w hw
  have key : ∀ n, N ≤ n → ((a ^ n) ^ d) ^ e * CP ≤ ((a ^ n) ^ d) ^ f * CQ := by
    intro n hn
    have h1 := hRsP P1 e hP1 hPμ hP1S n hn
    have h2 := hRsP Q1 f hQ1 hQμ hQ1S n hn
    rw [← h1, ← h2]
    refine h _ (hFdeg n) ?_
    rw [← norm_pos_iff, h1]
    exact mul_pos (pow_pos (pow_pos (pow_pos ha0 n) d) e) hCPpos
  by_contra hfe
  push Not at hfe
  have hy0 : 0 < (a ^ d) ^ (f - e) := pow_pos (pow_pos ha0 d) _
  have hy1 : (a ^ d) ^ (f - e) < 1 :=
    pow_lt_one₀ (pow_pos ha0 d).le (pow_lt_one₀ ha0.le ha1 hd.ne') (by omega)
  have hlim2 := tendsto_pow_atTop_nhds_zero_of_lt_one hy0.le hy1
  have hCQ0 : 0 ≤ CQ := Multiset.prod_nonneg fun x hx => by
    obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hx
    exact norm_nonneg _
  have ev3 : ∀ᶠ n in atTop, ((a ^ d) ^ (f - e)) ^ n * CQ < CP := by
    have : Tendsto (fun n => ((a ^ d) ^ (f - e)) ^ n * CQ) atTop (𝓝 (0 * CQ)) := hlim2.mul_const CQ
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds hCPpos)
  obtain ⟨n, hn1, hn2⟩ := (ev3.and (eventually_ge_atTop N)).exists
  have k := key n hn2
  have hxe : 0 < ((a ^ n) ^ d) ^ e := pow_pos (pow_pos (pow_pos ha0 n) d) e
  have hsplit : ((a ^ n) ^ d) ^ f = ((a ^ n) ^ d) ^ e * ((a ^ d) ^ (f - e)) ^ n := by
    have hf : f = e + (f - e) := by omega
    calc ((a ^ n) ^ d) ^ f = ((a ^ n) ^ d) ^ (e + (f - e)) := by rw [← hf]
      _ = ((a ^ n) ^ d) ^ e * ((a ^ n) ^ d) ^ (f - e) := pow_add _ _ _
      _ = ((a ^ n) ^ d) ^ e * ((a ^ d) ^ (f - e)) ^ n := by ring
  rw [hsplit, mul_assoc] at k
  have := le_of_mul_le_mul_left k hxe
  linarith



/-- **One-sided comparison lemma, bounded degree.** Monic `P, Q` over `ℚ_ℓ` of the same degree with
`|∏_{P(a)=0} F(a)|_ℓ ≤ |∏_{Q(b)=0} F(b)|_ℓ` for every `F ∈ ℤ[X]` of degree `≤ deg Q` with nonzero left side
are equal. -/
theorem eq_of_norm_RsZ_le_bdd {P Q : ℚ_[ℓ][X]} (hP : P.Monic) (hQ : Q.Monic)
    (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ F : ℤ[X], F.natDegree ≤ Q.natDegree → RsZ P F ≠ 0 → ‖RsZ P F‖ ≤ ‖RsZ Q F‖) :
    P = Q := by
  classical
  have hP0 := hP.ne_zero
  have hQ0 := hQ.ne_zero
  have hcount : ∀ μ : ℚ_[ℓ][X], Irreducible μ → μ.Monic → μ ∣ Q →
      (UniqueFactorizationMonoid.normalizedFactors Q).count μ ≤
        (UniqueFactorizationMonoid.normalizedFactors P).count μ := by
    intro μ hμ hμm hμQ
    have hμdeg : μ.natDegree ≤ Q.natDegree := natDegree_le_of_dvd hμQ hQ0
    obtain ⟨e, P1, hP1μ, hPe⟩ := WfDvdMonoid.max_power_factor hP0 hμ
    obtain ⟨f, Q1, hQ1μ, hQf⟩ := WfDvdMonoid.max_power_factor hQ0 hμ
    have hP1 : P1 ≠ 0 := by rintro rfl; rw [mul_zero] at hPe; exact hP0 hPe
    have hQ1 : Q1 ≠ 0 := by rintro rfl; rw [mul_zero] at hQf; exact hQ0 hQf
    have hfe : f ≤ e := mult_le_of_norm_Rs_le_bdd hμ hμm hP1 hQ1 hP1μ hQ1μ e f (by
      rw [← hPe, ← hQf]; exact fun F hF => h F (hF.trans hμdeg))
    have hnd : ∀ (k : ℕ) (R : ℚ_[ℓ][X]), ¬ μ ∣ R → ¬ μ ^ (k + 1) ∣ μ ^ k * R := by
      intro k R hR hdvd
      rw [pow_succ] at hdvd
      exact hR ((mul_dvd_mul_iff_left (pow_ne_zero k hμ.ne_zero)).mp hdvd)
    rw [UniqueFactorizationMonoid.count_normalizedFactors_eq hμ hμm.normalize_eq_self
        ⟨P1, hPe⟩ (hPe ▸ hnd e P1 hP1μ),
      UniqueFactorizationMonoid.count_normalizedFactors_eq hμ hμm.normalize_eq_self
        ⟨Q1, hQf⟩ (hQf ▸ hnd f Q1 hQ1μ)]
    exact hfe
  have hle : UniqueFactorizationMonoid.normalizedFactors Q ≤
      UniqueFactorizationMonoid.normalizedFactors P := by
    rw [Multiset.le_iff_count]
    intro μ
    by_cases hμ : μ ∈ UniqueFactorizationMonoid.normalizedFactors Q
    · have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor μ hμ
      have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor μ hμ
      have hmon : μ.Monic := by rw [← hnorm]; exact Polynomial.monic_normalize hirr.ne_zero
      exact hcount μ hirr hmon (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hμ)
    · rw [Multiset.count_eq_zero.mpr hμ]; exact Nat.zero_le _
  have hdvd : Q ∣ P := by
    rw [← (UniqueFactorizationMonoid.prod_normalizedFactors hQ0).dvd_iff_dvd_left,
      ← (UniqueFactorizationMonoid.prod_normalizedFactors hP0).dvd_iff_dvd_right]
    exact Multiset.prod_dvd_prod_of_le hle
  obtain ⟨c, hc⟩ := hdvd
  have hcm : c.Monic := by
    have := hP
    rw [hc] at this
    exact hQ.of_mul_monic_left this
  have hcd : c.natDegree = 0 := by
    have := congrArg natDegree hc
    rw [hQ.natDegree_mul hcm, ← hdeg] at this
    omega
  rw [hc, hcm.natDegree_eq_zero.mp hcd, mul_one]

end Compare

end ZInQ.Contrib.OneProof.CharPolyCharP
