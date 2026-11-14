import ZInQKernel.OneProof.H.TailA

/-!
# theta-split: the use of `ThetaRatiosAlgebraic`, proved from a statement on the explicit QM curve

The field `thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic` (OneProof/H/TailA.lean l.4386,
bundled at TailA l.4952 and consumed at TailA l.5010, TailD l.588, TailE l.6663, TailI, TailK, TailO,
TailZ4) is used only through `ThetaPt.thetaPointOfFibre_of_qm_ratios hQM hAlg`, which applies it once:
at the period matrix `Ω(τ)` (pkg-I1 / bp-analytic `Omega`) of the QM lattice `ι(𝒪)(τ, 1)ᵀ` supplied
by `FibreQMPeriod`, where `jNum(Ω(τ))/jDen(Ω(τ)) = J(u)`, `u ∈ ℚ \ 𝒞`, so `J(u) ∈ ℚ \ {0}`.

Here:
* `ThetaRatiosAtQM`: exactly that use (theta-null ratios at `Ω(τ)` are algebraic when
  `j_θ(Ω(τ)) ∈ ℚ \ {0}`), stated over the explicit functions `τ ↦ θ_m(Ω(τ))`, with no abelian
  variety; `thetaPointOfFibre_of_qm_atQM : FibreQMPeriod → ThetaRatiosAtQM → ThetaPointOfFibre`
  (proved) replaces `thetaPointOfFibre_of_qm_ratios`.
* `QMThetaSymmetric`: along the curve, the elementary symmetric functions `e_k` of the ten
  `θ_m(Ω(τ))⁸` are `R_k(j_θ)·(Σθ_m⁸)^k` for polynomials `R_k ∈ ℚ[X]`;
  `thetaRatiosAtQM_of_symmetric` (proved): `QMThetaSymmetric → ThetaRatiosAtQM`.
* `QMThetaSymmetricCore`: the same with the explicit `R_k` found numerically (`qmR`, 80-digit
  numerics, `py/fit_hp.py`), for `2 ≤ k ≤ 9` only; `k = 0, 1, 10` are proved here
  (`esymm_zero`, `esymm_one`, `esymm_ten`). `qmThetaSymmetric_of_core` (proved).

No `sorry`; every theorem ends with `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

namespace HDec.HSyn.G0Split.ThetaPt.ThetaSplit

open CategoryTheory AlgebraicGeometry Limits
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open _root_.ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst
  absLogHeight)
open Complex Polynomial

/-! ## 0. The field, copied verbatim (check) -/

/-- Verbatim copy of `G0Split.ThetaPt.ThetaRatiosAlgebraic` (TailA l.4386). -/
def ThetaRatiosAlgebraicCopy : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts A σ), IsUniformization σ Λ Φu →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∃ m₀ : Char2, thetaConst Ω m₀ ≠ 0 ∧ ∀ m, IsAlgebraic ℚ (thetaConst Ω m / thetaConst Ω m₀)

example : ThetaRatiosAlgebraicCopy ↔ ThetaRatiosAlgebraic := Iff.rfl

/-! ## 1. The use form and the consumer -/

/-- **GLUE (G19 / F1, the use of `ThetaRatiosAlgebraic`; theta-null ratios on the QM curve).**
For `τ` in the upper half-plane with `j_θ(Ω(τ)) = jNum(Ω(τ))/jDen(Ω(τ)) = q ∈ ℚ \ {0}` (pkg-I1's
`Ω(τ) = (F₀(τ)P⁻¹)⁻¹E(τ)`, the period matrix of the QM lattice `ι(𝒪)(τ, 1)ᵀ` for N5's maximal order
of the quaternion algebra of discriminant 6): some theta constant `θ_{m₀}(0, Ω(τ))` is nonzero and every
ratio `θ_m(0, Ω(τ))/θ_{m₀}(0, Ω(τ))` is an algebraic number. (In fact `m₀ = (0,0)` works and all ten
even theta constants are nonzero, since `jNum ≠ 0`.)

This is exactly how the bundle field `ThetaRatiosAlgebraic` is used (at `Ω(τ)` with `j_θ = J(u)`,
`u ∉ 𝒞`): `thetaPointOfFibre_of_qm_atQM`. It is a statement about explicit holomorphic functions of
one variable `τ`; no abelian variety or polarization occurs. Why true: `QMThetaSymmetric` (below) and
`thetaRatiosAtQM_of_symmetric`. -/
def ThetaRatiosAtQM : Prop :=
  ∀ τ : ℂ, 0 < τ.im → ∀ q : ℚ, q ≠ 0 →
    PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = (q : ℂ) →
    ∃ m₀ : Char2, thetaConst (BPAnalytic.QM.Omega τ) m₀ ≠ 0 ∧
      ∀ m, IsAlgebraic ℚ (thetaConst (BPAnalytic.QM.Omega τ) m / thetaConst (BPAnalytic.QM.Omega τ) m₀)

/-- `J(u) ≠ 0` off the contact set (as kernel `J_ne_zero`, PRArith l.131, reproved). -/
theorem Jmap_ne_zero {u : ℚ} (hu : u ∉ contactSet) : Jmap u ≠ 0 := by
  unfold Jmap
  have hG := G_ne_zero u
  simp only [contactSet, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hu
  have hF : u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 ?_) ?_) ?_) ?_) ?_
    · intro h; exact h1 (by linarith)
    · intro h; exact h2 (by linarith)
    · intro h; exact h3 (by linarith)
    · intro h; exact h4 (by linarith)
    · intro h; exact h5 (by linarith)
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hF)) (pow_ne_zero _ hG)

/-- **Missing piece 9, `ThetaPointOfFibre`, from `FibreQMPeriod` and the use form (proved).**
Replaces `thetaPointOfFibre_of_qm_ratios hQM hAlg` (same proof, with `ThetaRatiosAtQM` applied at the
`τ` of `FibreQMPeriod` instead of `ThetaRatiosAlgebraic` at `Ω(τ)`). -/
theorem thetaPointOfFibre_of_qm_atQM (hQM : FibreQMPeriod) (hT : ThetaRatiosAtQM) :
    ThetaPointOfFibre := by
  intro Y Φ π h1 h2 u hu K A hFib
  obtain ⟨σ, Λ, Φu, hΦu, τ, hτ, F, hF, hJ⟩ := hQM Y Φ π h1 h2 u hu K A hFib
  have hS : IsSiegel (BPAnalytic.QM.Omega τ) := isSiegel_Omega hτ
  have hP : IsPeriodMatrix Λ (BPAnalytic.QM.Omega τ) :=
    isPeriodMatrix_of_comap (isPeriodMatrix_qmLattice hτ.ne') F hF
  have hJθ : jTheta (BPAnalytic.QM.Omega τ) = ((Jmap u : ℚ) : ℂ) := by
    rw [jTheta_eq, ← omega_eq]; exact hJ
  obtain ⟨m₀, h0, halg⟩ := hT τ hτ (Jmap u) (Jmap_ne_zero hu) hJ
  obtain ⟨L, emb, z, hz⟩ := exists_nf_of_isAlgebraic _ halg
  have hz' : ∀ m, emb (z m) = (thetaConst (BPAnalytic.QM.Omega τ) m₀)⁻¹ *
      thetaConst (BPAnalytic.QM.Omega τ) m := fun m => by rw [hz m, div_eq_inv_mul]
  exact ⟨σ, Λ, Φu, hΦu, BPAnalytic.QM.Omega τ, hS, hP, L, emb, z, _, inv_ne_zero h0, hz', L,
    fun i => z (evenEnum i), f1_of_theta emb _ z _ (inv_ne_zero h0) hz' (Jmap u) hJθ, height_even z⟩

/-! ## 2. Reduction to symmetric functions of `θ⁸` along the curve -/

/-- The multiset of the ten `θ_m(Ω)⁸`, `m` even (pkg-I1's theta constants). -/
def thetaEight (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Multiset ℂ :=
  PkgI1.evenChars.val.map (fun m => PkgI1.thetaConst m Ω ^ 8)

theorem card_thetaEight (Ω : Matrix (Fin 2) (Fin 2) ℂ) : (thetaEight Ω).card = 10 := by
  rw [thetaEight, Multiset.card_map, Finset.card_val, PkgI1.card_evenChars]

/-- **GLUE (symmetric functions of the even `θ⁸` along the QM curve are rational in `j_θ`).** There
are `R_0, …, R_10 ∈ ℚ[X]` such that for every `τ` in the upper half-plane with `Σ_m θ_m(Ω(τ))⁸ ≠ 0`,
the `k`-th elementary symmetric function of the ten `θ_m(Ω(τ))⁸` (`m` even) is
`R_k(j_θ(Ω(τ)))·(Σ_m θ_m(Ω(τ))⁸)^k`.

Why true (model argument, no human review; locators UNVERIFIED): `e_k(θ_m⁸)` is a Siegel modular form of
weight `4k` for `Sp₄(ℤ)` (the theta transformation formula permutes the `θ_m⁸` with the common factor
`det(CΩ+D)⁴`; Igusa, *Theta functions*, 1972, Ch. V), with rational Fourier coefficients, hence a
polynomial over `ℚ` in Igusa's `ψ₄, ψ₆, χ₁₀, χ₁₂` (Igusa, Amer. J. Math. 84 (1962), 86 (1964)); along the
QM curve `[ψ₄ : ψ₆ : 2¹²3⁵χ₁₀ : 2¹²3⁶χ₁₂] = [j : j² : j³ : j³(j+1)]` weighted-projectively (Lin–Yang,
arXiv:1807.00466v1, Example 29; Baba–Granath, Canad. J. Math. 60 (2008), Prop. 3.6; the manuscript's F1
input, as restated in scratch/h-v14/igusa_check.py), and `ψ₄ = Σθ⁸/4`. This needs the same identification
of `τ ↦ Ω(τ)` with the QM locus as F1 (`FibreQMPeriod`, `PkgI1.QMHauptmodul`). The explicit
`R_k` are in `qmR` (`QMThetaSymmetricCore`). -/
def QMThetaSymmetric : Prop :=
  ∃ R : ℕ → Polynomial ℚ, ∀ τ : ℂ, 0 < τ.im → PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 →
    ∀ k ≤ 10, (thetaEight (PkgI1.Omega τ)).esymm k =
      Polynomial.aeval (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)) (R k) *
        PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k

/-- A root of a monic polynomial over `ℂ` whose elementary symmetric functions are rational is
algebraic (Vieta + lifting of monic polynomials). -/
theorem isAlgebraic_of_esymm (s : Multiset ℂ) (r : ℕ → ℚ)
    (hs : ∀ k ≤ Multiset.card s, s.esymm k = (r k : ℂ)) {y : ℂ} (hy : y ∈ s) :
    IsAlgebraic ℚ y := by
  have hmon : (s.map (fun t => X - C t)).prod.Monic :=
    monic_multiset_prod_of_monic _ _ (fun t _ => monic_X_sub_C t)
  have hlift : (s.map (fun t => X - C t)).prod ∈ lifts (algebraMap ℚ ℂ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ Multiset.card s
    · rw [Multiset.prod_X_sub_C_coeff s hn, hs _ (Nat.sub_le _ _)]
      exact ⟨(-1) ^ (Multiset.card s - n) * r (Multiset.card s - n), by simp⟩
    · rw [coeff_eq_zero_of_natDegree_lt]
      · exact ⟨0, by simp⟩
      · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift hmon
  refine ⟨Q, hQm.ne_zero, ?_⟩
  rw [aeval_def, eval₂_eq_eval_map, hQ, eval_multiset_prod]
  apply Multiset.prod_eq_zero
  rw [Multiset.map_map]
  exact Multiset.mem_map.mpr ⟨y, hy, by simp⟩

theorem zero_mem_evenChars : ((0, 0) : Char2) ∈ PkgI1.evenChars := by decide

theorem isOddChar_of_not_even {m : Char2} (hm : m ∉ PkgI1.evenChars) : IsOddChar m := by
  unfold IsOddChar
  simp only [PkgI1.evenChars, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  omega

/-- **The use form from the symmetric-function glue (proved).** With `S = Σθ_m⁸ ≠ 0` (from
`jDen ≠ 0`), each `θ_m⁸/S` is a root of `∏_m (X − θ_m⁸/S)`, whose coefficients `±e_k/S^k = ±R_k(q)`
are rational; `θ_{(0,0)} ≠ 0` (from `jNum ≠ 0`), so `(θ_m/θ_{(0,0)})⁸` is algebraic; odd `θ_m` vanish. -/
theorem thetaRatiosAtQM_of_symmetric (h : QMThetaSymmetric) : ThetaRatiosAtQM := by
  obtain ⟨R, hR⟩ := h
  intro τ hτ q hq hJ
  have hDen : PkgI1.jDen (PkgI1.Omega τ) ≠ 0 := by
    intro h0; rw [h0, div_zero] at hJ; exact hq (by exact_mod_cast hJ.symm)
  have hNum : PkgI1.jNum (PkgI1.Omega τ) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hJ; exact hq (by exact_mod_cast hJ.symm)
  have hS : PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 := by
    intro h0; apply hDen; rw [PkgI1.jDen, h0]; ring
  have hProd : PkgI1.thetaProd2 (PkgI1.Omega τ) ≠ 0 := by
    intro h0; apply hNum; rw [PkgI1.jNum, h0]; ring
  set S := PkgI1.thetaSum8 (PkgI1.Omega τ) with hSdef
  -- conversion to pkg-I1's theta constants
  have hconv : ∀ m, thetaConst (BPAnalytic.QM.Omega τ) m = PkgI1.thetaConst m (PkgI1.Omega τ) :=
    fun m => by rw [thetaConst_eq_pkgI1, omega_eq]
  have h00 : PkgI1.thetaConst (0, 0) (PkgI1.Omega τ) ≠ 0 := by
    have := (Finset.prod_ne_zero_iff.mp hProd) _ zero_mem_evenChars
    exact fun h0 => this (by rw [h0]; ring)
  -- the scaled multiset has rational elementary symmetric functions
  set s' := (thetaEight (PkgI1.Omega τ)).map (fun t => S⁻¹ • t) with hs'
  have hcard : Multiset.card s' = 10 := by rw [hs', Multiset.card_map, card_thetaEight]
  have hesymm : ∀ k ≤ Multiset.card s', s'.esymm k = ((Polynomial.eval q (R k) : ℚ) : ℂ) := by
    intro k hk
    rw [hcard] at hk
    rw [hs', ← Multiset.pow_smul_esymm, hR τ hτ hS k hk, hJ, smul_eq_mul]
    have : Polynomial.aeval (q : ℂ) (R k) = ((Polynomial.eval q (R k) : ℚ) : ℂ) := by
      rw [← map_ratCast (algebraMap ℚ ℂ) q, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      simp
    rw [this, inv_pow, ← mul_assoc, mul_comm _ ((Polynomial.eval q (R k) : ℚ) : ℂ), mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hS), mul_one]
  have halg8 : ∀ m ∈ PkgI1.evenChars, IsAlgebraic ℚ (S⁻¹ * PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8) :=
    fun m hm => isAlgebraic_of_esymm s' _ hesymm
      (Multiset.mem_map.mpr ⟨_, Multiset.mem_map.mpr ⟨m, hm, rfl⟩, rfl⟩)
  refine ⟨(0, 0), by rw [hconv]; exact h00, fun m => ?_⟩
  rw [hconv, hconv]
  by_cases hm : m ∈ PkgI1.evenChars
  · apply IsAlgebraic.of_pow (n := 8) (by norm_num)
    have : (PkgI1.thetaConst m (PkgI1.Omega τ) / PkgI1.thetaConst (0, 0) (PkgI1.Omega τ)) ^ 8 =
        (S⁻¹ * PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8) *
          (S⁻¹ * PkgI1.thetaConst (0, 0) (PkgI1.Omega τ) ^ 8)⁻¹ := by
      field_simp
    rw [this]
    exact (halg8 m hm).mul (halg8 _ zero_mem_evenChars).inv
  · have h0 : PkgI1.thetaConst m (PkgI1.Omega τ) = 0 := by
      rw [← hconv]; exact thetaConst_odd _ m (isOddChar_of_not_even hm)
    rw [h0, zero_div]
    exact isAlgebraic_zero

/-! ## 3. The explicit polynomials -/

/-- The polynomials `R_k` (`py/fit_hp.py`, 80-digit numerics; rational reconstruction with residual
`≤ 5·10⁻⁷⁵` at independent points): `E_k/E_1^k = R_k(j)` along the QM curve. -/
def qmR : ℕ → Polynomial ℚ
  | 0 => 1
  | 1 => 1
  | 2 => C (3 / 8)
  | 3 => C (283 / 3888) + C (1 / 972) * X
  | 4 => C (1529 / 186624) - C (1 / 1458) * X
  | 5 => C (13 / 23328) + C (17 / 314928) * X
  | 6 => C (521 / 22674816) + C (95 / 5668704) * X + C (1 / 2834352) * X ^ 2
  | 7 => C (19 / 34012224) + C (313 / 272097792) * X - C (1 / 2834352) * X ^ 2
  | 8 => C (1 / 136048896) + C (107 / 3673320192) * X + C (49 / 1836660096) * X ^ 2
  | 9 => C (1 / 24794911296) * (1 + C (9 / 8) * X + C (1 / 4) * X ^ 2 + X ^ 3)
  | 10 => C (1 / 14281868906496) * X ^ 2
  | _ => 0

/-- **GLUE (explicit form of `QMThetaSymmetric`, `2 ≤ k ≤ 9`; numerically VERIFIED, not proved).**
For `τ` in the upper half-plane with `Σθ_m(Ω(τ))⁸ ≠ 0` and `2 ≤ k ≤ 9`:
`e_k(θ_m(Ω(τ))⁸) = R_k(j_θ(Ω(τ)))·(Σθ_m(Ω(τ))⁸)^k` with the explicit `R_k = qmR k`. For `k = 2` this is
the global Siegel identity `Σθ_m¹⁶ = (Σθ_m⁸)²/4` (weight 8 has dimension 1; Igusa 1964, UNVERIFIED);
for `3 ≤ k ≤ 9` it is the restriction to the QM curve of Igusa's expressions of `e_k(θ⁸)` with
Lin–Yang's vector (see `QMThetaSymmetric`); `k = 3` was cross-checked against Lin–Yang's vector
(`py/lycheck.py`). Checked numerically at 30 points (`py/verify.py`). -/
def QMThetaSymmetricCore : Prop :=
  ∀ τ : ℂ, 0 < τ.im → PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 → ∀ k, 2 ≤ k → k ≤ 9 →
    (thetaEight (PkgI1.Omega τ)).esymm k =
      Polynomial.aeval (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)) (qmR k) *
        PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k

/-- `k = 1`: `e_1 = Σθ⁸` (definition). -/
theorem esymm_one (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    (thetaEight Ω).esymm 1 = PkgI1.thetaSum8 Ω := by
  rw [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
  simp only [Function.comp_def, Multiset.prod_singleton, Multiset.map_id']
  rw [thetaEight, Finset.sum_map_val]
  rfl

/-- `k = 10`: `e_10 = ∏θ⁸ = j²S¹⁰/3779136²` when `S ≠ 0` (definitions of `jNum`, `jDen`). -/
theorem esymm_ten (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hS : PkgI1.thetaSum8 Ω ≠ 0) :
    (thetaEight Ω).esymm 10 =
      (1 / 14281868906496 : ℂ) * (PkgI1.jNum Ω / PkgI1.jDen Ω) ^ 2 * PkgI1.thetaSum8 Ω ^ 10 := by
  have hcard := card_thetaEight Ω
  have hprod : (thetaEight Ω).esymm 10 = (thetaEight Ω).prod := by
    rw [← hcard, Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton,
      Multiset.sum_singleton]
  have hprodP : (thetaEight Ω).prod = PkgI1.thetaProd2 Ω ^ 4 := by
    rw [thetaEight, Finset.prod_map_val, PkgI1.thetaProd2, ← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun m _ => by ring)
  rw [hprod, hprodP, PkgI1.jNum, PkgI1.jDen]
  field_simp
  ring

/-- The explicit identities for all `k ≤ 10` from the core (`k = 0, 1, 10` are identities). -/
theorem qmR_identity (h : QMThetaSymmetricCore) (τ : ℂ) (hτ : 0 < τ.im)
    (hS : PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0) (k : ℕ) (hk : k ≤ 10) :
    (thetaEight (PkgI1.Omega τ)).esymm k =
      Polynomial.aeval (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)) (qmR k) *
        PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k := by
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · interval_cases k
    · simp [qmR]
    · simp [qmR, esymm_one]
  · rcases Nat.lt_or_ge k 10 with h10 | h10
    · exact h τ hτ hS k h2 (by omega)
    · obtain rfl : k = 10 := by omega
      rw [esymm_ten _ hS]
      simp [qmR]

/-- **`QMThetaSymmetric` from the explicit core (proved):** `R = qmR`. -/
theorem qmThetaSymmetric_of_core (h : QMThetaSymmetricCore) : QMThetaSymmetric :=
  ⟨qmR, qmR_identity h⟩

/-! ## 4. Summary -/

/-- **`ThetaPointOfFibre` from `FibreQMPeriod` and the explicit core (proved).** -/
theorem thetaPointOfFibre_of_qm_core (hQM : FibreQMPeriod) (h : QMThetaSymmetricCore) :
    ThetaPointOfFibre :=
  thetaPointOfFibre_of_qm_atQM hQM (thetaRatiosAtQM_of_symmetric (qmThetaSymmetric_of_core h))


/-! ## 5. Route 2: Shimura's CM theorem and interpolation (the arithmetic input at CM points only)

`QMThetaSymmetric` asks for polynomials over `ℚ`; algebraicity only needs algebraic coefficients. Those
follow from the *shape* of the identity (an analytic statement, `QMThetaShape`) and the values at four
CM points of the curve, where Shimura's theorem on theta-nulls at CM points applies
(`ShimuraCMThetaAlgebraic`): Lagrange interpolation. -/

/-- The lattice `Ωℤ² + ℤ²` is stable under multiplication by the scalar `w` (for `w ∉ ℝ`: the
principally polarized torus `ℂ²/(Ωℤ² + ℤ²)` has complex multiplication by the imaginary quadratic
order `ℤ[w]` acting by scalars, so it is isogenous to `E²` for a CM elliptic curve `E`). -/
def ScalarCM (Ω : Matrix (Fin 2) (Fin 2) ℂ) (w : ℂ) : Prop :=
  ∀ a b : Fin 2 → ℤ, ∃ c d : Fin 2 → ℤ,
    w • (Ω.mulVec (fun i => (a i : ℂ)) + fun i => (b i : ℂ)) =
      Ω.mulVec (fun i => (c i : ℂ)) + fun i => (d i : ℂ)

/-- **LEAF (consequence of Shimura's theorem on theta-null values at CM points).** For `Ω ∈ 𝔥₂` whose
period lattice `Ωℤ² + ℤ²` is stable under a non-real scalar `w`, every theta-constant ratio
`θ_m(0, Ω)/θ_{m'}(0, Ω)` with `θ_{m'}(0, Ω) ≠ 0` is an algebraic number.

Sources (locators UNVERIFIED, no network): Shimura, *Theta functions with complex multiplication*,
Duke Math. J. 43 (1976), 673–696 (theta values at CM points are algebraic, with reciprocity), equivalently
Shimura's theorem that Siegel modular functions with algebraic Fourier coefficients take algebraic values
at CM points (Shimura, Ann. of Math. 102 (1975); `θ_m/θ_{m'}` is a modular function of level `(4,8)`
with coefficients in `ℚ(ζ₈)`). The hypothesis makes `ℂ²/(Ωℤ²+ℤ²)` of CM type: `Λ ⊗ ℚ` is a 2-dimensional
`K = ℚ(w)`-space on which `K ⊗ ℝ = ℂ` acts by scalars, so the torus is isogenous to `(ℂ/𝒪_K)²`
(elementary). Form: the published statement restricted to this kind of CM point (weaker). -/
def ShimuraCMThetaAlgebraic : Prop :=
  ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → ∀ w : ℂ, w.im ≠ 0 → ScalarCM Ω w →
    ∀ m m' : Char2, thetaConst Ω m' ≠ 0 → IsAlgebraic ℚ (thetaConst Ω m / thetaConst Ω m')

/-- **GLUE (analytic; the shape of `QMThetaSymmetric`).** There are `R_k ∈ ℂ[X]` of degree `≤ 3` with
`e_k(θ_m(Ω(τ))⁸) = R_k(j_θ(Ω(τ)))·(Σθ_m(Ω(τ))⁸)^k` for all `τ ∈ ℍ` with `Σθ_m⁸ ≠ 0`, `k ≤ 10`.
No arithmetic: `E_k/E_1^k ∘ Ω` is invariant under `Γ*` (theta transformation formula through the
modular embedding `Ω(γτ) = M_γ·Ω(τ)`, pkg-I1 §4), meromorphic on the compact curve `Γ*\ℍ` with
Hauptmodul `j_θ ∘ Ω` (`PkgI1.QMHauptmodul`), with poles only at the zeros of `E_1 ∘ Ω`, so a polynomial in
`j_θ`; degree `⌊k/3⌋ ≤ 3` (observed numerically, `py/fit_hp.py`). It follows from `QMThetaSymmetricCore`
(`qmThetaShape_of_core`). -/
def QMThetaShape : Prop :=
  ∃ R : ℕ → Polynomial ℂ, (∀ k, (R k).natDegree ≤ 3) ∧
    ∀ τ : ℂ, 0 < τ.im → PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 →
      ∀ k ≤ 10, (thetaEight (PkgI1.Omega τ)).esymm k =
        (R k).eval (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)) *
          PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k

/-- **GLUE (four CM points on the curve).** There are `τ₁, …, τ₄ ∈ ℍ` such that each `Ω(τᵢ)` has
scalar CM, `Σθ_m(Ω(τᵢ))⁸ ≠ 0`, and the values `j_θ(Ω(τᵢ))` are pairwise distinct. Candidates
(`py/cmnodes.py`, numerically): the fixed points of `ι(μ)` for `μ ∈ 𝒪` of discriminants `−4, −19, −24,
−40`, with `j_θ = 0, 81/64, −16/27, 1296/125` (Elkies' values); the scalar is `w = cτ + d` for
`ι(μ) = [[a, b], [c, d]]`, since `ι(x)·w(τ,1)ᵀ = ι(xμ)(τ,1)ᵀ ∈ ι(𝒪)(τ,1)ᵀ` and `F'(τ)` is `ℂ`-linear. -/
def QMCMNodes : Prop :=
  ∃ τ : Fin 4 → ℂ, (∀ i, 0 < (τ i).im) ∧
    (∀ i, ∃ w : ℂ, w.im ≠ 0 ∧ ScalarCM (PkgI1.Omega (τ i)) w) ∧
    (∀ i, PkgI1.thetaSum8 (PkgI1.Omega (τ i)) ≠ 0) ∧
    Function.Injective (fun i => PkgI1.jNum (PkgI1.Omega (τ i)) / PkgI1.jDen (PkgI1.Omega (τ i)))

/-- The explicit core gives the shape (`R_k = qmR k` mapped to `ℂ`; degrees `≤ 3`). -/
theorem qmThetaShape_of_core (h : QMThetaSymmetricCore) : QMThetaShape := by
  refine ⟨fun k => (qmR k).map (algebraMap ℚ ℂ), fun k => ?_, fun τ hτ hS k hk => ?_⟩
  · refine natDegree_map_le.trans ?_
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp only [qmR] <;>
      compute_degree!
  · rw [eval_map_algebraMap]
    exact qmR_identity h τ hτ hS k hk

local notation "𝔸" => algebraicClosure ℚ ℂ

/-- A root of a monic polynomial whose elementary symmetric functions are algebraic is algebraic. -/
theorem mem_of_esymm_mem (s : Multiset ℂ) (hs : ∀ k ≤ Multiset.card s, s.esymm k ∈ 𝔸) {y : ℂ}
    (hy : y ∈ s) : y ∈ 𝔸 := by
  have hmon : (s.map (fun t => X - C t)).prod.Monic :=
    monic_multiset_prod_of_monic _ _ (fun t _ => monic_X_sub_C t)
  have hlift : (s.map (fun t => X - C t)).prod ∈ lifts (algebraMap 𝔸 ℂ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ Multiset.card s
    · rw [Multiset.prod_X_sub_C_coeff s hn]
      have : (-1 : ℂ) ^ (Multiset.card s - n) * s.esymm (Multiset.card s - n) ∈ 𝔸 :=
        mul_mem (pow_mem (neg_mem (one_mem _)) _) (hs _ (Nat.sub_le _ _))
      exact ⟨⟨_, this⟩, rfl⟩
    · rw [coeff_eq_zero_of_natDegree_lt]
      · exact ⟨0, by simp⟩
      · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift hmon
  have hA : IsAlgebraic 𝔸 y := by
    refine ⟨Q, hQm.ne_zero, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, hQ, eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map]
    exact Multiset.mem_map.mpr ⟨y, hy, by simp⟩
  exact mem_algebraicClosure_iff.mpr (hA.restrictScalars ℚ)

/-- Elementary symmetric functions of algebraic numbers are algebraic. -/
theorem esymm_mem (s : Multiset ℂ) (h : ∀ x ∈ s, x ∈ 𝔸) (k : ℕ) : s.esymm k ∈ 𝔸 := by
  unfold Multiset.esymm
  refine multiset_sum_mem _ (fun x hx => ?_)
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  exact multiset_prod_mem _ (fun y hy => h y (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hy))

/-- **Interpolation:** a polynomial of degree `≤ 3` with algebraic values at four distinct algebraic
points has algebraic values at algebraic points. -/
theorem eval_mem_of_nodes (R : Polynomial ℂ) (hdeg : R.natDegree ≤ 3) (x : Fin 4 → ℂ)
    (hx : Function.Injective x) (hxA : ∀ i, x i ∈ 𝔸) (hv : ∀ i, R.eval (x i) ∈ 𝔸) {q : ℂ}
    (hq : q ∈ 𝔸) : R.eval q ∈ 𝔸 := by
  have hdeg' : R.degree < (Finset.univ : Finset (Fin 4)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact (degree_le_of_natDegree_le hdeg).trans_lt (by exact_mod_cast (show (3 : ℕ) < 4 by norm_num))
  rw [Lagrange.eq_interpolate (s := Finset.univ) (v := x) (hx.injOn) hdeg']
  simp only [Lagrange.interpolate, LinearMap.coe_mk, AddHom.coe_mk, eval_finsetSum, eval_mul,
    eval_C]
  refine sum_mem (fun i _ => mul_mem (hv i) ?_)
  rw [Lagrange.basis, eval_prod]
  refine prod_mem (fun j _ => ?_)
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  exact mul_mem (inv_mem (sub_mem (hxA i) (hxA j))) (sub_mem hq (hxA j))

/-- At a scalar-CM point with `Σθ⁸ ≠ 0`: `j_θ` and every `e_k(θ⁸)/(Σθ⁸)^k` are algebraic. -/
theorem node_values (hCM : ShimuraCMThetaAlgebraic) {τ : ℂ} (hτ : 0 < τ.im) {w : ℂ} (hw : w.im ≠ 0)
    (hsc : ScalarCM (PkgI1.Omega τ) w) (hS : PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0) :
    PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) ∈ 𝔸 ∧
      ∀ k, (thetaEight (PkgI1.Omega τ)).esymm k / PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k ∈ 𝔸 := by
  set Ω := PkgI1.Omega τ with hΩ
  -- a nonvanishing even theta constant
  obtain ⟨m', hm', hc⟩ : ∃ m' ∈ PkgI1.evenChars, PkgI1.thetaConst m' Ω ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hS
    unfold PkgI1.thetaSum8
    exact Finset.sum_eq_zero (fun m hm => by rw [hall m hm]; ring)
  set c := PkgI1.thetaConst m' Ω with hcdef
  have hr : ∀ m, PkgI1.thetaConst m Ω / c ∈ 𝔸 := by
    intro m
    have := hCM Ω (isSiegel_Omega hτ) w hw hsc m m' (by rw [thetaConst_eq_pkgI1]; exact hc)
    rw [thetaConst_eq_pkgI1, thetaConst_eq_pkgI1] at this
    exact mem_algebraicClosure_iff.mpr this
  have hc8 : c ^ 8 ≠ 0 := pow_ne_zero _ hc
  -- scaled multiset
  have hscaled : ∀ k, (c ^ 8)⁻¹ ^ k * (thetaEight Ω).esymm k ∈ 𝔸 := by
    intro k
    have e := Multiset.pow_smul_esymm ((c ^ 8)⁻¹) k (thetaEight Ω)
    simp only [smul_eq_mul] at e
    rw [e]
    refine esymm_mem _ (fun x hx => ?_) k
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨m, -, rfl⟩ := Multiset.mem_map.mp hy
    have : (c ^ 8)⁻¹ * PkgI1.thetaConst m Ω ^ 8 = (PkgI1.thetaConst m Ω / c) ^ 8 := by
      field_simp
    rw [this]; exact pow_mem (hr m) _
  have hS' : (c ^ 8)⁻¹ * PkgI1.thetaSum8 Ω ∈ 𝔸 := by
    have := hscaled 1
    rwa [pow_one, esymm_one] at this
  have hS'0 : (c ^ 8)⁻¹ * PkgI1.thetaSum8 Ω ≠ 0 := mul_ne_zero (inv_ne_zero hc8) hS
  constructor
  · have hP : (c ^ 20)⁻¹ * PkgI1.thetaProd2 Ω ∈ 𝔸 := by
      have : (c ^ 20)⁻¹ * PkgI1.thetaProd2 Ω =
          ∏ m ∈ PkgI1.evenChars, (PkgI1.thetaConst m Ω / c) ^ 2 := by
        rw [PkgI1.thetaProd2]
        simp_rw [div_pow]
        rw [Finset.prod_div_distrib, Finset.prod_const, PkgI1.card_evenChars, ← pow_mul,
          div_eq_mul_inv, mul_comm]
      rw [this]; exact prod_mem (fun m _ => pow_mem (hr m) _)
    have : PkgI1.jNum Ω / PkgI1.jDen Ω =
        3779136 * ((c ^ 20)⁻¹ * PkgI1.thetaProd2 Ω) ^ 2 / ((c ^ 8)⁻¹ * PkgI1.thetaSum8 Ω) ^ 5 := by
      rw [PkgI1.jNum, PkgI1.jDen]
      field_simp
    rw [this]
    exact div_mem (mul_mem (by exact_mod_cast (𝔸).algebraMap_mem (3779136 : ℚ)) (pow_mem hP _))
      (pow_mem hS' _)
  · intro k
    have : (thetaEight Ω).esymm k / PkgI1.thetaSum8 Ω ^ k =
        ((c ^ 8)⁻¹ ^ k * (thetaEight Ω).esymm k) / ((c ^ 8)⁻¹ * PkgI1.thetaSum8 Ω) ^ k := by
      rw [mul_pow, mul_div_mul_left _ _ (pow_ne_zero _ (inv_ne_zero hc8))]
    rw [this]
    exact div_mem (hscaled k) (pow_mem hS' _)

/-- **Route 2 (proved):** the use form from the analytic shape, four CM nodes and Shimura's CM theorem. -/
theorem thetaRatiosAtQM_of_cm (hSh : QMThetaShape) (hN : QMCMNodes)
    (hCM : ShimuraCMThetaAlgebraic) : ThetaRatiosAtQM := by
  obtain ⟨R, hdeg, hR⟩ := hSh
  obtain ⟨τ₀, hτ₀, hcm, hS₀, hinj⟩ := hN
  -- `R_k(q)` is algebraic for every rational `q`
  have hRq : ∀ k ≤ 10, ∀ q : ℚ, (R k).eval (q : ℂ) ∈ 𝔸 := by
    intro k hk q
    have hnode : ∀ i, PkgI1.jNum (PkgI1.Omega (τ₀ i)) / PkgI1.jDen (PkgI1.Omega (τ₀ i)) ∈ 𝔸 ∧
        ∀ k, (thetaEight (PkgI1.Omega (τ₀ i))).esymm k /
          PkgI1.thetaSum8 (PkgI1.Omega (τ₀ i)) ^ k ∈ 𝔸 := fun i => by
      obtain ⟨w, hw, hsc⟩ := hcm i
      exact node_values hCM (hτ₀ i) hw hsc (hS₀ i)
    refine eval_mem_of_nodes (R k) (hdeg k) _ hinj (fun i => (hnode i).1) (fun i => ?_)
      (by exact_mod_cast (𝔸).algebraMap_mem q)
    have h1 := (hnode i).2 k
    rw [hR (τ₀ i) (hτ₀ i) (hS₀ i) k hk, mul_div_cancel_right₀ _ (pow_ne_zero _ (hS₀ i))] at h1
    exact h1
  intro τ hτ q hq hJ
  have hDen : PkgI1.jDen (PkgI1.Omega τ) ≠ 0 := by
    intro h0; rw [h0, div_zero] at hJ; exact hq (by exact_mod_cast hJ.symm)
  have hNum : PkgI1.jNum (PkgI1.Omega τ) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hJ; exact hq (by exact_mod_cast hJ.symm)
  have hS : PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 := by
    intro h0; apply hDen; rw [PkgI1.jDen, h0]; ring
  have hProd : PkgI1.thetaProd2 (PkgI1.Omega τ) ≠ 0 := by
    intro h0; apply hNum; rw [PkgI1.jNum, h0]; ring
  set S := PkgI1.thetaSum8 (PkgI1.Omega τ) with hSdef
  have hconv : ∀ m, thetaConst (BPAnalytic.QM.Omega τ) m = PkgI1.thetaConst m (PkgI1.Omega τ) :=
    fun m => by rw [thetaConst_eq_pkgI1, omega_eq]
  have h00 : PkgI1.thetaConst (0, 0) (PkgI1.Omega τ) ≠ 0 := by
    have := (Finset.prod_ne_zero_iff.mp hProd) _ zero_mem_evenChars
    exact fun h0 => this (by rw [h0]; ring)
  set s' := (thetaEight (PkgI1.Omega τ)).map (fun t => S⁻¹ • t) with hs'
  have hcard : Multiset.card s' = 10 := by rw [hs', Multiset.card_map, card_thetaEight]
  have hesymm : ∀ k ≤ Multiset.card s', s'.esymm k ∈ 𝔸 := by
    intro k hk
    rw [hcard] at hk
    rw [hs', ← Multiset.pow_smul_esymm, hR τ hτ hS k hk, hJ, smul_eq_mul, inv_pow, ← mul_assoc,
      mul_comm _ ((R k).eval (q : ℂ)), mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hS), mul_one]
    exact hRq k hk q
  have halg8 : ∀ m ∈ PkgI1.evenChars, S⁻¹ * PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8 ∈ 𝔸 :=
    fun m hm => mem_of_esymm_mem s' hesymm
      (Multiset.mem_map.mpr ⟨_, Multiset.mem_map.mpr ⟨m, hm, rfl⟩, rfl⟩)
  refine ⟨(0, 0), by rw [hconv]; exact h00, fun m => ?_⟩
  rw [hconv, hconv]
  by_cases hm : m ∈ PkgI1.evenChars
  · apply IsAlgebraic.of_pow (n := 8) (by norm_num)
    have : (PkgI1.thetaConst m (PkgI1.Omega τ) / PkgI1.thetaConst (0, 0) (PkgI1.Omega τ)) ^ 8 =
        (S⁻¹ * PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8) /
          (S⁻¹ * PkgI1.thetaConst (0, 0) (PkgI1.Omega τ) ^ 8) := by
      field_simp
    rw [this]
    exact mem_algebraicClosure_iff.mp (div_mem (halg8 m hm) (halg8 _ zero_mem_evenChars))
  · have h0 : PkgI1.thetaConst m (PkgI1.Omega τ) = 0 := by
      rw [← hconv]; exact thetaConst_odd _ m (isOddChar_of_not_even hm)
    rw [h0, zero_div]
    exact isAlgebraic_zero

/-- **`ThetaPointOfFibre` by Route 2 (proved).** -/
theorem thetaPointOfFibre_of_qm_cm (hQM : FibreQMPeriod) (hSh : QMThetaShape) (hN : QMCMNodes)
    (hCM : ShimuraCMThetaAlgebraic) : ThetaPointOfFibre :=
  thetaPointOfFibre_of_qm_atQM hQM (thetaRatiosAtQM_of_cm hSh hN hCM)

end HDec.HSyn.G0Split.ThetaPt.ThetaSplit

#print axioms HDec.HSyn.G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_atQM
#print axioms HDec.HSyn.G0Split.ThetaPt.ThetaSplit.thetaRatiosAtQM_of_symmetric
#print axioms HDec.HSyn.G0Split.ThetaPt.ThetaSplit.qmThetaSymmetric_of_core
#print axioms HDec.HSyn.G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_core
#print axioms HDec.HSyn.G0Split.ThetaPt.ThetaSplit.qmThetaShape_of_core
#print axioms HDec.HSyn.G0Split.ThetaPt.ThetaSplit.thetaRatiosAtQM_of_cm
#print axioms HDec.HSyn.G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_cm
