import ZInQKernel.Contrib.CloudB3RC53.Torsion.Cone

/-!
# The Knudsen–Mumford coordinate is bilinear in the class and the functional

Manuscript `diophantine_zq.tex`, tex 3877–3892 (Definition `ex:arith-coordinate`: the coordinate
of `[z] ⊗ [λ]`) and 4189–4193.

**`kmCoord_smul`** (PROVED): over a field, for nonzero scalars `c` and `e`,
`kmCoord(C, c z, e λ) = c e · kmCoord(C, z, λ)`, for every orientation. The augmented complex at
`(c z, e λ)` is the augmented complex at `(z, λ)` in the bases rescaled by `c` on the degree-zero
augmentation line and by `e` on the degree-three line (`augScale`). The torsion then changes by
`det P_od · det Q_ev = e · c` (`torsion_rebase'`). The two sides of a comparison of models scale
by the same factor, so a comparison with coefficients in a domain can be read on integral
representatives (lane E1's assembly of `KmCoordComparisonLamUnit`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion

variable {K : Type*} [Field K] {ι0 ι1 ι2 ι3 : Type*} [Fintype ι0] [Fintype ι1] [Fintype ι2]
  [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]

/-- Two based complexes with the same gradings and differentials are equal. Kind: PROVED. -/
theorem BasedCx.ext' {R : Type*} [CommRing R] {κe κo : Type*} [Fintype κe] [Fintype κo]
    {X Y : BasedCx R κe κo} (h1 : X.degE = Y.degE) (h2 : X.degO = Y.degO) (h3 : X.dOE = Y.dOE)
    (h4 : X.dEO = Y.dEO) : X = Y := by
  cases X
  cases Y
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

/-- A diagonal matrix has degree zero. Kind: PROVED. -/
theorem hasDeg_diagonal {R : Type*} [CommRing R] {κ : Type*} [DecidableEq κ] (v : κ → R)
    (b : κ → ℤ) : HasDeg (diagonal v) b b 0 := by
  intro i j h
  by_cases hij : i = j
  · rw [hij, add_zero]
  · exact absurd (diagonal_apply_ne v hij) h

/-- The even rescaling: `c` on the degree-zero augmentation line. Kind: definition. -/
def vE (c : K) : (ι0 ⊕ Unit) ⊕ ι2 → K := Sum.elim (Sum.elim (fun _ => 1) (fun _ => c)) (fun _ => 1)

/-- The odd rescaling: `e` on the degree-three augmentation line. Kind: definition. -/
def vO (e : K) : ι1 ⊕ (ι3 ⊕ Unit) → K := Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1) (fun _ => e))

omit [Fintype ι0] [Fintype ι2] [DecidableEq ι0] [DecidableEq ι2] in
theorem vE_ne_zero {c : K} (hc : c ≠ 0) (i : (ι0 ⊕ Unit) ⊕ ι2) : vE (ι0 := ι0) (ι2 := ι2) c i ≠ 0 := by
  rcases i with (i | i) | i <;> simp [vE, hc]

omit [Fintype ι1] [Fintype ι3] [DecidableEq ι1] [DecidableEq ι3] in
theorem vO_ne_zero {e : K} (he : e ≠ 0) (i : ι1 ⊕ (ι3 ⊕ Unit)) : vO (ι1 := ι1) (ι3 := ι3) e i ≠ 0 := by
  rcases i with i | i | i <;> simp [vO, he]

/-- `diagonal v⁻¹ * diagonal v = 1` for a nowhere-zero `v`. Kind: PROVED. -/
theorem diagonal_inv_mul {κ : Type*} [Fintype κ] [DecidableEq κ] {v : κ → K}
    (hv : ∀ i, v i ≠ 0) : diagonal (fun i => (v i)⁻¹) * diagonal v = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (hv i)

/-- `diagonal v * diagonal v⁻¹ = 1`. Kind: PROVED. -/
theorem diagonal_mul_inv {κ : Type*} [Fintype κ] [DecidableEq κ] {v : κ → K}
    (hv : ∀ i, v i ≠ 0) : diagonal v * diagonal (fun i => (v i)⁻¹) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hv i)

/-- **The rescaling of the augmentation lines** as a graded change of basis of the augmented
complex. Kind: definition. -/
def augScale (C : FourCx K ι0 ι1 ι2 ι3) (z : ι1 → K) (lam : ι2 → K) (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) {c e : K} (hc : c ≠ 0) (he : e ≠ 0) :
    GradedBasisChange (C.aug z lam hz hlam).toBased where
  Pe := diagonal fun i => (vE (ι0 := ι0) (ι2 := ι2) c i)⁻¹
  Qe := diagonal (vE c)
  Po := diagonal (vO (ι1 := ι1) (ι3 := ι3) e)
  Qo := diagonal fun i => (vO e i)⁻¹
  hPQe := diagonal_inv_mul (vE_ne_zero hc)
  hPQo := diagonal_mul_inv (vO_ne_zero he)
  deg_Pe := hasDeg_diagonal _ _
  deg_Qe := hasDeg_diagonal _ _
  deg_Po := hasDeg_diagonal _ _
  deg_Qo := hasDeg_diagonal _ _

/-- **The rescaled augmented complex is the augmented complex of the rescaled class and
functional.** Kind: PROVED. -/
theorem aug_smul_eq_rebase (C : FourCx K ι0 ι1 ι2 ι3) (z : ι1 → K) (lam : ι2 → K)
    (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) {c e : K} (hc : c ≠ 0) (he : e ≠ 0)
    (hz' : C.d1 *ᵥ (c • z) = 0) (hlam' : (e • lam) ᵥ* C.d1 = 0) :
    (C.aug (c • z) (e • lam) hz' hlam').toBased =
      (C.aug z lam hz hlam).toBased.rebase (augScale C z lam hz hlam hc he) := by
  refine BasedCx.ext' rfl rfl ?_ ?_
  · change (C.aug (c • z) (e • lam) hz' hlam').toBased.dOE =
      diagonal (vO e) * (C.aug z lam hz hlam).toBased.dOE * diagonal (vE c)
    ext i j
    rw [mul_diagonal, diagonal_mul]
    rcases i with i | i | i <;> rcases j with (j | j) | j <;>
      simp [FourCx.toBased_dOE, FourCx.aug, vE, vO, fromBlocks, fromCols_apply_inl,
        fromCols_apply_inr, fromRows_apply_inl, fromRows_apply_inr, replicateCol, replicateRow,
        mul_comm]
  · change (C.aug (c • z) (e • lam) hz' hlam').toBased.dEO =
      diagonal (fun i => (vE c i)⁻¹) * (C.aug z lam hz hlam).toBased.dEO *
        diagonal (fun i => (vO e i)⁻¹)
    ext i j
    rw [mul_diagonal, diagonal_mul]
    rcases i with (i | i) | i <;> rcases j with j | j | j <;>
      simp [FourCx.toBased_dEO, FourCx.aug, vE, vO, fromBlocks]

/-- **The coordinate is bilinear**: `kmCoord(C, c z, e λ) = c e · kmCoord(C, z, λ)` for nonzero
`c`, `e` (tex 3877–3892). Kind: PROVED. -/
theorem kmCoord_smul (C : FourCx K ι0 ι1 ι2 ι3) (z : ι1 → K) (lam : ι2 → K)
    (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) {c e : K} (hc : c ≠ 0) (he : e ≠ 0)
    (hz' : C.d1 *ᵥ (c • z) = 0) (hlam' : (e • lam) ᵥ* C.d1 = 0)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C (c • z) (e • lam) hz' hlam' σ = c * e * kmCoord C z lam hz hlam σ := by
  unfold kmCoord
  rw [aug_smul_eq_rebase C z lam hz hlam hc he hz' hlam', torsion_rebase']
  change -(det (diagonal (vO (ι1 := ι1) (ι3 := ι3) e)) * _ * det (diagonal (vE (ι0 := ι0)
    (ι2 := ι2) c))) = _
  rw [det_diagonal, det_diagonal]
  simp only [vE, vO, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one,
    Finset.prod_const, Finset.card_univ, Fintype.card_unit, pow_one, one_mul, mul_one]
  ring

end ZInQ.Contrib.CloudB3E1Torsion
