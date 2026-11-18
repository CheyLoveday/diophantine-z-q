import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.TorsionCancel

/-!
# Torsion, part 8: the mapping cone of a chain map of acyclic based complexes

For a degree-preserving chain map `f : C → D` of based complexes over a field (`ChainMapB`), the
**mapping cone** `cone f` has `cone^n = D^n ⊕ C^{n+1}` and differential `(d, c) ↦ (d_D d + f c,
−d_C c)`; in the even/odd split its even basis is `κe(D) ⊕ κo(C)` and its odd basis
`κo(D) ⊕ κe(C)` (`BasedCx.cone`).

* `torsion_rebase'` (no contraction hypothesis): a graded change of basis multiplies the torsion by
  `det P_od · det P_ev⁻¹`.
* `negCx`, `torsion_negCx`: negating the differential multiplies the torsion by `(−1)^{|κo|}`.
* **`torsion_cone` (PROVED)**: if `C` and `D` are acyclic,
  `τ(cone f) = τ(D) · ((−1)^{|κo(C)|} τ(C))⁻¹` (orientation `σ_D ⊕ σ_C⁻¹`): with a contraction `h`
  of `D`, the unipotent graded change of basis `[[1, −h f], [0, 1]]` carries `cone f` to
  `D ⊕ C[1]` (`cone_rebase_eq`), and the shift inverts the torsion (lane ClearingComplex's
  `torsion_shift`).
* `torsion_eq_of_cone` (the form used for coordinates): `τ(C) = (−1)^{|κo(C)|} τ(D) / τ(cone f)`.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Torsion

open Matrix ZInQ.Contrib.CloudB3RC53.ClearingComplex

variable {K : Type*} [Field K]
variable {κe κo κe' κo' : Type*} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]
  [Fintype κe'] [Fintype κo'] [DecidableEq κe'] [DecidableEq κo']

/-! ### Change of basis without a contraction hypothesis -/

/-- **A graded change of basis multiplies the torsion by `det P_od · det Q_ev`.** -/
theorem torsion_rebase' (C : BasedCx K κe κo) (P : GradedBasisChange C) (σ : κe ≃ κo) :
    torsion (C.rebase P) σ = P.Po.det * torsion C σ * P.Qe.det := by
  by_cases hC : Nonempty (Contraction C)
  · obtain ⟨h⟩ := hC
    rw [← tau_eq_torsion _ (h.rebase P), ← tau_eq_torsion _ h, tau_rebase]
  · have hC' : ¬ Nonempty (Contraction (C.rebase P)) := by
      rintro ⟨h⟩
      exact hC ⟨rebase_inv' C P ▸ h.rebase (basisInv P)⟩
    unfold torsion
    simp only [hC, hC', dite_false, mul_zero, zero_mul]

/-! ### Negating the differential -/

/-- The basis change negating the odd basis vectors. -/
def negBasis (C : BasedCx K κe κo) : GradedBasisChange C where
  Pe := 1
  Qe := 1
  Po := -1
  Qo := -1
  hPQe := Matrix.one_mul 1
  hPQo := by rw [neg_mul_neg, Matrix.one_mul]
  deg_Pe := hasDeg_one _
  deg_Qe := hasDeg_one _
  deg_Po := (hasDeg_one _).neg
  deg_Qo := (hasDeg_one _).neg

/-- The complex with negated differential. -/
abbrev negCx (C : BasedCx K κe κo) : BasedCx K κe κo := C.rebase (negBasis C)

theorem negCx_dOE (C : BasedCx K κe κo) : (negCx C).dOE = -C.dOE := by
  change -1 * C.dOE * 1 = _
  rw [Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]

theorem negCx_dEO (C : BasedCx K κe κo) : (negCx C).dEO = -C.dEO := by
  change 1 * C.dEO * -1 = _
  rw [Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one]

/-- **Negating the differential multiplies the torsion by `(−1)^{|κo|}`.** -/
theorem torsion_negCx (C : BasedCx K κe κo) (σ : κe ≃ κo) :
    torsion (negCx C) σ = (-1) ^ Fintype.card κo * torsion C σ := by
  rw [torsion_rebase']
  change (-1 : Matrix κo κo K).det * torsion C σ * (1 : Matrix κe κe K).det = _
  rw [det_one, mul_one, det_neg, det_one, mul_one]

/-! ### Chain maps and cones -/

/-- **A degree-preserving chain map** of based complexes. -/
structure ChainMapB (C : BasedCx K κe κo) (D : BasedCx K κe' κo') where
  fE : Matrix κe' κe K
  fO : Matrix κo' κo K
  deg_fE : HasDeg fE D.degE C.degE 0
  deg_fO : HasDeg fO D.degO C.degO 0
  commOE : D.dOE * fE = fO * C.dOE
  commEO : D.dEO * fO = fE * C.dEO

variable {C : BasedCx K κe κo} {D : BasedCx K κe' κo'}

/-- **The mapping cone** `cone^n = D^n ⊕ C^{n+1}`, `d(d, c) = (d_D d + f c, −d_C c)`. -/
def BasedCx.cone (f : ChainMapB C D) : BasedCx K (κe' ⊕ κo) (κo' ⊕ κe) where
  degE := Sum.elim D.degE (fun c => C.degO c + -1)
  degO := Sum.elim D.degO (fun c => C.degE c + -1)
  even_degE := by rintro (i | i); exacts [D.even_degE i, (C.odd_degO i).add_odd odd_neg_one]
  odd_degO := by rintro (i | i); exacts [D.odd_degO i, (C.even_degE i).add_odd odd_neg_one]
  dOE := fromBlocks D.dOE f.fO 0 (-C.dEO)
  dEO := fromBlocks D.dEO f.fE 0 (-C.dOE)
  dd_E := by
    rw [fromBlocks_multiply]
    simp [D.dd_E, C.dd_O, f.commEO]
  dd_O := by
    rw [fromBlocks_multiply]
    simp [D.dd_O, C.dd_E, f.commOE]
  deg_dOE := by
    rintro (i | i) (j | j) h
    · exact D.deg_dOE i j h
    · have := f.deg_fO i j h; change D.degO i = C.degO j + -1 + 1; omega
    · exact absurd rfl h
    · have := C.deg_dEO i j (by simpa using h); change C.degE i + -1 = C.degO j + -1 + 1; omega
  deg_dEO := by
    rintro (i | i) (j | j) h
    · exact D.deg_dEO i j h
    · have := f.deg_fE i j h; change D.degE i = C.degE j + -1 + 1; omega
    · exact absurd rfl h
    · have := C.deg_dOE i j (by simpa using h); change C.degO i + -1 = C.degE j + -1 + 1; omega

/-- The shifted negated complex `C[1]`. -/
abbrev shiftNeg (C : BasedCx K κe κo) : BasedCx K κo κe := shiftCx (negCx C) (-1) odd_neg_one

/-- The unipotent graded change of basis `[[1, −h f], [0, 1]]` of the cone. -/
def coneBasis (f : ChainMapB C D) (hD : Contraction D) : GradedBasisChange (BasedCx.cone f) where
  Pe := fromBlocks 1 (hD.hEO * f.fO) 0 1
  Qe := fromBlocks 1 (-(hD.hEO * f.fO)) 0 1
  Po := fromBlocks 1 (hD.hOE * f.fE) 0 1
  Qo := fromBlocks 1 (-(hD.hOE * f.fE)) 0 1
  hPQe := by rw [fromBlocks_multiply]; simp [← fromBlocks_one]
  hPQo := by rw [fromBlocks_multiply]; simp [← fromBlocks_one]
  deg_Pe := by
    rintro (i | i) (j | j) h
    · exact hasDeg_one _ i j h
    · have := (hD.deg_hEO.mul f.deg_fO) i j h
      change D.degE i = C.degO j + -1 + 0; omega
    · exact absurd rfl h
    · exact hasDeg_one (fun c => C.degO c + -1) i j h
  deg_Qe := by
    rintro (i | i) (j | j) h
    · exact hasDeg_one _ i j h
    · have := (hD.deg_hEO.mul f.deg_fO).neg i j h
      change D.degE i = C.degO j + -1 + 0; omega
    · exact absurd rfl h
    · exact hasDeg_one (fun c => C.degO c + -1) i j h
  deg_Po := by
    rintro (i | i) (j | j) h
    · exact hasDeg_one _ i j h
    · have := (hD.deg_hOE.mul f.deg_fE) i j h
      change D.degO i = C.degE j + -1 + 0; omega
    · exact absurd rfl h
    · exact hasDeg_one (fun c => C.degE c + -1) i j h
  deg_Qo := by
    rintro (i | i) (j | j) h
    · exact hasDeg_one _ i j h
    · have := (hD.deg_hOE.mul f.deg_fE).neg i j h
      change D.degO i = C.degE j + -1 + 0; omega
    · exact absurd rfl h
    · exact hasDeg_one (fun c => C.degE c + -1) i j h

/-- **The cone of a chain map into a contractible complex is, up to a unipotent graded change of
basis, the direct sum `D ⊕ C[1]`.** -/
theorem cone_rebase_eq (f : ChainMapB C D) (hD : Contraction D) :
    (BasedCx.cone f).rebase (coneBasis f hD) = D.sum (shiftNeg C) := by
  apply BasedCx.ext'
  · funext i; rcases i with i | i <;> rfl
  · funext i; rcases i with i | i <;> rfl
  · change fromBlocks 1 (hD.hOE * f.fE) 0 1 * fromBlocks D.dOE f.fO 0 (-C.dEO) *
      fromBlocks 1 (-(hD.hEO * f.fO)) 0 1 = fromBlocks D.dOE 0 0 (negCx C).dEO
    rw [negCx_dEO, fromBlocks_multiply, fromBlocks_multiply]
    have key : D.dOE * -(hD.hEO * f.fO) + (f.fO + hD.hOE * f.fE * -C.dEO) = 0 := by
      have e := hD.htpy_O
      rw [Matrix.mul_neg, Matrix.mul_neg, Matrix.mul_assoc, ← f.commEO, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc]
      calc -(D.dOE * hD.hEO * f.fO) + (f.fO + -(hD.hOE * D.dEO * f.fO))
          = f.fO - (D.dOE * hD.hEO + hD.hOE * D.dEO) * f.fO := by
            rw [Matrix.add_mul]; abel
        _ = 0 := by rw [e, Matrix.one_mul, sub_self]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add]
    congr 1
  · change fromBlocks 1 (hD.hEO * f.fO) 0 1 * fromBlocks D.dEO f.fE 0 (-C.dOE) *
      fromBlocks 1 (-(hD.hOE * f.fE)) 0 1 = fromBlocks D.dEO 0 0 (negCx C).dOE
    rw [negCx_dOE, fromBlocks_multiply, fromBlocks_multiply]
    have key : D.dEO * -(hD.hOE * f.fE) + (f.fE + hD.hEO * f.fO * -C.dOE) = 0 := by
      have e := hD.htpy_E
      rw [Matrix.mul_neg, Matrix.mul_neg, Matrix.mul_assoc, ← f.commOE, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc]
      calc -(D.dEO * hD.hOE * f.fE) + (f.fE + -(hD.hEO * D.dOE * f.fE))
          = f.fE - (D.dEO * hD.hOE + hD.hEO * D.dOE) * f.fE := by
            rw [Matrix.add_mul]; abel
        _ = 0 := by rw [e, Matrix.one_mul, sub_self]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add]
    congr 1

/-- **The torsion of the cone** (PROVED): for acyclic `C`, `D`,
`τ(cone f) = τ(D) · ((−1)^{|κo(C)|} τ(C))⁻¹`. -/
theorem torsion_cone (f : ChainMapB C D) (hC : Contraction C) (hD : Contraction D)
    (σD : κe' ≃ κo') (σC : κe ≃ κo) :
    torsion (BasedCx.cone f) (σD.sumCongr σC.symm) =
      torsion D σD * ((-1) ^ Fintype.card κo * torsion C σC)⁻¹ := by
  have h1 := torsion_rebase' (BasedCx.cone f) (coneBasis f hD) (σD.sumCongr σC.symm)
  have hPo : (coneBasis f hD).Po.det = 1 := by
    change (fromBlocks 1 (hD.hOE * f.fE) 0 1 : Matrix (κo' ⊕ κe) (κo' ⊕ κe) K).det = 1
    rw [det_fromBlocks_zero₂₁, det_one, det_one, mul_one]
  have hQe : (coneBasis f hD).Qe.det = 1 := by
    change (fromBlocks 1 (-(hD.hEO * f.fO)) 0 1 : Matrix (κe' ⊕ κo) (κe' ⊕ κo) K).det = 1
    rw [det_fromBlocks_zero₂₁, det_one, det_one, mul_one]
  rw [hPo, hQe, one_mul, mul_one, cone_rebase_eq f hD] at h1
  have hneg : Contraction (negCx C) := hC.rebase (negBasis C)
  rw [← h1, torsion_sum D (shiftNeg C) hD (shiftContr (-1) odd_neg_one hneg) σD σC.symm,
    torsion_shift, torsion_negCx]

/-- **The form used for coordinates**: `τ(C) = (−1)^{|κo(C)|} τ(D) / τ(cone f)`. -/
theorem torsion_eq_of_cone (f : ChainMapB C D) (hC : Contraction C) (hD : Contraction D)
    (σD : κe' ≃ κo') (σC : κe ≃ κo) :
    torsion C σC = (-1) ^ Fintype.card κo * torsion D σD *
      (torsion (BasedCx.cone f) (σD.sumCongr σC.symm))⁻¹ := by
  rw [torsion_cone f hC hD σD σC]
  have hD' : torsion D σD ≠ 0 := (tau_eq_torsion D hD σD ▸ isUnit_tau D hD σD).ne_zero
  have hs : ((-1 : K) ^ Fintype.card κo) * (-1) ^ Fintype.card κo = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨_, rfl⟩
  rw [mul_inv, inv_inv]
  calc torsion C σC
      = ((-1 : K) ^ Fintype.card κo * (-1) ^ Fintype.card κo) * torsion C σC *
          (torsion D σD * (torsion D σD)⁻¹) := by rw [hs, mul_inv_cancel₀ hD']; ring
    _ = _ := by ring

end ZInQ.Contrib.CloudB3RC53.Torsion
