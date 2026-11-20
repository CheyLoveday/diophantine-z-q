import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent

/-!
# The printed definitions of Breuil–Conrad–Diamond–Taylor and the library's objects

`Statement.lean` formalizes the Introduction of Breuil–Conrad–Diamond–Taylor (author manuscript,
pp. 1–3) over Mathlib's cusp forms and the vendored Hecke operators. This file proves that these
objects are the printed ones.

* `heckeTCuspNat_apply_eq_printed`: for a prime `p ∤ N` and every `(a b; c d) ∈ SL₂(ℤ)` with
  `c ≡ 0` and `d ≡ p mod N`, the vendored `T_p` is the printed
  `(f|T_p)(z) = p^{−1} ∑_{i=0}^{p−1} f((z + i)/p) + p^{k−1} (cpz + d)^{−k} f((apz + b)/(cpz + d))`.
* `IsPrintedCuspForm`, `isPrintedCuspForm`, `exists_cuspForm_of_isPrintedCuspForm`,
  `isPrintedCuspForm_iff`: a function `f` on the upper half plane is a cusp form of weight
  `k ≥ 1` and level `N` in the printed sense (holomorphic, `f((az + b)/(cz + d)) = (cz + d)^k f(z)`
  on `Γ₁(N)`, `|f(z)|² (Im z)^k` bounded) exactly when it is a Mathlib cusp form on `Γ₁(N)`.
* `coeff_prime_eq_eigenvalue_mul_coeff_one`: the printed identity `c_p(f) = a_p(f) c_1(f)`.
* `condition2At_iff`: for an eigenform, `L(E, s) = L(f, s)` on a right half-plane is equivalent
  to `c_n(f) = a_n(E)` for every `n ≥ 1`; `condition2At_normalised_eigen`: such an eigenform is
  normalised, with eigenvalue `a_p(E)` at every `p ∤ N`.
* Non-vacuity: every vendored full eigenform and every newform is an eigenform in the printed
  sense (`isBCDTEigenform_of_eigenform`, `isBCDTEigenform_of_newform`); `0` is not
  (`not_isBCDTEigenform_zero`).
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.BCDTPrint

open Filter CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup HeckeRing.GL2

open scoped MatrixGroups ModularForm

variable {N : ℕ}

/-! ### Möbius action in coordinates -/

/-- **PROVED**, from Mathlib's `UpperHalfPlane.coe_specialLinearGroup_apply`: the action of
`(a b; c d) ∈ SL₂(ℤ)` on the upper half plane is `z ↦ (az + b)/(cz + d)`. -/
theorem coe_smul_eq_printed (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
  rw [coe_specialLinearGroup_apply]
  simp

/-- **PROVED**, by `coe_smul_eq_printed` and `UpperHalfPlane.ofComplex_apply`: the value of a
function at `(az + b)/(cz + d)`, read through Mathlib's chart `ofComplex`, is its value at
`γ • z`. -/
theorem comp_ofComplex_eq_smul (f : ℍ → ℂ) (γ : SL(2, ℤ)) (z : ℍ) :
    (f ∘ ofComplex) (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) = f (γ • z) := by
  rw [← coe_smul_eq_printed, Function.comp_apply, ofComplex_apply]

/-- **PROVED**, by Mathlib's `UpperHalfPlane.denom_ne_zero`: the automorphy factor `cz + d` of
`(a b; c d) ∈ SL₂(ℤ)` does not vanish on the upper half plane. -/
theorem denom_printed_ne_zero (γ : SL(2, ℤ)) (z : ℍ) : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
  rw [← ModularGroup.denom_apply]
  exact denom_ne_zero _ _

/-- **PROVED**, Mathlib's `ModularForm.SL_slash_apply` in coordinates: the weight-`k` slash of
`f` by `(a b; c d) ∈ SL₂(ℤ)` is `z ↦ (cz + d)^{−k} f((az + b)/(cz + d))`. -/
theorem slash_mapGL_apply_printed (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (z : ℍ) :
    (f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ)) z = f (γ • z) * ((γ 1 0 : ℂ) * z + γ 1 1) ^ (-k) := by
  rw [← ModularGroup.denom_apply]
  exact ModularForm.SL_slash_apply f γ z

/-! ### The printed Hecke operator -/

/-- **PROVED**, from the vendored coset formula `coe_heckeTCuspNat_prime`
(`T_p f = ∑_{b < p} f ∣ (1 b; 0 p) + (⟨p⟩ f) ∣ (p 0; 0 1)`), the slash formulas
`slash_upperTriRep_apply`, `TauCeti.slash_natDiagGL_d_one_apply`, and the evaluation of the
diamond operator at a representative, `coe_diamondOpCusp`. For a prime `p ∤ N` and every
`(a b; c d) ∈ SL₂(ℤ)` with `c ≡ 0 mod N` and `d ≡ p mod N`, the vendored `T_p` is the operator
displayed on p. 2 of the author manuscript of Breuil–Conrad–Diamond–Taylor:
`(f|T_p)(z) = p^{−1} ∑_{i=0}^{p−1} f((z + i)/p) + p^{k−1} (cpz + d)^{−k} f((apz + b)/(cpz + d))`.
Values off `ℍ` are read through Mathlib's chart `ofComplex`; every argument here lies in `ℍ`. -/
theorem heckeTCuspNat_apply_eq_printed [NeZero N] {k : ℤ} {p : ℕ} (hp : p.Prime)
    (hpN : ¬p ∣ N) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ))
    (hc : ((γ 1 0 : ℤ) : ZMod N) = 0) (hd : ((γ 1 1 : ℤ) : ZMod N) = p) (z : ℍ) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f z =
      (p : ℂ)⁻¹ * ∑ i ∈ Finset.range p, (⇑f ∘ ofComplex) ((z + i) / p) +
        (p : ℂ) ^ (k - 1) * ((γ 1 0 : ℂ) * p * z + γ 1 1) ^ (-k) *
          (⇑f ∘ ofComplex) (((γ 0 0 : ℂ) * p * z + γ 0 1) / ((γ 1 0 : ℂ) * p * z + γ 1 1)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  rw [coe_heckeTCuspNat_prime k hp f, Pi.add_apply]
  congr 1
  · rw [heckeSlashUpperTri_apply, Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (p : ℂ)⁻¹ * (⇑f ∘ ofComplex) ((z + i) / p)) p]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [slash_upperTriRep_apply, Function.comp_apply, ← coe_upperTriRep_smul, ofComplex_apply]
  · rw [scaleRep_def, TauCeti.slash_natDiagGL_d_one_apply, diamondOpCuspNat_of_coprime k hcop]
    have hγ0 : γ ∈ Gamma0 N := Gamma0_mem.mpr hc
    have hu : (Gamma0Map N).toHomUnits ⟨γ, hγ0⟩ = ZMod.unitOfCoprime p hcop := by
      ext
      rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply, ZMod.coe_unitOfCoprime]
      exact hd
    rw [coe_diamondOpCusp k _ ⟨γ, hγ0⟩ hu f, slash_mapGL_apply_printed]
    have hw : (((TauCeti.scaleGL p • z : ℍ) : ℂ)) = p * z := TauCeti.coe_scaleGL_smul z
    rw [← comp_ofComplex_eq_smul (⇑f) γ (TauCeti.scaleGL p • z), hw]
    simp only [mul_assoc]
    ring

/-! ### The printed cusp forms -/

/-- **DEFINITION**, a cusp form of weight `k` and level `N` as printed in
Breuil–Conrad–Diamond–Taylor, p. 1 of the author manuscript: "a holomorphic function `f` on the
upper half complex plane `𝔥` such that • for all matrices `(a b; c d) ∈ Γ₁(N)` and all `z ∈ 𝔥`,
we have `f((az + b)/(cz + d)) = (cz + d)^k f(z)`; • and `|f(z)|² (Im z)^k` is bounded on `𝔥`."
Holomorphy is complex differentiability on the open set `Im z > 0` of the function read through
Mathlib's chart `ofComplex`. -/
def IsPrintedCuspForm (N : ℕ) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  DifferentiableOn ℂ (f ∘ ofComplex) {z : ℂ | 0 < z.im} ∧
    (∀ γ : SL(2, ℤ), γ ∈ Gamma1 N → ∀ z : ℍ,
      (f ∘ ofComplex) (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) =
        ((γ 1 0 : ℂ) * z + γ 1 1) ^ k * f z) ∧
    ∃ C : ℝ, ∀ z : ℍ, ‖f z‖ ^ 2 * z.im ^ k ≤ C

/-- **PROVED**, from Mathlib's bound `CuspFormClass.exists_bound`
(`|f(z)| ≤ C (Im z)^{−k/2}`) and slash invariance: a Mathlib cusp form on `Γ₁(N)` is a cusp
form in the printed sense. -/
theorem isPrintedCuspForm [NeZero N] {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IsPrintedCuspForm N k f := by
  refine ⟨UpperHalfPlane.mdifferentiable_iff.mp (CuspFormClass.holo f), fun γ hγ z ↦ ?_, ?_⟩
  · rw [comp_ofComplex_eq_smul]
    have h := congrFun (SlashInvariantFormClass.slash_action_eq f (mapGL ℝ γ)
      (Subgroup.mem_map_of_mem _ hγ)) z
    rw [slash_mapGL_apply_printed] at h
    have hj := zpow_ne_zero k (denom_printed_ne_zero γ z)
    rw [← h, zpow_neg, ← mul_assoc, mul_comm (((γ 1 0 : ℂ) * z + γ 1 1) ^ k), mul_assoc,
      mul_inv_cancel₀ hj, mul_one]
  · obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
    refine ⟨C ^ 2, fun z ↦ ?_⟩
    have hy : 0 < z.im := z.im_pos
    have hyk : 0 < z.im ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hy _
    have h2 : ‖f z‖ * z.im ^ ((k : ℝ) / 2) ≤ C := (le_div_iff₀ hyk).mp (hC z)
    have h3 : (z.im ^ ((k : ℝ) / 2)) ^ 2 = z.im ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    calc ‖f z‖ ^ 2 * z.im ^ k = (‖f z‖ * z.im ^ ((k : ℝ) / 2)) ^ 2 := by rw [mul_pow, h3]
      _ ≤ C ^ 2 := pow_le_pow_left₀ (by positivity) h2 2

/-- **PROVED**, by `Im(γz) = Im z / |cz + d|²` (Mathlib, `ModularGroup.im_smul_eq_div_normSq`):
the printed bound `|f(z)|² (Im z)^k ≤ C` passes, with the same constant, to every slash
`f ∣[k] γ` by `γ ∈ SL₂(ℤ)`. -/
theorem printedBound_slash {k : ℤ} {f : ℍ → ℂ} {C : ℝ} (hC : ∀ z : ℍ, ‖f z‖ ^ 2 * z.im ^ k ≤ C)
    (γ : SL(2, ℤ)) (z : ℍ) : ‖(f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ)) z‖ ^ 2 * z.im ^ k ≤ C := by
  refine le_of_eq_of_le ?_ (hC (γ • z))
  have him : (γ • z).im = z.im / ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, ModularGroup.denom_apply]
  set t := ‖(γ 1 0 : ℂ) * z + γ 1 1‖
  rw [slash_mapGL_apply_printed, him, norm_mul, norm_zpow, mul_pow, div_zpow, zpow_neg, inv_pow]
  have e : (t ^ 2) ^ k = (t ^ k) ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast (t ^ k), ← zpow_mul, ← zpow_mul, mul_comm]
  rw [e, div_eq_mul_inv]
  ring

/-- **PROVED**, from the printed bound with `k ≥ 1`: if `|g(z)|² (Im z)^k ≤ C` on `ℍ`, then `g`
tends to zero at `i∞`. -/
theorem isZeroAtImInfty_of_printedBound {k : ℤ} (hk : 0 < k) {g : ℍ → ℂ} {C : ℝ}
    (hC : ∀ z : ℍ, ‖g z‖ ^ 2 * z.im ^ k ≤ C) : IsZeroAtImInfty g := by
  rw [isZeroAtImInfty_iff]
  intro ε hε
  refine ⟨max 1 (C / ε ^ 2 + 1), fun z hz ↦ ?_⟩
  have hy1 : 1 ≤ z.im := le_trans (le_max_left _ _) hz
  have hyA : C / ε ^ 2 + 1 ≤ z.im := le_trans (le_max_right _ _) hz
  have hy : 0 < z.im := z.im_pos
  have hyk : z.im ≤ z.im ^ k := by
    calc z.im = z.im ^ (1 : ℤ) := (zpow_one _).symm
      _ ≤ z.im ^ k := zpow_le_zpow_right₀ hy1 (by omega)
  have h1 : ‖g z‖ ^ 2 * z.im ≤ C :=
    le_trans (mul_le_mul_of_nonneg_left hyk (sq_nonneg _)) (hC z)
  have h2 : ‖g z‖ ^ 2 ≤ ε ^ 2 := by
    have h3 : ‖g z‖ ^ 2 ≤ C / z.im := (le_div_iff₀ hy).mpr h1
    have h4 : C / z.im ≤ ε ^ 2 := by
      rw [div_le_iff₀ hy]
      have h5 : C / ε ^ 2 ≤ z.im := by linarith
      rwa [div_le_iff₀ (by positivity), mul_comm] at h5
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).mp h2

/-- **DEFINITION**, the Mathlib cusp form on `Γ₁(N)` of a cusp form in the printed sense of
positive weight. Slash invariance is the printed transformation law; vanishing at every cusp
follows from the printed bound (`printedBound_slash`, `isZeroAtImInfty_of_printedBound`). -/
def cuspFormOfPrinted {k : ℤ} (hk : 0 < k) {f : ℍ → ℂ} (hf : IsPrintedCuspForm N k f) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := f
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    funext z
    rw [slash_mapGL_apply_printed, ← comp_ofComplex_eq_smul f γ z, hf.2.1 γ hγ z, zpow_neg,
      mul_comm, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero k (denom_printed_ne_zero γ z)),
      one_mul]
  holo' := UpperHalfPlane.mdifferentiable_iff.mpr hf.1
  zero_at_cusps' := by
    intro c hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z (hc.mono (Subgroup.map_le_range _ _))]
    intro γ _
    obtain ⟨C, hC⟩ := hf.2.2
    exact isZeroAtImInfty_of_printedBound hk (printedBound_slash hC γ)

/-- **PROVED**, the converse of `isPrintedCuspForm`, by `cuspFormOfPrinted`: for `k ≥ 1`, a cusp
form in the printed sense is a Mathlib cusp form on `Γ₁(N)`. -/
theorem exists_cuspForm_of_isPrintedCuspForm {k : ℤ} (hk : 0 < k) {f : ℍ → ℂ}
    (hf : IsPrintedCuspForm N k f) : ∃ F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k, ⇑F = f :=
  ⟨cuspFormOfPrinted hk hf, rfl⟩

/-- **PROVED**, `isPrintedCuspForm` and `exists_cuspForm_of_isPrintedCuspForm`: for `k ≥ 1`
the printed space `S_k(N)` is exactly the set of Mathlib cusp forms on `Γ₁(N)`. -/
theorem isPrintedCuspForm_iff [NeZero N] {k : ℤ} (hk : 0 < k) (f : ℍ → ℂ) :
    IsPrintedCuspForm N k f ↔ ∃ F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k, ⇑F = f :=
  ⟨exists_cuspForm_of_isPrintedCuspForm hk, fun ⟨F, hF⟩ ↦ hF ▸ isPrintedCuspForm F⟩

/-! ### Eigenforms and the L-function equality -/

/-- **PROVED**, by the vendored `qExpansion_coeff_one_heckeSlashGamma1CuspFormEnd_diagCosetGamma1`
(`c_1(T_p f) = c_p(f)`): the printed identity `c_p(f) = a_p(f) c_1(f)` for an eigenvector of
`T_p` with eigenvalue `a_p(f)` (Breuil–Conrad–Diamond–Taylor, p. 2). It confirms that the
normalisation of the vendored `T_p` is the printed one. -/
theorem coeff_prime_eq_eigenvalue_mul_coeff_one [NeZero N] {k : ℤ} {p : ℕ} (hp : p.Prime)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} {c : ℂ}
    (hc : heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f = c • f) :
    (qExpansion 1 f).coeff p = c * (qExpansion 1 f).coeff 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h := qExpansion_coeff_one_heckeSlashGamma1CuspFormEnd_diagCosetGamma1 k hp f
  rw [← heckeTCuspNat_def, hc, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    map_smul, smul_eq_mul] at h
  exact h.symm

/-- **PROVED**, by `LSeries_congr`: equal coefficients at every positive index give equal
L-series everywhere. -/
theorem lSeries_eq_cuspLSeries_of_coeff_eq (E : WeierstrassCurve ℚ) {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) (s : ℂ) :
    E.LSeries s = cuspLSeries f s :=
  LSeries_congr (fun {n} hn ↦ (h n (Nat.pos_of_ne_zero hn)).symm) s

/-- **PROVED**, by `coeff_eq_of_eq_cuspLSeries` and `lSeries_eq_cuspLSeries_of_coeff_eq`: for
an eigenform, the half-plane equality `L(E, s) = L(f, s)` of `Condition2At` is equivalent to the
equality `c_n(f) = a_n(E)` of all positive-index coefficients. Neither direction uses a growth
bound for `a_n(E)`. -/
theorem condition2At_iff (E : WeierstrassCurve ℚ) (N : ℕ) [NeZero N] :
    Condition2At E N ↔ ∃ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2, IsBCDTEigenform f ∧
      ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ) := by
  constructor
  · rintro ⟨f, hf, σ, hL⟩
    exact ⟨f, hf, coeff_eq_of_eq_cuspLSeries E hf.1 hL⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, 0, fun s _ ↦ lSeries_eq_cuspLSeries_of_coeff_eq E f h s⟩

/-- **PROVED**, by `coeff_eq_of_eq_cuspLSeries` and `coeff_prime_eq_eigenvalue_mul_coeff_one`:
the eigenform of condition (2) is normalised, `c_1(f) = 1`, and its eigenvalue at every prime
`p ∤ N` is `a_p(E)`. Neither is assumed in `Condition2At`. -/
theorem condition2At_normalised_eigen [NeZero N] {E : WeierstrassCurve ℚ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2} (hf : IsBCDTEigenform f) {σ : ℝ}
    (hL : ∀ s : ℂ, σ < s.re → E.LSeries s = cuspLSeries f s) :
    (qExpansion 1 f).coeff 1 = 1 ∧ ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ N →
      heckeTCuspNat 2 p (_hn := ⟨hp.ne_zero⟩) f = (E.LFunction p : ℂ) • f := by
  have hc := coeff_eq_of_eq_cuspLSeries E hf.1 hL
  have h1 : (qExpansion 1 f).coeff 1 = 1 := by
    rw [hc 1 one_pos, NewformGlueG0.lFunction_one]
    simp
  refine ⟨h1, fun p hp hpN ↦ ?_⟩
  obtain ⟨c, hcf⟩ := hf.2 p hp hpN
  have hcp := coeff_prime_eq_eigenvalue_mul_coeff_one hp hcf
  rw [h1, mul_one, hc p hp.pos] at hcp
  rw [hcf, hcp]

/-! ### Non-vacuity -/

/-- **PROVED**, non-vacuity: a vendored full Hecke eigenform (eigen for every `T_n`, with a
nebentypus) is an eigenform in the printed sense, which asks for less. -/
theorem isBCDTEigenform_of_eigenform [NeZero N] {k : ℤ} (F : Eigenform N k) :
    IsBCDTEigenform F.toCuspForm :=
  ⟨F.ne_zero, fun _ hp _ ↦ ⟨_, F.heckeTCuspNat_eq_eigenvalue_smul hp⟩⟩

/-- **PROVED**, non-vacuity: a vendored newform is an eigenform in the printed sense. -/
theorem isBCDTEigenform_of_newform [NeZero N] {k : ℤ} (F : Newform N k) :
    IsBCDTEigenform F.toCuspForm := by
  simpa using isBCDTEigenform_of_eigenform F.toEigenform

/-- **PROVED**, non-vacuity: the zero form is not an eigenform. -/
theorem not_isBCDTEigenform_zero [NeZero N] {k : ℤ} :
    ¬IsBCDTEigenform (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  fun h ↦ h.1 rfl

end ZInQ.Contrib.RC53Assist.BCDTPrint
