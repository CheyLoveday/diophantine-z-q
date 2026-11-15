import Mathlib

/-!
# qm-glue (a): `ThetaQuotientValue24`

The glue `HDec.LeafQCheck.HM.QMSplit.ThetaQuotientValue24` of qm-split (`scratch/qm-split/Haupt.lean`
l.2287), copied verbatim with what it depends on: the definitions of `HDec.PkgI1` (copied verbatim from
`ZInQKernel/OneProof/H/LPrefix.lean` l.221-363, itself from `scratch/pkg-I1/I1.lean`) and `HDec.LeafQCheck.HM.mu`
(qm-split `Haupt.lean` l.1119).

Results (all compiled here):
* `fixedPoint_eq`: the only `τ` fixed by a `γ` with matrix `ι(μ)` is `τ₂₄ = i(√6 + √3) = i√(9 + 6√2)`.
* `omega_tau24`: the period matrix is explicit, `Ω(τ₂₄) = Ω₂₄ := [[(−4+3√−6)/14, (−1−√−6)/7],
  [(−1−√−6)/7, (−4+3√−6)/7]]` (entries in `ℚ(√−6)`).
* `thetaQuotientValue24_iff`: the glue is equivalent to the closed numeric statement
  `ThetaValueAtOmega24`: `jDen Ω₂₄ ≠ 0 ∧ jNum Ω₂₄ / jDen Ω₂₄ = −16/27` (ten theta constants at one explicit
  matrix).
* `thetaQuotientValue24_of_igusa`: the glue from the published value `IgusaCMValue24` (Lin–Yang's weighted
  Igusa vector along the QM curve, eqs. (2), (14), at the Baba–Granath CM value `j = −16/27`), and the
  converse `igusa_of_thetaQuotientValue24` (the leaf has exactly the content of the glue, no more).
-/

set_option linter.all false

open Complex Matrix

noncomputable section

namespace HDec

namespace PkgI1


/-! ## §1 The quaternion datum (N5 L410-420) -/

/-- `B = (2,-3)`: Mathlib's `QuaternionAlgebra R c₁ c₂ c₃` has `i² = c₁ + c₂ i`, `j² = c₃`. -/
abbrev B := QuaternionAlgebra ℚ 2 0 (-3)

/-- `i`, `j`, `k = ij` in `B`. -/
def qi : B := ⟨0, 1, 0, 0⟩
def qj : B := ⟨0, 0, 1, 0⟩
def qk : B := ⟨0, 0, 0, 1⟩

/-- N5's ordered basis `(1, i, (1+j)/2, (i+ij)/2)` of the maximal order `𝒪`. -/
def oBasis : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1/2, 0, 1/2, 0⟩, ⟨0, 1/2, 0, 1/2⟩]

/-- Membership in `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩`. -/
def InO (x : B) : Prop := ∃ n : Fin 4 → ℤ, x = ∑ k, (n k : ℚ) • oBasis k

/-- `μ = 2j + ij`. -/
def mu : B := ⟨0, 0, 2, 1⟩

/-- `μ⁻¹ = -μ/6`, since `μ² = -6`. -/
def muInv : B := ⟨0, 0, -1/3, -1/6⟩

/-- Reduced trace. -/
def trd (x : B) : ℚ := 2 * x.re

theorem mu_sq : mu * mu = (⟨-6, 0, 0, 0⟩ : B) := by
  ext <;> simp [mu]; norm_num

theorem mu_mul_muInv : mu * muInv = 1 := by
  ext <;> simp [mu, muInv] <;> norm_num

/-- N5's Gram matrix (L413-415). -/
def gram : Matrix (Fin 4) (Fin 4) ℚ := !![0, 0, -1, 1; 0, 0, 1, -2; 1, -1, 0, 0; -1, 2, 0, 0]

/-- **A1 (glue, proved).** `Trd(μ⁻¹ x ȳ)` has N5's Gram matrix in N5's basis. -/
theorem gram_eq (r s : Fin 4) : trd (muInv * oBasis r * star (oBasis s)) = gram r s := by
  fin_cases r <;> fin_cases s <;> simp [trd, muInv, oBasis, gram] <;> norm_num

theorem gram_det : gram.det = 1 := by
  simp [gram, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  rw [show Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 from rfl,
    show Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 from rfl]
  norm_num

/-! ## §2 The real embedding and `Γ*` -/

/-- `ι(i) = [[√2,0],[0,-√2]]`. -/
def Mi : Matrix (Fin 2) (Fin 2) ℝ := !![√2, 0; 0, -√2]
/-- `ι(j) = [[0,-3],[1,0]]`. -/
def Mj : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; 1, 0]

/-- The real embedding `ι : B → M₂(ℝ)` (a ring homomorphism: `qm_embed.py` checks it on the
basis; `Mi² = 2`, `Mj² = -3`, `Mi Mj = -Mj Mi`). -/
def iota (x : B) : Matrix (Fin 2) (Fin 2) ℝ :=
  (x.re : ℝ) • 1 + (x.imI : ℝ) • Mi + (x.imJ : ℝ) • Mj + (x.imK : ℝ) • (Mi * Mj)

/-- `x ∈ B` is invertible and normalizes `𝒪`. -/
def NormalizesO (x : B) : Prop :=
  ∃ y : B, x * y = 1 ∧ y * x = 1 ∧ ∀ z : B, InO z → InO (x * z * y) ∧ InO (y * z * x)

/-- `Γ* = ι(N_B(𝒪)⁺)` acting on `ℍ`; modulo scalars this is the group of the Atkin–Lehner
quotient `X₆/W` (positive reduced norm = positive determinant). -/
def GammaStar : Set (GL (Fin 2) ℝ) :=
  {γ | ∃ x : B, NormalizesO x ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = iota x ∧
    0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det}

/-! ## §3 Siegel upper half-space and theta constants -/

/-- The Siegel upper half-space of degree 2. -/
def SiegelH2 : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {Ω | Ωᵀ = Ω ∧ (Ω.map Complex.im).PosDef}

/-- A half-integral characteristic `m = (a, b)`, `a b ∈ {0,1}²`. -/
abbrev Char2 := (Fin 2 → Fin 2) × (Fin 2 → Fin 2)

/-- Theta constant `θ_m(Ω) = Σ_{n ∈ ℤ²} exp(πi (n+a/2)ᵀΩ(n+a/2) + πi (n+a/2)ᵀ b)`. -/
def thetaConst (m : Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑' n : Fin 2 → ℤ,
    let v : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2
    Complex.exp (Real.pi * I * (v ⬝ᵥ (Ω *ᵥ v)) + Real.pi * I * (v ⬝ᵥ fun k => ((m.2 k : ℕ) : ℂ)))

/-- The ten even characteristics (`aᵀb ≡ 0 mod 2`). -/
def evenChars : Finset Char2 :=
  Finset.univ.filter fun m => ((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ)) % 2 = 0

theorem card_evenChars : evenChars.card = 10 := by decide

/-- `Σ_{m even} θ_m⁸` (`= 4ψ₄`). -/
def thetaSum8 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ∑ m ∈ evenChars, thetaConst m Ω ^ 8

/-- `∏_{m even} θ_m²` (`= -2¹⁴χ₁₀`). -/
def thetaProd2 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ∏ m ∈ evenChars, thetaConst m Ω ^ 2

/-- Numerator of F1: `3779136·(∏θ_m)⁴`. -/
def jNum (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 3779136 * thetaProd2 Ω ^ 2

/-- Denominator of F1: `(Σθ_m⁸)⁵`. -/
def jDen (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := thetaSum8 Ω ^ 5

/-- The action of `Sp₄` on degree-2 matrices: `(AΩ+B)(CΩ+D)⁻¹`. -/
def spAct (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let Mc := M.map (Int.cast : ℤ → ℂ)
  (Mc.toBlocks₁₁ * Ω + Mc.toBlocks₁₂) * (Mc.toBlocks₂₁ * Ω + Mc.toBlocks₂₂)⁻¹

/-- The automorphy factor `det(CΩ+D)`. -/
def spFactor (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    ℂ :=
  let Mc := M.map (Int.cast : ℤ → ℂ)
  (Mc.toBlocks₂₁ * Ω + Mc.toBlocks₂₂).det

/-! ## §4 The modular embedding of N5's QM datum (`qm_embed.py`)

For `τ ∈ ℍ` put `v_τ = (τ, 1)ᵀ` and `Λ_τ = ι(𝒪)v_τ ⊂ ℂ²`, with Riemann form
`E(ι(x)v_τ, ι(y)v_τ) = Trd(μ⁻¹xȳ)`. In N5's basis the Gram matrix is `[[0,P],[-Pᵀ,0]]` with
`P = [[-1,1],[1,-2]]`, `P⁻¹ = [[-2,-1],[-1,-1]]`. So `e = (ι(1)v, ι(i)v)` and
`f' = (ι((1+j)/2)v, ι((i+ij)/2)v)·P⁻¹` is a symplectic basis, and `Ω(τ) = F'(τ)⁻¹E(τ)` is a
period matrix of the principally polarized QM surface `A_τ = ℂ²/Λ_τ` (symmetric with positive
definite imaginary part: VERIFIED numerically; the other normalization `E⁻¹F'` belongs to `-E`). -/

/-- `ι(x)·(τ, 1)ᵀ`. -/
def latVec (x : B) (τ : ℂ) : Fin 2 → ℂ := (iota x).map (fun r : ℝ => (r : ℂ)) *ᵥ ![τ, 1]

/-- `E(τ)`: columns `ι(1)v_τ`, `ι(i)v_τ`. -/
def Emat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 0) τ, latVec (oBasis 1) τ] c r

/-- `F₀(τ)`: columns `ι((1+j)/2)v_τ`, `ι((i+ij)/2)v_τ`. -/
def F0mat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 2) τ, latVec (oBasis 3) τ] c r

/-- `P⁻¹` for `P = [[-1,1],[1,-2]]`. -/
def Pinv : Matrix (Fin 2) (Fin 2) ℂ := !![-2, -1; -1, -1]

/-- The period matrix `Ω(τ) = (F₀(τ)P⁻¹)⁻¹E(τ)` of the QM surface at `τ`. -/
def Omega (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (F0mat τ * Pinv)⁻¹ * Emat τ

end PkgI1

namespace LeafQCheck.HM

/-- `μ = 2j + ij` (qm-split `Haupt.lean` l.1119, verbatim). -/
def mu : PkgI1.B := ⟨0, 0, 2, 1⟩

namespace QMSplit

open PkgI1

/-- **GLUE (the value of the theta quotient at the CM point of discriminant `−24`).** At the fixed point
`τ = i√(9 + 6√2)` of `ι(μ)`, `μ = 2j + ij`: `jDen(Ω(τ)) ≠ 0` and `jNum(Ω(τ))/jDen(Ω(τ)) = −16/27`.
Numerically VERIFIED by leaf-review-a (`py/hauptmodul_check.py`: `−0.592592592592593`). Sources for a proof:
Baba–Granath, Canad. J. Math. 60 (2008) (Igusa invariants of the QM family as functions of the Hauptmodul of
`X₆/W`, and its CM values) with Igusa's theta expressions of the Igusa invariants (Amer. J. Math. 89 (1967));
locators UNVERIFIED. -/
def ThetaQuotientValue24 : Prop :=
  ∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu → ∀ τ : UpperHalfPlane, γ • τ = τ →
    PkgI1.jDen (PkgI1.Omega τ) ≠ 0 ∧
      PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = -16 / 27

end QMSplit
end LeafQCheck.HM
end HDec

/-! ## Proofs -/

namespace HDec.LeafQCheck.HM.QMSplit.Value24

open PkgI1 UpperHalfPlane

theorem iota_mu : PkgI1.iota mu = !![0, -6 - 3 * √2; 2 - √2, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [PkgI1.iota, mu, PkgI1.Mi, PkgI1.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sqrt2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
theorem sqrt3_sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
theorem sqrt6_eq : (√6 : ℝ) = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
theorem sqrt2_lt : (√2 : ℝ) < 2 := by
  rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- `s₂₄ = √6 + √3`, so `τ₂₄ = i s₂₄` and `s₂₄² = 9 + 6√2`. -/
def s24 : ℝ := √6 + √3

theorem s24_pos : 0 < s24 := by unfold s24; positivity

theorem s24_sq : s24 ^ 2 = 9 + 6 * √2 := by
  unfold s24; rw [sqrt6_eq]
  have h2 := sqrt2_sq; have h3 := sqrt3_sq
  linear_combination (√3 ^ 2) * h2 + (3 + 2 * √2) * h3

/-- From qm-split `Haupt.lean` l.652 (`fixed_data`, verbatim): the fixed-point equations. -/
theorem fixed_data {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) :
    (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
        2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
        -(γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (P.re ^ 2 + P.im ^ 2) := by
  have hd' : 0 < γ.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  have h := congrArg (fun w : UpperHalfPlane => (w : ℂ)) hP
  rw [UpperHalfPlane.coe_smul_of_det_pos hd', div_eq_iff (denom_ne_zero γ P)] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [UpperHalfPlane.num, UpperHalfPlane.denom] at hre him
  have hq := P.im_pos
  have ha : ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - 2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re -
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1) * P.im = 0 := by linear_combination him
  have ha' := (mul_eq_zero.1 ha).resolve_right hq.ne'
  refine ⟨by linarith, ?_⟩
  have : (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    linarith
  rw [this] at hre
  linear_combination hre

/-- **The CM point.** The only point fixed by a `γ` with matrix `ι(μ)` is `τ₂₄ = i(√6 + √3)`. -/
theorem fixedPoint_eq (γ : GL (Fin 2) ℝ) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu)
    (τ : UpperHalfPlane) (h : γ • τ = τ) : (τ : ℂ) = Complex.I * (s24 : ℂ) := by
  have h2 := sqrt2_lt
  have hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [hγ, iota_mu, Matrix.det_fin_two_of]; nlinarith [sqrt2_sq]
  obtain ⟨e1, e2⟩ := fixed_data hd h
  rw [hγ, iota_mu] at e1 e2
  simp at e1 e2
  have hc : (2 - √2 : ℝ) ≠ 0 := by linarith
  have hre : τ.re = 0 := e1.resolve_left hc
  rw [hre] at e2
  have him2 : τ.im ^ 2 = s24 ^ 2 := by
    rw [s24_sq]
    have : (2 - √2) * (τ.im ^ 2 - (9 + 6 * √2)) = 0 := by
      linear_combination e2 + 6 * sqrt2_sq
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc
    · linarith
  have him : τ.im = s24 := by
    have := τ.im_pos; have := s24_pos
    nlinarith [sq_nonneg (τ.im - s24), sq_nonneg (τ.im + s24)]
  apply Complex.ext <;> simp [hre, him]

/-- The explicit period matrix at `τ₂₄` (entries in `ℚ(√−6)`). -/
def Om24 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-4 + 3 * Complex.I * ((√6 : ℝ) : ℂ)) / 14, (-1 - Complex.I * ((√6 : ℝ) : ℂ)) / 7;
     (-1 - Complex.I * ((√6 : ℝ) : ℂ)) / 7, (-4 + 3 * Complex.I * ((√6 : ℝ) : ℂ)) / 7]

theorem Emat_eq (τ : ℂ) : PkgI1.Emat τ = !![τ, (√2 : ℂ) * τ; 1, -(√2 : ℂ)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [PkgI1.Emat, PkgI1.latVec, PkgI1.iota, PkgI1.oBasis, PkgI1.Mi, PkgI1.Mj, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.mul_apply]

theorem F0mat_eq (τ : ℂ) : PkgI1.F0mat τ =
    !![(τ - 3) / 2, (√2 : ℂ) * (τ - 3) / 2; (τ + 1) / 2, -(√2 : ℂ) * (τ + 1) / 2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [PkgI1.F0mat, PkgI1.latVec, PkgI1.iota, PkgI1.oBasis, PkgI1.Mi, PkgI1.Mj, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.mul_apply] <;> ring

theorem c2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast sqrt2_sq
theorem c3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast sqrt3_sq

/-- **The period matrix at `τ₂₄`**: `Ω(τ₂₄) = Ω₂₄`. -/
theorem omega_tau24 : PkgI1.Omega (Complex.I * (s24 : ℂ)) = Om24 := by
  set τ : ℂ := Complex.I * (s24 : ℂ) with hτ
  have ha := c2; have hb := c3
  have ha3 : ((√2 : ℝ) : ℂ) ^ 3 = 2 * ((√2 : ℝ) : ℂ) := by rw [pow_succ, ha]
  have hb3 : ((√3 : ℝ) : ℂ) ^ 3 = 3 * ((√3 : ℝ) : ℂ) := by rw [pow_succ, hb]
  have hA : (PkgI1.F0mat τ * PkgI1.Pinv) * Om24 = PkgI1.Emat τ := by
    rw [F0mat_eq, Emat_eq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Om24, PkgI1.Pinv, Matrix.mul_apply, Fin.sum_univ_two, hτ, s24, sqrt6_eq] <;>
      ring_nf <;> simp only [ha, hb, ha3, hb3, Complex.I_sq] <;> ring_nf
  have him : τ.im ≠ 0 := by simp [hτ]; exact s24_pos.ne'
  have h1 : τ - 3 ≠ 0 := fun h => him (by simpa using congrArg Complex.im h)
  have h2 : τ + 1 ≠ 0 := fun h => him (by simpa using congrArg Complex.im h)
  have hdet : IsUnit (PkgI1.F0mat τ * PkgI1.Pinv).det := by
    rw [Matrix.det_mul, F0mat_eq, Matrix.det_fin_two_of]
    have hP : PkgI1.Pinv.det = 1 := by simp [PkgI1.Pinv, Matrix.det_fin_two_of]; norm_num
    rw [hP, mul_one, isUnit_iff_ne_zero]
    have : (τ - 3) / 2 * (-((√2 : ℝ) : ℂ) * (τ + 1) / 2) - ((√2 : ℝ) : ℂ) * (τ - 3) / 2 * ((τ + 1) / 2)
        = -(((√2 : ℝ) : ℂ) * (τ - 3) * (τ + 1)) / 2 := by ring
    rw [this]
    have : ((√2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
    simp [h1, h2, this]
  unfold PkgI1.Omega
  rw [← hA, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

/-! ## The glue as a closed numeric statement -/

/-- **The glue at the explicit period matrix**: the ten even theta constants at `Ω₂₄` satisfy
`(Σθ⁸)⁵ ≠ 0` and `3779136(∏θ²)²/(Σθ⁸)⁵ = −16/27`. -/
def ThetaValueAtOmega24 : Prop :=
  PkgI1.jDen Om24 ≠ 0 ∧ PkgI1.jNum Om24 / PkgI1.jDen Om24 = -16 / 27

theorem det_iota_mu : (PkgI1.iota mu).det = 6 := by
  rw [iota_mu, Matrix.det_fin_two_of]; linear_combination (-3 : ℝ) * sqrt2_sq

/-- `γ_μ ∈ GL₂(ℝ)` with matrix `ι(μ)`. -/
def gammaMu : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (PkgI1.iota mu) (by rw [det_iota_mu]; norm_num)

/-- `τ₂₄ ∈ ℍ`. -/
def tau24 : UpperHalfPlane := ⟨Complex.I * (s24 : ℂ), by simpa using s24_pos⟩

theorem gammaMu_fix : gammaMu • tau24 = tau24 := by
  have hd : 0 < gammaMu.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show 0 < (PkgI1.iota mu).det
    rw [det_iota_mu]; norm_num
  have hc : ((2 : ℂ) - ((√2 : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have : (√2 : ℝ) = 2 := by exact_mod_cast (sub_eq_zero.1 h).symm
    linarith [sqrt2_lt]
  have hs : ((s24 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast s24_pos.ne'
  have hs2 : ((s24 : ℝ) : ℂ) ^ 2 = 9 + 6 * ((√2 : ℝ) : ℂ) := by exact_mod_cast s24_sq
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hd, div_eq_iff (UpperHalfPlane.denom_ne_zero _ _)]
  have hval : (gammaMu : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu := rfl
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hval, iota_mu, tau24, UpperHalfPlane.coe_mk]
  simp
  linear_combination (-(2 - ((√2 : ℝ) : ℂ)) * ((s24 : ℝ) : ℂ) ^ 2) * Complex.I_sq +
    (2 - ((√2 : ℝ) : ℂ)) * hs2 + (-6 : ℂ) * c2

/-- **(a), exact part.** The glue `ThetaQuotientValue24` is equivalent to the closed statement
`ThetaValueAtOmega24` about the theta constants at the explicit matrix `Ω₂₄`. -/
theorem thetaQuotientValue24_iff : ThetaQuotientValue24 ↔ ThetaValueAtOmega24 := by
  constructor
  · intro h
    have := h gammaMu rfl tau24 gammaMu_fix
    have e : ((tau24 : UpperHalfPlane) : ℂ) = Complex.I * (s24 : ℂ) := rfl
    rw [e, omega_tau24] at this
    exact this
  · intro h γ hγ τ hτ
    rw [fixedPoint_eq γ hγ τ hτ, omega_tau24]
    exact h

/-! ## Reduction to the published value -/

/-- Verbatim from `ZInQKernel/OneProof/H/LPrefix.lean` §7 (`HDec.PkgI1.f1_algebra`). -/
theorem f1_algebra {K : Type*} [Field K] [CharZero K] (j lam J2 J4 J10 Sig Pi : K)
    (hJ2 : J2 = 12 * (j + 1) * lam) (hJ4 : J4 = 6 * (j ^ 2 + j + 1) * lam ^ 2)
    (hJ10 : J10 = j ^ 3 * lam ^ 5)
    (hpsi : J2 ^ 2 - 24 * J4 = Sig / 4) (hchi : -J10 / 4 = -Pi / 2 ^ 14) :
    j * Sig ^ 5 = 3779136 * Pi ^ 2 := by
  have hS : Sig = 576 * j * lam ^ 2 := by
    rw [hJ2, hJ4] at hpsi; linear_combination (-4 : K) * hpsi
  have hP : Pi = 4096 * j ^ 3 * lam ^ 5 := by
    rw [hJ10] at hchi; linear_combination (16384 : K) * hchi
  rw [hS, hP]; ring

/-- **LEAF (published value: the Igusa invariants at the CM point of discriminant `−24`).** At the fixed
point `τ` of `ι(μ)` (the CM point of discriminant `−24` of `X₆/W` in the modular embedding of `PkgI1` §4,
whose Riemann form is Lin–Yang's convention, eq. (3) and Lemma 3), Igusa's invariants of the principally
polarized surface with period matrix `Ω(τ)` are, in a weighted representative, Lin–Yang's vector
`J₂ = 12(j+1)λ`, `J₄ = 6(j²+j+1)λ²`, `J₁₀ = j³λ⁵` at `j = −16/27`, with Igusa's
`ψ₄ = J₂² − 24J₄`, `χ₁₀ = −J₁₀/4` and LNY's theta conventions `ψ₄ = Σθ_m⁸/4`, `χ₁₀ = −∏θ_m²/2¹⁴`.

Published form: Lin–Yang, *Quaternionic loci in Siegel's modular threefold* (Math. Z., 2020; arXiv v1),
eqs. (2) and (14), pp. 3 and 17 (the Igusa vector of the QM curve of discriminant 6 as a function of the
Hauptmodul `j` of `X₆/W`), with the CM value `j = −16/27` at discriminant `−24` (Baba–Granath, Canad. J. Math.
60 (2008), Thm 2.1 and the CM table; Elkies, ANTS-III (1998), the CM points of `X*(6)`); Lauter–Naehrig–Yang
(2015) §2.2, p. 4 for the theta conventions; Igusa, Amer. J. Math. 89 (1967). This is the citation of the
manuscript, l.908-923 (`diophantine_zq.tex`). Locators UNVERIFIED (no network); the manuscript cites
exactly these equations and pages.

Content: by `igusa_of_thetaQuotientValue24` this leaf is *equivalent* to the glue `ThetaQuotientValue24`
(it restates it in Igusa's normalization; it is not stronger). The published content that it uses is one
number: the value of Lin–Yang's normalized Hauptmodul at the discriminant `−24` point. -/
def IgusaCMValue24 : Prop :=
  ∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu → ∀ τ : UpperHalfPlane, γ • τ = τ →
    ∃ lam J2 J4 J10 : ℂ, lam ≠ 0 ∧
      J2 = 12 * ((-16 / 27 : ℂ) + 1) * lam ∧
      J4 = 6 * ((-16 / 27 : ℂ) ^ 2 + (-16 / 27 : ℂ) + 1) * lam ^ 2 ∧
      J10 = (-16 / 27 : ℂ) ^ 3 * lam ^ 5 ∧
      J2 ^ 2 - 24 * J4 = PkgI1.thetaSum8 (PkgI1.Omega τ) / 4 ∧
      -J10 / 4 = -PkgI1.thetaProd2 (PkgI1.Omega τ) / 2 ^ 14

/-- **(a): the glue from the published value.** -/
theorem thetaQuotientValue24_of_igusa (h : IgusaCMValue24) : ThetaQuotientValue24 := by
  intro γ hγ τ hτ
  obtain ⟨lam, J2, J4, J10, hlam, h2, h4, h10, hpsi, hchi⟩ := h γ hγ τ hτ
  have key := f1_algebra (-16 / 27 : ℂ) lam J2 J4 J10 _ _ h2 h4 h10 hpsi hchi
  have hS : PkgI1.thetaSum8 (PkgI1.Omega τ) = 576 * (-16 / 27) * lam ^ 2 := by
    rw [h2, h4] at hpsi; linear_combination (-4 : ℂ) * hpsi
  have hS0 : PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 := by
    rw [hS]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hlam)
  have hD : PkgI1.jDen (PkgI1.Omega τ) ≠ 0 := pow_ne_zero _ hS0
  refine ⟨hD, ?_⟩
  rw [div_eq_iff hD]
  simp only [PkgI1.jNum, PkgI1.jDen]
  linear_combination -key

/-- **The converse: the leaf is not stronger than the glue.** -/
theorem igusa_of_thetaQuotientValue24 (h : ThetaQuotientValue24) : IgusaCMValue24 := by
  intro γ hγ τ hτ
  obtain ⟨hD, hv⟩ := h γ hγ τ hτ
  set Sig := PkgI1.thetaSum8 (PkgI1.Omega τ)
  set Pi := PkgI1.thetaProd2 (PkgI1.Omega τ)
  have hS0 : Sig ≠ 0 := fun h0 => hD (by simp [PkgI1.jDen, Sig, h0])
  have key : 3779136 * Pi ^ 2 = (-16 / 27) * Sig ^ 5 := by
    rw [div_eq_iff hD] at hv; simpa [PkgI1.jNum, PkgI1.jDen] using hv
  obtain ⟨l0, hl0⟩ := IsAlgClosed.exists_pow_nat_eq (Sig / (576 * (-16 / 27))) (n := 2) (by norm_num)
  have hl0' : Sig = 576 * (-16 / 27) * l0 ^ 2 := by rw [hl0]; field_simp
  have hl00 : l0 ≠ 0 := by rintro rfl; simp at hl0'; exact hS0 hl0'
  -- `Pi² = (4096 j³ l0⁵)²`, so `Pi = ± 4096 j³ l0⁵`
  have hsq : (Pi - 4096 * (-16 / 27) ^ 3 * l0 ^ 5) * (Pi + 4096 * (-16 / 27) ^ 3 * l0 ^ 5) = 0 := by
    rw [hl0'] at key; linear_combination key / 3779136
  have hsign : ∃ lam : ℂ, lam ≠ 0 ∧ Sig = 576 * (-16 / 27) * lam ^ 2 ∧
      Pi = 4096 * (-16 / 27) ^ 3 * lam ^ 5 := by
    rcases mul_eq_zero.1 hsq with e | e
    · exact ⟨l0, hl00, hl0', by linear_combination e⟩
    · exact ⟨-l0, neg_ne_zero.2 hl00, by rw [hl0']; ring, by linear_combination e⟩
  obtain ⟨lam, hlam, hS, hP⟩ := hsign
  refine ⟨lam, _, _, _, hlam, rfl, rfl, rfl, ?_, ?_⟩
  · rw [hS]; ring
  · rw [hP]; ring

end HDec.LeafQCheck.HM.QMSplit.Value24

/-! # cm24-value: the copy above is `scratch/qm-glue/ThetaValue24.lean` l.1-447, verbatim.
Below: the exact evaluation (namespace `CM24`). -/

open scoped Real

namespace CM24

/-- The general genus-2 theta term with real characteristics `c = (c0,c1)`, `d = (d0,d1)` at the symmetric
matrix `[[α, β], [β, γ]]`: `exp(πi vᵀΩv + 2πi v·d)`, `v = n + c`. -/
def term2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n : ℤ × ℤ) : ℂ :=
  cexp (π * I * (α * (((n.1 : ℝ) + c0 : ℝ) : ℂ) ^ 2 + 2 * β * (((n.1 : ℝ) + c0 : ℝ) : ℂ) * (((n.2 : ℝ) + c1 : ℝ) : ℂ)
      + γ * (((n.2 : ℝ) + c1 : ℝ) : ℂ) ^ 2)
    + 2 * π * I * ((((n.1 : ℝ) + c0 : ℝ) : ℂ) * d0 + (((n.2 : ℝ) + c1 : ℝ) : ℂ) * d1))

def Th2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) : ℂ := ∑' n : ℤ × ℤ, term2 α β γ c0 c1 d0 d1 n

theorem re_exponent (α β γ : ℂ) (x y d0 d1 : ℝ) :
    (π * I * (α * (x : ℂ) ^ 2 + 2 * β * x * y + γ * (y : ℂ) ^ 2) + 2 * π * I * ((x : ℂ) * d0 + (y : ℂ) * d1)).re
      = -π * (α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2) := by
  simp [Complex.mul_re, Complex.mul_im, pow_two]

/-- 1D Gaussian summability. -/
theorem summable_gauss {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    Summable (fun n : ℤ => Real.exp (-π * δ * ((n : ℝ) + c) ^ 2)) := by
  have h := ((summable_jacobiTheta₂_term_iff ((c * δ : ℝ) * I) ((δ : ℂ) * I)).2
    (by simpa using hδ)).norm.mul_left (Real.exp (-π * δ * c ^ 2))
  refine h.congr fun n => ?_
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  simp
  ring

theorem norm_term2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n : ℤ × ℤ) :
    ‖term2 α β γ c0 c1 d0 d1 n‖ = Real.exp (-π * (α.im * ((n.1 : ℝ) + c0) ^ 2
      + 2 * β.im * ((n.1 : ℝ) + c0) * ((n.2 : ℝ) + c1) + γ.im * ((n.2 : ℝ) + c1) ^ 2)) := by
  rw [term2, Complex.norm_exp, re_exponent]

theorem summable_norm_term2 {α β γ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ x y : ℝ, δ * (x ^ 2 + y ^ 2) ≤ α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2)
    (c0 c1 d0 d1 : ℝ) : Summable (fun n => ‖term2 α β γ c0 c1 d0 d1 n‖) := by
  have h := (summable_gauss hδ c0).mul_of_nonneg (summable_gauss hδ c1)
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) h
  rw [norm_term2, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have := hQ ((n.1 : ℝ) + c0) ((n.2 : ℝ) + c1)
  nlinarith [Real.pi_pos]

theorem summable_term2 {α β γ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ x y : ℝ, δ * (x ^ 2 + y ^ 2) ≤ α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2)
    (c0 c1 d0 d1 : ℝ) : Summable (term2 α β γ c0 c1 d0 d1) :=
  (summable_norm_term2 hδ hQ c0 c1 d0 d1).of_norm


/-- Sum over `ℤ × ℤ` as an iterated sum, inner over the first coordinate. -/
theorem tsum_swap_iter {f : ℤ × ℤ → ℂ} (hf : Summable f) :
    ∑' n, f n = ∑' n1 : ℤ, ∑' n0 : ℤ, f (n0, n1) := by
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq]
  exact ((Equiv.prodComm ℤ ℤ).summable_iff.2 hf).tsum_prod

theorem term2_eq_jt (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n0 n1 : ℤ) :
    term2 α β γ c0 c1 d0 d1 (n0, n1) =
      cexp (π * I * (α * (c0 : ℂ) ^ 2 + 2 * β * c0 * ((n1 : ℂ) + c1) + γ * ((n1 : ℂ) + c1) ^ 2)
        + 2 * π * I * ((c0 : ℂ) * d0 + ((n1 : ℂ) + c1) * d1)) *
      jacobiTheta₂_term n0 (c0 * α + β * ((n1 : ℂ) + c1) + d0) α := by
  rw [term2, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem jt_dual (α β γ : ℂ) (hα : α ≠ 0) (c0 c1 d0 d1 : ℝ) (m n1 : ℤ) :
    cexp (π * I * (α * (c0 : ℂ) ^ 2 + 2 * β * c0 * ((n1 : ℂ) + c1) + γ * ((n1 : ℂ) + c1) ^ 2)
        + 2 * π * I * ((c0 : ℂ) * d0 + ((n1 : ℂ) + c1) * d1)) *
      (cexp (-π * I * (c0 * α + β * ((n1 : ℂ) + c1) + d0) ^ 2 / α) *
        jacobiTheta₂_term m ((c0 * α + β * ((n1 : ℂ) + c1) + d0) / α) (-1 / α)) =
      cexp (2 * π * I * c0 * d0) * term2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1 (m, n1) := by
  rw [term2, jacobiTheta₂_term, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- **Partial inversion in the first coordinate** (two applications of Mathlib's
`jacobiTheta₂_functional_equation` give the full inversion `Ω ↦ −Ω⁻¹`). -/
theorem pi0 {α β γ : ℂ} (hα : 0 < α.im) (c0 c1 d0 d1 : ℝ)
    (hs : Summable (term2 α β γ c0 c1 d0 d1))
    (hs' : Summable (term2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1)) :
    Th2 α β γ c0 c1 d0 d1 = 1 / (-I * α) ^ (1 / 2 : ℂ) * cexp (2 * π * I * c0 * d0) *
      Th2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1 := by
  have hα0 : α ≠ 0 := fun h => by simp [h] at hα
  rw [Th2, Th2, tsum_swap_iter hs, tsum_swap_iter hs', ← tsum_mul_left]
  congr 1; funext n1
  conv_lhs => enter [1]; ext n0; rw [term2_eq_jt]
  rw [tsum_mul_left]
  change _ * jacobiTheta₂ _ _ = _
  rw [jacobiTheta₂_functional_equation, jacobiTheta₂, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_mul_left]
  congr 1; funext m
  conv_rhs => rw [mul_assoc, ← jt_dual α β γ hα0 c0 c1 d0 d1 m n1]
  ring


/-! ## Symmetries -/

theorem th2_swap (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) : Th2 α β γ c0 c1 d0 d1 = Th2 γ β α c1 c0 d1 d0 := by
  rw [Th2, Th2, ← (Equiv.prodComm ℤ ℤ).tsum_eq]
  congr 1; funext n
  simp only [term2, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  congr 1; ring

theorem th2_shift_c (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (k0 k1 : ℤ) :
    Th2 α β γ (c0 + k0) (c1 + k1) d0 d1 = Th2 α β γ c0 c1 d0 d1 := by
  rw [Th2, Th2]
  conv_rhs => rw [← (Equiv.addRight ((k0, k1) : ℤ × ℤ)).tsum_eq]
  congr 1; funext n
  simp only [term2, Equiv.coe_addRight, Prod.fst_add, Prod.snd_add]
  congr 1; push_cast; ring

theorem th2_shift_d (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (k0 k1 : ℤ) :
    Th2 α β γ c0 c1 (d0 + k0) (d1 + k1) =
      cexp (2 * π * I * (c0 * k0 + c1 * k1)) * Th2 α β γ c0 c1 d0 d1 := by
  rw [Th2, Th2, ← tsum_mul_left]
  congr 1; funext n
  have h : cexp (((-(n.1 * k0 + n.2 * k1) : ℤ) : ℂ) * (2 * π * I)) = 1 := exp_int_mul_two_pi_mul_I _
  rw [term2, term2, ← mul_one (cexp (_ + _)), ← h, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-! ## Duplication -/

/-- `(σ, p, q) ↦ (p + q + σ, p − q)`, a bijection `Fin 2 × ℤ × ℤ ≃ ℤ × ℤ`. -/
def dupE1 : Fin 2 × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun w := (w.2.1 + w.2.2 + (w.1 : ℕ), w.2.1 - w.2.2)
  invFun mn := (if (mn.1 - mn.2) % 2 = 0 then 0 else 1,
    (mn.2 + (mn.1 - mn.2 - (if (mn.1 - mn.2) % 2 = 0 then 0 else 1)) / 2,
     (mn.1 - mn.2 - (if (mn.1 - mn.2) % 2 = 0 then 0 else 1)) / 2))
  left_inv w := by
    obtain ⟨σ, p, q⟩ := w
    fin_cases σ <;> simp <;> omega
  right_inv mn := by
    obtain ⟨m, n⟩ := mn
    by_cases h : (m - n) % 2 = 0 <;> simp [h] <;> omega

/-- The 2D version: `((σ₀,σ₁), (p, q)) ↦ (p + q + σ, p − q)` on `ℤ² × ℤ²`. -/
def dupE2 : (Fin 2 × Fin 2) × ((ℤ × ℤ) × (ℤ × ℤ)) ≃ (ℤ × ℤ) × (ℤ × ℤ) where
  toFun w := ((w.2.1.1 + w.2.2.1 + (w.1.1 : ℕ), w.2.1.2 + w.2.2.2 + (w.1.2 : ℕ)),
    (w.2.1.1 - w.2.2.1, w.2.1.2 - w.2.2.2))
  invFun mn :=
    let s0 : ℤ := if (mn.1.1 - mn.2.1) % 2 = 0 then 0 else 1
    let s1 : ℤ := if (mn.1.2 - mn.2.2) % 2 = 0 then 0 else 1
    ((if (mn.1.1 - mn.2.1) % 2 = 0 then 0 else 1, if (mn.1.2 - mn.2.2) % 2 = 0 then 0 else 1),
      ((mn.2.1 + (mn.1.1 - mn.2.1 - s0) / 2, mn.2.2 + (mn.1.2 - mn.2.2 - s1) / 2),
       ((mn.1.1 - mn.2.1 - s0) / 2, (mn.1.2 - mn.2.2 - s1) / 2)))
  left_inv w := by
    obtain ⟨⟨σ0, σ1⟩, ⟨p0, p1⟩, ⟨q0, q1⟩⟩ := w
    fin_cases σ0 <;> fin_cases σ1 <;> simp <;> omega
  right_inv mn := by
    obtain ⟨⟨m0, m1⟩, ⟨n0, n1⟩⟩ := mn
    by_cases h0 : (m0 - n0) % 2 = 0 <;> by_cases h1 : (m1 - n1) % 2 = 0 <;> simp [h0, h1] <;> omega

theorem dupE2_apply (σ0 σ1 : Fin 2) (p0 p1 q0 q1 : ℤ) :
    dupE2 ((σ0, σ1), ((p0, p1), (q0, q1))) =
      ((p0 + q0 + (σ0 : ℕ), p1 + q1 + (σ1 : ℕ)), (p0 - q0, p1 - q1)) := rfl

theorem dup2 {α β γ : ℂ} (c0 c1 d0 d1 : ℝ)
    (hs : Summable (fun n => ‖term2 α β γ c0 c1 d0 d1 n‖))
    (hs2 : ∀ c0' c1' d0' d1' : ℝ, Summable (fun n => ‖term2 (2 * α) (2 * β) (2 * γ) c0' c1' d0' d1' n‖)) :
    Th2 α β γ c0 c1 d0 d1 ^ 2 = ∑ σ : Fin 2 × Fin 2,
      Th2 (2 * α) (2 * β) (2 * γ) (((σ.1 : ℕ) : ℝ) / 2 + c0) (((σ.2 : ℕ) : ℝ) / 2 + c1) (2 * d0) (2 * d1) *
      Th2 (2 * α) (2 * β) (2 * γ) (((σ.1 : ℕ) : ℝ) / 2) (((σ.2 : ℕ) : ℝ) / 2) 0 0 := by
  have hprod := summable_mul_of_summable_norm hs hs
  have h2 : Summable (fun c => term2 α β γ c0 c1 d0 d1 (dupE2 c).1 *
      term2 α β γ c0 c1 d0 d1 (dupE2 c).2) := dupE2.summable_iff.2 hprod
  rw [sq, Th2, tsum_mul_tsum_of_summable_norm hs hs, ← dupE2.tsum_eq, h2.tsum_prod, tsum_fintype]
  congr 1; funext σ
  rw [Th2, Th2, tsum_mul_tsum_of_summable_norm (hs2 _ _ _ _) (hs2 _ _ _ _)]
  congr 1; funext w
  obtain ⟨σ0, σ1⟩ := σ
  obtain ⟨⟨p0, p1⟩, ⟨q0, q1⟩⟩ := w
  rw [dupE2_apply]
  simp only [term2, ← Complex.exp_add]
  congr 1; push_cast; ring


/-! ## Genus one -/

/-- Genus-1 theta term with real characteristic: `exp(πiτ(n+c)² + 2πi(n+c)d)`. -/
def term1 (τ : ℂ) (c d : ℝ) (n : ℤ) : ℂ :=
  cexp (π * I * τ * (((n : ℝ) + c : ℝ) : ℂ) ^ 2 + 2 * π * I * (((n : ℝ) + c : ℝ) : ℂ) * d)

def th1 (τ : ℂ) (c d : ℝ) : ℂ := ∑' n : ℤ, term1 τ c d n

theorem term1_eq (τ : ℂ) (c d : ℝ) (n : ℤ) :
    term1 τ c d n = cexp (π * I * τ * (c : ℂ) ^ 2 + 2 * π * I * c * d) *
      jacobiTheta₂_term n (c * τ + d) τ := by
  rw [term1, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- The bridge to Mathlib: `th1 τ c d = exp(πiτc² + 2πicd)·jacobiTheta₂(cτ + d, τ)`. -/
theorem th1_eq (τ : ℂ) (c d : ℝ) :
    th1 τ c d = cexp (π * I * τ * (c : ℂ) ^ 2 + 2 * π * I * c * d) * jacobiTheta₂ (c * τ + d) τ := by
  rw [th1, jacobiTheta₂, ← tsum_mul_left]
  exact tsum_congr fun n => term1_eq τ c d n

theorem summable_norm_term1 {τ : ℂ} (hτ : 0 < τ.im) (c d : ℝ) :
    Summable (fun n => ‖term1 τ c d n‖) := by
  have h := ((summable_jacobiTheta₂_term_iff (c * τ + d) τ).2 hτ).norm.mul_left
    ‖cexp (π * I * τ * (c : ℂ) ^ 2 + 2 * π * I * c * d)‖
  refine h.congr fun n => ?_
  rw [term1_eq, norm_mul]

theorem th1_shift_c (τ : ℂ) (c d : ℝ) (k : ℤ) : th1 τ (c + k) d = th1 τ c d := by
  rw [th1, th1]
  conv_rhs => rw [← (Equiv.addRight k).tsum_eq]
  congr 1; funext n
  simp only [term1, Equiv.coe_addRight]
  congr 1; push_cast; ring

theorem th1_shift_d (τ : ℂ) (c d : ℝ) (k : ℤ) :
    th1 τ c (d + k) = cexp (2 * π * I * c * k) * th1 τ c d := by
  rw [th1, th1, ← tsum_mul_left]
  congr 1; funext n
  have h : cexp (((-(n * k)) : ℤ) * (2 * π * I)) = 1 := exp_int_mul_two_pi_mul_I _
  rw [term1, term1, ← mul_one (cexp (_ + _)), ← h, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem dup1 {τ : ℂ} (hτ : 0 < τ.im) (c d : ℝ) :
    th1 τ c d ^ 2 = ∑ σ : Fin 2,
      th1 (2 * τ) (((σ : ℕ) : ℝ) / 2 + c) (2 * d) * th1 (2 * τ) (((σ : ℕ) : ℝ) / 2) 0 := by
  have hs := summable_norm_term1 hτ c d
  have hτ2 : 0 < (2 * τ).im := by simpa using hτ
  have hprod := summable_mul_of_summable_norm hs hs
  have h2 : Summable (fun c' => term1 τ c d (dupE1 c').1 * term1 τ c d (dupE1 c').2) :=
    dupE1.summable_iff.2 hprod
  rw [sq, th1, tsum_mul_tsum_of_summable_norm hs hs, ← dupE1.tsum_eq, h2.tsum_prod, tsum_fintype]
  congr 1; funext σ
  rw [th1, th1, tsum_mul_tsum_of_summable_norm (summable_norm_term1 hτ2 _ _)
    (summable_norm_term1 hτ2 _ _)]
  congr 1; funext w
  obtain ⟨p, q⟩ := w
  simp only [dupE1, Equiv.coe_fn_mk, term1, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Diagonal period matrices: the genus-2 theta factors. -/
theorem th2_diag {τ0 τ1 : ℂ} (h0 : 0 < τ0.im) (h1 : 0 < τ1.im) (c0 c1 d0 d1 : ℝ) :
    Th2 τ0 0 τ1 c0 c1 d0 d1 = th1 τ0 c0 d0 * th1 τ1 c1 d1 := by
  rw [th1, th1, tsum_mul_tsum_of_summable_norm (summable_norm_term1 h0 _ _)
    (summable_norm_term1 h1 _ _), Th2]
  congr 1; funext n
  simp only [term2, term1, ← Complex.exp_add]
  congr 1; ring

/-- The odd genus-1 theta constant vanishes. -/
theorem th1_odd (τ : ℂ) : th1 τ (1 / 2) (1 / 2) = 0 := by
  have h : th1 τ (1 / 2) (1 / 2) = -th1 τ (1 / 2) (1 / 2) := by
    conv_lhs => rw [th1, ← (Equiv.neg ℤ).tsum_eq, ← (Equiv.addRight (1 : ℤ)).tsum_eq]
    rw [th1, ← tsum_neg]
    congr 1; funext n
    simp only [term1, Equiv.coe_addRight, Equiv.neg_apply]
    have : π * I * τ * (((((-(n + 1) : ℤ) : ℝ) + 1 / 2 : ℝ)) : ℂ) ^ 2
        + 2 * π * I * (((((-(n + 1) : ℤ) : ℝ) + 1 / 2 : ℝ)) : ℂ) * ((1 / 2 : ℝ) : ℂ) =
        (π * I * τ * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ 2 + 2 * π * I * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ))
          + ((-n - 1 : ℤ) : ℂ) * (2 * π * I) + π * I := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_add, exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
    ring
  have : (2 : ℂ) * th1 τ (1 / 2) (1 / 2) = 0 := by linear_combination h
  simpa using this


/-! ## The explicit matrices: `Ω₂₄`, its partial inversion, and `W = −Ω₂₄⁻¹` -/

abbrev r6 : ℝ := √6
theorem r6_sq : r6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
theorem r6_pos : 0 < r6 := Real.sqrt_pos.2 (by norm_num)

/-- `Ω₂₄ = [[α0, β0], [β0, γ0]]`. -/
def α0 : ℂ := ⟨-2 / 7, 3 * r6 / 14⟩
def β0 : ℂ := ⟨-1 / 7, -r6 / 7⟩
def γ0 : ℂ := ⟨-4 / 7, 3 * r6 / 7⟩
/-- The partial inversion `[[−1/α0, β0/α0], [β0/α0, γ0 − β0²/α0]]`. -/
def α1 : ℂ := ⟨4 / 5, 3 * r6 / 5⟩
def β1 : ℂ := ⟨-2 / 5, r6 / 5⟩
def γ1 : ℂ := ⟨-4 / 5, 2 * r6 / 5⟩
/-- `W = −Ω₂₄⁻¹ = [[wa, wb], [wb, wc]] = [[1 + i√6/2, 1/2], [1/2, 1/2 + i√6/4]]`. -/
def wa : ℂ := ⟨1, r6 / 2⟩
def wb : ℂ := ⟨1 / 2, 0⟩
def wc : ℂ := ⟨1 / 2, r6 / 4⟩

theorem α0_ne : α0 ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp [α0] at this <;> linarith [r6_pos]
theorem γ1_ne : γ1 ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp [γ1] at this <;> linarith [r6_pos]

theorem eqA1 : -1 / α0 = α1 := by
  rw [div_eq_iff α0_ne]; apply Complex.ext <;> simp [α0, α1] <;> nlinarith [r6_sq]
theorem eqB1 : β0 / α0 = β1 := by
  rw [div_eq_iff α0_ne]; apply Complex.ext <;> simp [α0, β0, β1] <;> nlinarith [r6_sq]
theorem eqC1 : γ0 - β0 ^ 2 / α0 = γ1 := by
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', eq_div_iff α0_ne]
  apply Complex.ext <;> simp [α0, β0, γ0, γ1, pow_two] <;> nlinarith [r6_sq]
theorem eqA2 : -1 / γ1 = wc := by
  rw [div_eq_iff γ1_ne]; apply Complex.ext <;> simp [γ1, wc] <;> nlinarith [r6_sq]
theorem eqB2 : β1 / γ1 = wb := by
  rw [div_eq_iff γ1_ne]; apply Complex.ext <;> simp [γ1, β1, wb] <;> nlinarith [r6_sq]
theorem eqC2 : α1 - β1 ^ 2 / γ1 = wa := by
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', eq_div_iff γ1_ne]
  apply Complex.ext <;> simp [α1, β1, γ1, wa, pow_two] <;> nlinarith [r6_sq]

theorem pos0 : ∀ x y : ℝ, r6 / 7 * (x ^ 2 + y ^ 2) ≤
    α0.im * x ^ 2 + 2 * β0.im * x * y + γ0.im * y ^ 2 := by
  intro x y; simp only [α0, β0, γ0]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg (x - 2 * y))]
theorem pos1 : ∀ x y : ℝ, r6 / 5 * (x ^ 2 + y ^ 2) ≤
    α1.im * x ^ 2 + 2 * β1.im * x * y + γ1.im * y ^ 2 := by
  intro x y; simp only [α1, β1, γ1]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg x), mul_nonneg r6_pos.le (sq_nonneg (x + y))]
theorem pos1s : ∀ x y : ℝ, r6 / 5 * (x ^ 2 + y ^ 2) ≤
    γ1.im * x ^ 2 + 2 * β1.im * x * y + α1.im * y ^ 2 := by
  intro x y; simp only [α1, β1, γ1]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg y), mul_nonneg r6_pos.le (sq_nonneg (x + y))]
theorem posW : ∀ x y : ℝ, r6 / 4 * (x ^ 2 + y ^ 2) ≤
    wa.im * x ^ 2 + 2 * wb.im * x * y + wc.im * y ^ 2 := by
  intro x y; simp only [wa, wb, wc]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg x)]
theorem posW2 : ∀ x y : ℝ, r6 / 2 * (x ^ 2 + y ^ 2) ≤
    (2 * wa).im * x ^ 2 + 2 * (2 * wb).im * x * y + (2 * wc).im * y ^ 2 := by
  intro x y; simp [wa, wb, wc]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg x)]
theorem posWs : ∀ x y : ℝ, r6 / 4 * (x ^ 2 + y ^ 2) ≤
    wc.im * x ^ 2 + 2 * wb.im * x * y + wa.im * y ^ 2 := by
  intro x y; simp only [wa, wb, wc]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg y)]

theorem d0pos : (0 : ℝ) < r6 / 7 := div_pos r6_pos (by norm_num)
theorem d1pos : (0 : ℝ) < r6 / 5 := div_pos r6_pos (by norm_num)
theorem d2pos : (0 : ℝ) < r6 / 4 := div_pos r6_pos (by norm_num)
theorem d3pos : (0 : ℝ) < r6 / 2 := div_pos r6_pos (by norm_num)

/-- **The inversion `Ω₂₄ ↦ W`** on theta constants with characteristics: two partial inversions
(each Mathlib's one-variable functional equation) and two coordinate swaps. -/
theorem invert (a0 a1 : ℝ) (b0 b1 : ℤ) :
    Th2 α0 β0 γ0 (a0 / 2) (a1 / 2) ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) =
      1 / (-I * α0) ^ (1 / 2 : ℂ) * cexp (2 * π * I * (a0 / 2 : ℝ) * ((b0 : ℝ) / 2 : ℝ)) *
      (1 / (-I * γ1) ^ (1 / 2 : ℂ) * cexp (2 * π * I * (a1 / 2 : ℝ) * ((b1 : ℝ) / 2 : ℝ))) *
      Th2 wa wb wc ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) (a0 / 2) (a1 / 2) := by
  have hα : 0 < α0.im := by simp [α0] <;> exact r6_pos
  have hγ : 0 < γ1.im := by simp [γ1] <;> exact r6_pos
  rw [pi0 hα _ _ _ _ (summable_term2 d0pos pos0 _ _ _ _)
    (by rw [eqA1, eqB1, eqC1]; exact summable_term2 d1pos pos1 _ _ _ _), eqA1, eqB1, eqC1,
    th2_swap, pi0 hγ _ _ _ _ (summable_term2 d1pos pos1s _ _ _ _)
    (by rw [eqA2, eqB2, eqC2]; exact summable_term2 d2pos posWs _ _ _ _), eqA2, eqB2, eqC2,
    th2_swap]
  have e0 : ((b0 : ℝ) / 2) = -((b0 : ℝ) / 2) + (b0 : ℤ) := by ring
  have e1 : ((b1 : ℝ) / 2) = -((b1 : ℝ) / 2) + (b1 : ℤ) := by ring
  conv_rhs => rw [e0, e1, th2_shift_c]
  ring


/-! ## `2W = diag(i√6, i√6/2) + [[2,1],[1,1]]`: translation to a diagonal matrix -/

/-- `τ₆ = i√6`, `τ₃ = i√6/2`: the two CM points of discriminant `−24` (one per ideal class). -/
def τ6 : ℂ := ⟨0, r6⟩
def τ3 : ℂ := ⟨0, r6 / 2⟩

theorem τ6_im : 0 < τ6.im := by simp [τ6] <;> exact r6_pos
theorem τ3_im : 0 < τ3.im := by simp [τ3] <;> exact div_pos r6_pos (by norm_num)

theorem h2wa : 2 * wa = τ6 + 2 := by apply Complex.ext <;> simp [wa, τ6] <;> ring
theorem h2wb : 2 * wb = 1 := by apply Complex.ext <;> simp [wb]
theorem h2wc : 2 * wc = τ3 + 1 := by apply Complex.ext <;> simp [wc, τ3] <;> ring

theorem th2_phase {α β γ α' β' γ' : ℂ} {c0 c1 d0 d1 d0' d1' : ℝ} (κ : ℂ)
    (h : ∀ n : ℤ × ℤ, ∃ k : ℤ,
      π * I * (α * (((n.1 : ℝ) + c0 : ℝ) : ℂ) ^ 2 + 2 * β * (((n.1 : ℝ) + c0 : ℝ) : ℂ) * (((n.2 : ℝ) + c1 : ℝ) : ℂ)
        + γ * (((n.2 : ℝ) + c1 : ℝ) : ℂ) ^ 2)
        + 2 * π * I * ((((n.1 : ℝ) + c0 : ℝ) : ℂ) * d0 + (((n.2 : ℝ) + c1 : ℝ) : ℂ) * d1) =
      (π * I * (α' * (((n.1 : ℝ) + c0 : ℝ) : ℂ) ^ 2 + 2 * β' * (((n.1 : ℝ) + c0 : ℝ) : ℂ) * (((n.2 : ℝ) + c1 : ℝ) : ℂ)
        + γ' * (((n.2 : ℝ) + c1 : ℝ) : ℂ) ^ 2)
        + 2 * π * I * ((((n.1 : ℝ) + c0 : ℝ) : ℂ) * d0' + (((n.2 : ℝ) + c1 : ℝ) : ℂ) * d1'))
        + κ + k * (2 * π * I)) :
    Th2 α β γ c0 c1 d0 d1 = cexp κ * Th2 α' β' γ' c0 c1 d0' d1' := by
  rw [Th2, Th2, ← tsum_mul_left]
  congr 1; funext n
  obtain ⟨k, hk⟩ := h n
  rw [term2, hk, Complex.exp_add, Complex.exp_add, exp_int_mul_two_pi_mul_I, term2]
  ring

theorem cast_even (n : ℤ) : ∃ t : ℤ, ((n : ℂ) * (n + 1)) = t + t := by
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self n
  exact ⟨t, by exact_mod_cast ht⟩

/-- `U(c) = θ[c; 0](2W)` for `c ∈ {0, 1/2}²`. -/
def U (c0 c1 : ℝ) : ℂ := Th2 (2 * wa) (2 * wb) (2 * wc) c0 c1 0 0

theorem U00 : U 0 0 = th1 τ6 0 0 * th1 τ3 0 (1 / 2) := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 0) (d1' := 1 / 2) 0, th2_diag τ6_im τ3_im]
  · simp
  intro n
  obtain ⟨t, ht⟩ := cast_even (n.2 - 1)
  refine ⟨n.1 ^ 2 + n.1 * n.2 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

theorem U10 : U (1 / 2) 0 = I * (th1 τ6 (1 / 2) 0 * th1 τ3 0 0) := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 0) (d1' := 0) (π * I / 2),
    th2_diag τ6_im τ3_im]
  · congr 1
    rw [show (π : ℂ) * I / 2 = π / 2 * I by ring, Complex.exp_mul_I]
    have h1 : Complex.cos (π / 2) = 0 := by exact_mod_cast Real.cos_pi_div_two
    have h2 : Complex.sin (π / 2) = 1 := by exact_mod_cast Real.sin_pi_div_two
    rw [h1, h2]; ring
  intro n
  obtain ⟨t, ht⟩ := cast_even n.2
  refine ⟨n.1 ^ 2 + n.1 + n.1 * n.2 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

theorem U01 : U 0 (1 / 2) = cexp (π * I / 4) * (th1 τ6 0 (1 / 2) * th1 τ3 (1 / 2) 0) := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 1 / 2) (d1' := 0) (π * I / 4),
    th2_diag τ6_im τ3_im]
  intro n
  obtain ⟨t, ht⟩ := cast_even n.2
  refine ⟨n.1 ^ 2 + n.1 * n.2 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

theorem U11 : U (1 / 2) (1 / 2) = 0 := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 1 / 2) (d1' := 1 / 2) (π * I / 4),
    th2_diag τ6_im τ3_im, th1_odd]
  · simp
  intro n
  obtain ⟨t, ht⟩ := cast_even n.2
  refine ⟨n.1 ^ 2 + n.1 * n.2 + n.1 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

end CM24

namespace CM24
open HDec.LeafQCheck.HM.QMSplit.Value24

/-! ## Bridge to `PkgI1.thetaConst` -/

theorem thetaConst_eq (m : HDec.PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : Ω 1 0 = Ω 0 1) :
    HDec.PkgI1.thetaConst m Ω = Th2 (Ω 0 0) (Ω 0 1) (Ω 1 1) (((m.1 0 : ℕ) : ℝ) / 2) (((m.1 1 : ℕ) : ℝ) / 2)
      (((m.2 0 : ℕ) : ℝ) / 2) (((m.2 1 : ℕ) : ℝ) / 2) := by
  rw [HDec.PkgI1.thetaConst, Th2, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  congr 1; funext p
  simp only [finTwoArrowEquiv_symm_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, term2,
    Matrix.cons_val_zero, Matrix.cons_val_one, hΩ]
  congr 1; push_cast; ring

theorem om24_00 : Om24 0 0 = α0 := by
  apply Complex.ext <;> simp [Om24, α0] <;> ring
theorem om24_01 : Om24 0 1 = β0 := by
  apply Complex.ext <;> simp [Om24, β0] <;> ring
theorem om24_10 : Om24 1 0 = β0 := by
  apply Complex.ext <;> simp [Om24, β0] <;> ring
theorem om24_11 : Om24 1 1 = γ0 := by
  apply Complex.ext <;> simp [Om24, γ0] <;> ring


/-! ## Squares of theta constants at `Ω₂₄` in terms of `U` -/

/-- `𝓔 = 1/((−iα0)(−iγ1))`: the square of the two automorphy factors. -/
def Ecal : ℂ := 1 / (-I * α0) * (1 / (-I * γ1))

theorem cpow_half_sq (x : ℂ) : (1 / x ^ (1 / 2 : ℂ)) ^ 2 = 1 / x := by
  rw [div_pow, one_pow, show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num, Complex.cpow_nat_inv_pow x two_ne_zero]

theorem sq_inv (a0 a1 b0 b1 : ℕ) :
    Th2 α0 β0 γ0 ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ^ 2 =
      Ecal * cexp (π * I * ((a0 * b0 + a1 * b1 : ℕ) : ℂ)) *
        Th2 wa wb wc ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ^ 2 := by
  have h := invert (a0 : ℝ) (a1 : ℝ) (b0 : ℤ) (b1 : ℤ)
  simp only [Int.cast_natCast] at h
  have e1 : cexp (2 * π * I * ((a0 : ℝ) / 2 : ℝ) * ((b0 : ℝ) / 2 : ℝ)) ^ 2 *
      cexp (2 * π * I * ((a1 : ℝ) / 2 : ℝ) * ((b1 : ℝ) / 2 : ℝ)) ^ 2 =
      cexp (π * I * ((a0 * b0 + a1 * b1 : ℕ) : ℂ)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [h]
  simp only [mul_pow]
  rw [cpow_half_sq, cpow_half_sq, ← e1, Ecal]
  ring

/-- `U` with characteristic reduced mod `ℤ²`. -/
def Uf (s0 s1 : ℕ) : ℂ := U (((s0 % 2 : ℕ) : ℝ) / 2) (((s1 % 2 : ℕ) : ℝ) / 2)

theorem U_nat (s0 s1 : ℕ) : U ((s0 : ℝ) / 2) ((s1 : ℝ) / 2) = Uf s0 s1 := by
  rw [Uf, U, U]
  conv_rhs => rw [← th2_shift_c _ _ _ _ _ _ _ ((s0 / 2 : ℕ) : ℤ) ((s1 / 2 : ℕ) : ℤ)]
  simp only [Int.cast_natCast]
  have h0 : (s0 : ℝ) = ((s0 % 2 : ℕ) : ℝ) + 2 * ((s0 / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div s0 2).symm
  have h1 : (s1 : ℝ) = ((s1 % 2 : ℕ) : ℝ) + 2 * ((s1 / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div s1 2).symm
  congr 1 <;> linarith

theorem exp_pi_nat (k : ℕ) : cexp (π * I * (k : ℂ)) = (-1) ^ k := by
  rw [mul_comm, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- **Duplication at `W`, with the translation reductions.** -/
theorem sqW (a0 a1 b0 b1 : ℕ) :
    Th2 wa wb wc ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ^ 2 =
      ∑ σ : Fin 2 × Fin 2, (-1 : ℂ) ^ (((σ.1 : ℕ) + b0) * a0 + ((σ.2 : ℕ) + b1) * a1) *
        Uf ((σ.1 : ℕ) + b0) ((σ.2 : ℕ) + b1) * Uf σ.1 σ.2 := by
  rw [dup2 _ _ _ _ (summable_norm_term2 d2pos posW _ _ _ _)
    (fun _ _ _ _ => summable_norm_term2 d3pos posW2 _ _ _ _)]
  congr 1; funext σ
  have e0 : 2 * ((a0 : ℝ) / 2) = 0 + ((a0 : ℤ) : ℝ) := by push_cast; ring
  have e1 : 2 * ((a1 : ℝ) / 2) = 0 + ((a1 : ℤ) : ℝ) := by push_cast; ring
  rw [e0, e1, th2_shift_d]
  have c0 : ((σ.1 : ℕ) : ℝ) / 2 + (b0 : ℝ) / 2 = (((σ.1 : ℕ) + b0 : ℕ) : ℝ) / 2 := by push_cast; ring
  have c1 : ((σ.2 : ℕ) : ℝ) / 2 + (b1 : ℝ) / 2 = (((σ.2 : ℕ) + b1 : ℕ) : ℝ) / 2 := by push_cast; ring
  rw [c0, c1]
  change _ * U _ _ * U _ _ = _
  rw [U_nat, U_nat, ← exp_pi_nat]
  congr 2
  congr 1; push_cast; ring

theorem om24_sym : Om24 1 0 = Om24 0 1 := by rw [om24_10, om24_01]

theorem sq_char (m : HDec.PkgI1.Char2) :
    HDec.PkgI1.thetaConst m Om24 ^ 2 =
      Ecal * cexp (π * I * (((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ) : ℕ) : ℂ)) *
      ∑ σ : Fin 2 × Fin 2, (-1 : ℂ) ^ (((σ.1 : ℕ) + (m.2 0 : ℕ)) * (m.1 0 : ℕ) + ((σ.2 : ℕ) + (m.2 1 : ℕ)) * (m.1 1 : ℕ)) *
        Uf ((σ.1 : ℕ) + (m.2 0 : ℕ)) ((σ.2 : ℕ) + (m.2 1 : ℕ)) * Uf σ.1 σ.2 := by
  rw [thetaConst_eq m Om24 om24_sym, om24_00, om24_01, om24_11, sq_inv, sqW]

theorem U11' : U (1 / 2) (1 / 2) = 0 := U11
theorem U11'' : U 2⁻¹ 2⁻¹ = 0 := by rw [← one_div]; exact U11

theorem exp_pi_two : cexp (π * I * 2) = 1 := by
  rw [show (π : ℂ) * I * 2 = ((1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring, exp_int_mul_two_pi_mul_I]

theorem sqc0 : HDec.PkgI1.thetaConst (![0, 0], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 + U (1 / 2) 0 ^ 2 + U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc1 : HDec.PkgI1.thetaConst (![0, 1], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 + U (1 / 2) 0 ^ 2 - U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc2 : HDec.PkgI1.thetaConst (![1, 0], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 - U (1 / 2) 0 ^ 2 + U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc3 : HDec.PkgI1.thetaConst (![1, 1], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 - U (1 / 2) 0 ^ 2 - U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc4 : HDec.PkgI1.thetaConst (![0, 0], ![1, 0]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc5 : HDec.PkgI1.thetaConst (![0, 1], ![1, 0]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc6 : HDec.PkgI1.thetaConst (![0, 0], ![0, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U 0 (1 / 2)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc7 : HDec.PkgI1.thetaConst (![1, 0], ![0, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U 0 (1 / 2)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc8 : HDec.PkgI1.thetaConst (![0, 0], ![1, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 (1 / 2) * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc9 : HDec.PkgI1.thetaConst (![1, 1], ![1, 1]) Om24 ^ 2 =
    Ecal * (-(2 * U 0 (1 / 2) * U (1 / 2) 0)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

/-! ## Genus one: duplication (Landen) and Jacobi's identity -/

theorem th1_c1 (τ : ℂ) (d : ℝ) : th1 τ 1 d = th1 τ 0 d := by
  simpa using th1_shift_c τ 0 d 1

theorem th1_d1 (τ : ℂ) (c : ℝ) : th1 τ c 1 = cexp (2 * π * I * c) * th1 τ c 0 := by
  simpa using th1_shift_d τ c 0 1

theorem exp_half : cexp (2 * π * I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
  rw [show (2 : ℂ) * π * I * ((1 / 2 : ℝ) : ℂ) = π * I by push_cast; ring, Complex.exp_pi_mul_I]

theorem dupA {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 0 ^ 2 = th1 (2 * τ) 0 0 ^ 2 + th1 (2 * τ) (1 / 2) 0 ^ 2 := by
  rw [dup1 hτ, Fin.sum_univ_two]; norm_num; ring

theorem dupB {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 (1 / 2) ^ 2 = th1 (2 * τ) 0 0 ^ 2 - th1 (2 * τ) (1 / 2) 0 ^ 2 := by
  rw [dup1 hτ, Fin.sum_univ_two]
  have e : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  simp only [e, th1_d1, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_div, zero_add,
    add_zero, exp_half]
  push_cast; simp only [mul_zero, Complex.exp_zero]; ring

theorem dupC {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ (1 / 2) 0 ^ 2 = 2 * th1 (2 * τ) 0 0 * th1 (2 * τ) (1 / 2) 0 := by
  rw [dup1 hτ, Fin.sum_univ_two]
  have e : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_div, zero_add, mul_zero, e, th1_c1]
  ring

/-- **Jacobi's quartic identity** `θ₀₀⁴ = θ₀₁⁴ + θ₁₀⁴`, from the duplication formulas. -/
theorem jacobi {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 0 ^ 4 = th1 τ 0 (1 / 2) ^ 4 + th1 τ (1 / 2) 0 ^ 4 := by
  have hA := dupA hτ; have hB := dupB hτ; have hC := dupC hτ
  linear_combination (th1 τ 0 0 ^ 2 + th1 (2 * τ) 0 0 ^ 2 + th1 (2 * τ) (1 / 2) 0 ^ 2) * hA
    - (th1 τ 0 (1 / 2) ^ 2 + th1 (2 * τ) 0 0 ^ 2 - th1 (2 * τ) (1 / 2) 0 ^ 2) * hB
    - (th1 τ (1 / 2) 0 ^ 2 + 2 * th1 (2 * τ) 0 0 * th1 (2 * τ) (1 / 2) 0) * hC

theorem h2τ3 : 2 * τ3 = τ6 := by apply Complex.ext <;> simp [τ3, τ6] <;> ring

end CM24
