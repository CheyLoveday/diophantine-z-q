import ZInQKernel.Contrib.OneProof.ThetaDirect.Glue
import ZInQKernel.Contrib.OneProof.ThetaModularityM46

/-! # theta-direct (helper 5/5): the genuine Siegel Eisenstein series, the LEAF `IgusaThetaExpressions`, and the
modularity of the Eisenstein series

* Lines 4-100 of origin/wip/theta-fold (8e3dbdea) `ZInQKernel/Contrib/OneProof/LinYangPrinted.lean`, verbatim
  (its §1 and the first leaf of its §2: `botRel` … `siegelEis`, `igusaChi10E`, `igusaChi12E`, `lyS2` … `lyS6`,
  `IgusaThetaExpressions`), and its lines 139-210 (`thetaConst_omega_analyticAt`). theta-fold's second leaf `LinYangEx29All` and everything after it are NOT copied
  (`LinYangEx29All` is false: wip/leaf-audit 8040661a, `LeafAudit1115.not_linYangEx29All`).
* §6 of origin/wip/linyang-printed `scratch/linyang-printed/LinYangPrintedFull.lean` (lines 2993-3310), verbatim,
  with linyang-printed's `SpMat` (its line 2470, `Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ`) renamed to
  gt-theta's `GapTheta.Mat4` (the same type; theta-fold's dedupe), and the modularity of Igusa's `χ₁₀`
  (linyang-printed lines 3330-3338, `igusaChi10E_modular`). -/

/-! # theta-fold (4/4): the printed leaves `IgusaThetaExpressions`, `LinYangEx29All` and Route 1 from them

linyang-printed's scratch/linyang-printed/LinYangPrintedFull.lean §1-§4 and §10: the genuine Siegel Eisenstein
series `siegelEis k` (a sum over `Γ_∞\Sp₄(ℤ)`), Igusa's `χ₁₀`, `χ₁₂` (1962 combinations), Lin–Yang's `s_k`; the
two LEAVES `IgusaThetaExpressions` (Igusa 1964/1967) and `LinYangEx29All` (Lin–Yang 2020, Example 29, the
relations only); `LinYangThetaCurve` from them (eliminating `j₆`, density off one countable `Γ*`-orbit); and
`thetaRatiosAtQM_of_printedAll`, which the chain's top `HDec.HSyn.sixContactMin_of_open29` uses in place of the
field `thetaRatiosAlgebraic`. Locators of both leaves UNVERIFIED (see the docstrings).
docs/research/theta-fold.md, docs/research/linyang-printed.md. -/

noncomputable section

namespace HDec.HSyn.G0Split.ThetaPt.LinYangPrinted

open Complex Matrix Filter Topology
open ThetaGlue (psi4Th psi6Th chi10Th chi12Th LinYangThetaCurve)
open HSyn.G0Split.FibreQM.PeriodMap (U isOpen_U thTerm qf quad_lower differentiableAt_omega summable_gb2
  norm_thTerm_le omegaSiegel_proof)

/-! ## 1. Genuine definitions: Siegel Eisenstein series, Igusa's `χ₁₀`, `χ₁₂`, Lin–Yang's `s_k` -/

/-- Same coset of the Siegel parabolic `Γ_∞ = {M ∈ Sp₄(ℤ) : C = 0}`: the bottom block rows satisfy
`(C_N, D_N) = U·(C_M, D_M)` for some `U ∈ GL₂(ℤ)`. -/
def botRel (M N : Matrix.symplecticGroup (Fin 2) ℤ) : Prop :=
  ∃ U : GL (Fin 2) ℤ,
    (N : GapTheta.Mat4).toBlocks₂₁ = (U : Matrix (Fin 2) (Fin 2) ℤ) * (M : GapTheta.Mat4).toBlocks₂₁ ∧
    (N : GapTheta.Mat4).toBlocks₂₂ = (U : Matrix (Fin 2) (Fin 2) ℤ) * (M : GapTheta.Mat4).toBlocks₂₂

theorem botRel_equiv : Equivalence botRel where
  refl M := ⟨1, by simp, by simp⟩
  symm := by
    rintro M N ⟨U, h1, h2⟩
    refine ⟨U⁻¹, ?_, ?_⟩
    · rw [h1, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    · rw [h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  trans := by
    rintro M N P ⟨U, h1, h2⟩ ⟨V, h3, h4⟩
    refine ⟨V * U, ?_, ?_⟩
    · rw [h3, h1, Units.val_mul, Matrix.mul_assoc]
    · rw [h4, h2, Units.val_mul, Matrix.mul_assoc]

/-- The coset relation as a setoid on `Sp₄(ℤ)`. -/
def botSetoid : Setoid (Matrix.symplecticGroup (Fin 2) ℤ) := ⟨botRel, botRel_equiv⟩

/-- `Γ_∞\Sp₄(ℤ)`, i.e. the classes of coprime symmetric pairs `(C, D)` modulo `GL₂(ℤ)`. -/
abbrev SiegelCosets := Quotient botSetoid

/-- **The Siegel Eisenstein series of degree 2 and weight `k`** (Igusa, Amer. J. Math. 84 (1962), the forms
`ψ_k`; the standard definition, e.g. Klingen, *Introductory lectures on Siegel modular forms*, §5):
`ψ_k(Ω) = Σ_{M ∈ Γ_∞\Sp₄(ℤ)} det(CΩ + D)^{-k}`, one representative per coset. For even `k` the summand does not
depend on the representative (`det U = ±1`); for `k ≥ 4` the series converges absolutely on `𝔥₂`, so the `tsum`
is the classical value. -/
def siegelEis (k : ℕ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑' c : SiegelCosets,
    (PkgI1.spFactor ((Quotient.out c : Matrix.symplecticGroup (Fin 2) ℤ) : GapTheta.Mat4) Ω)⁻¹ ^ k

/-- **Igusa's cusp form `χ₁₀`** (Igusa 1962, as a combination of Eisenstein series; constants recalled,
UNVERIFIED as a citation, VERIFIED against the theta expression on 76 Fourier coefficients, py/fourier.py):
`χ₁₀ = −43867·2⁻¹²3⁻⁵5⁻²7⁻¹53⁻¹ (ψ₄ψ₆ − ψ₁₀)`. -/
def igusaChi10E (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (-43867 / (2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 * 53) : ℂ) * (siegelEis 4 Ω * siegelEis 6 Ω - siegelEis 10 Ω)

/-- **Igusa's cusp form `χ₁₂`** (Igusa 1962; same status as `igusaChi10E`):
`χ₁₂ = 131·593·2⁻¹³3⁻⁷5⁻³7⁻²337⁻¹ (3²7²ψ₄³ + 2·5³ψ₆² − 691ψ₁₂)`. -/
def igusaChi12E (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (131 * 593 / (2 ^ 13 * 3 ^ 7 * 5 ^ 3 * 7 ^ 2 * 337) : ℂ) *
    (3 ^ 2 * 7 ^ 2 * siegelEis 4 Ω ^ 3 + 2 * 5 ^ 3 * siegelEis 6 Ω ^ 2 - 691 * siegelEis 12 Ω)

/-- Lin–Yang's normalized generators (arXiv:1807.00466v1 §2, as restated in scratch/h-v14/igusa_check.py):
`s₂ = ψ₄`. -/
def lyS2 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := siegelEis 4 Ω
/-- `s₃ = ψ₆`. -/
def lyS3 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := siegelEis 6 Ω
/-- `s₅ = 2¹²3⁵χ₁₀`. -/
def lyS5 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 2 ^ 12 * 3 ^ 5 * igusaChi10E Ω
/-- `s₆ = 2¹²3⁶χ₁₂`. -/
def lyS6 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 2 ^ 12 * 3 ^ 6 * igusaChi12E Ω

/-! ## 2. The two leaves, in printed form -/

/-- **LEAF (Igusa: the theta expressions of the generators).** On the Siegel upper half-space `𝔥₂`, the Eisenstein
series `ψ₄`, `ψ₆` and Igusa's cusp forms `χ₁₀`, `χ₁₂` equal their theta expressions:
`ψ₄ = 2⁻² Σ_m θ_m⁸`, `ψ₆ = 2⁻² Σ_{syzygous} ±(θ_{m₁}θ_{m₂}θ_{m₃})⁴`, `χ₁₀ = −2⁻¹⁴ ∏_m θ_m²`,
`χ₁₂ = 2⁻¹⁷3⁻¹ Σ_{Göpel Q} ∏_{m ∉ Q} θ_m⁴` (theta-glue's `psi4Th`, `psi6Th`, `chi10Th`, `chi12Th`).

Sources: J.-I. Igusa, *On Siegel modular forms of genus two (II)*, Amer. J. Math. 86 (1964), and *Modular forms and
projective invariants*, Amer. J. Math. 89 (1967), p. 848 (locators UNVERIFIED, no network; the printed sign rule of
`ψ₆` was not read). Evidence (VERIFIED, exact, py/fourier.py): all 76 Fourier coefficients at half-integral
`T = (n, r, m)`, `n, m ≤ 2`, agree on both sides; since `dim M_k(Sp₄(ℤ)) = 1, 1, 2, 3` for `k = 4, 6, 10, 12` and
the theta expressions are modular (theta-glue py/invariants.py), this pins the identities, including the sign
choice in `ψ₆` and Igusa's 1962 constants in `igusaChi10E`, `igusaChi12E`. Form: printed (the theta expressions as
theorems about Igusa's forms). -/
def IgusaThetaExpressions : Prop :=
  ∀ Ω ∈ PkgI1.SiegelH2,
    siegelEis 4 Ω = psi4Th Ω ∧ siegelEis 6 Ω = psi6Th Ω ∧
      igusaChi10E Ω = chi10Th Ω ∧ igusaChi12E Ω = chi12Th Ω


/-! theta-direct: lines 139-210 of theta-fold's `LinYangPrinted.lean` (its §3, `thetaConst_omega_analyticAt`), verbatim. -/

/-- Each theta constant along `Ω` is analytic on `ℍ` (copy of the inner step of period-map's
`thetaOmegaAnalytic_of`, TailJ). -/
theorem thetaConst_omega_analyticAt {τ₀ : ℂ} (hτ₀ : τ₀ ∈ U) (m : PkgI1.Char2) :
    AnalyticAt ℂ (fun τ => PkgI1.thetaConst m (PkgI1.Omega τ)) τ₀ := by
  have hS := omegaSiegel_proof
  have hτ₀' : (0 : ℝ) < τ₀.im := hτ₀
  obtain ⟨hsym, hpd⟩ := hS τ₀ hτ₀'
  set p : ℂ → ℝ := fun τ => (PkgI1.Omega τ 0 0).im with hp
  set q : ℂ → ℝ := fun τ => ((PkgI1.Omega τ 0 1).im + (PkgI1.Omega τ 1 0).im) / 2 with hq
  set r : ℂ → ℝ := fun τ => (PkgI1.Omega τ 1 1).im with hr
  have hcont : ∀ i j, ContinuousAt (fun τ => (PkgI1.Omega τ i j).im) τ₀ := fun i j =>
    Complex.continuous_im.continuousAt.comp (differentiableAt_omega hτ₀'.ne' i j).continuousAt
  have hp0 : 0 < p τ₀ := by
    have := hpd.diag_pos (i := 0); simpa [hp] using this
  have hr0 : 0 < r τ₀ := by
    have := hpd.diag_pos (i := 1); simpa [hr] using this
  have hsym01 : PkgI1.Omega τ₀ 1 0 = PkgI1.Omega τ₀ 0 1 := by
    have := congrFun (congrFun hsym 0) 1; simpa using this
  have hdet0 : 0 < p τ₀ * r τ₀ - q τ₀ ^ 2 := by
    have := hpd.det_pos
    rw [Matrix.det_fin_two] at this
    simp only [Matrix.map_apply] at this
    rw [hsym01] at this
    simp only [hp, hq, hr, hsym01]
    nlinarith [this]
  set g : ℂ → ℝ := fun τ => (p τ * r τ - q τ ^ 2) / (p τ + r τ) with hg
  have hg0 : 0 < g τ₀ := div_pos hdet0 (add_pos hp0 hr0)
  have hpc : ContinuousAt p τ₀ := hcont 0 0
  have hrc : ContinuousAt r τ₀ := hcont 1 1
  have hqc : ContinuousAt q τ₀ := ((hcont 0 1).add (hcont 1 0)).div_const 2
  have hgc : ContinuousAt g τ₀ :=
    ((hpc.mul hrc).sub (hqc.pow 2)).div (hpc.add hrc) (add_pos hp0 hr0).ne'
  have hev : ∀ᶠ τ in 𝓝 τ₀, τ ∈ U ∧ 0 < p τ + r τ ∧ g τ₀ / 2 < g τ := by
    refine (show ∀ᶠ τ in 𝓝 τ₀, τ ∈ U from isOpen_U.mem_nhds hτ₀).and ((?_ : ∀ᶠ τ in 𝓝 τ₀, 0 < p τ + r τ).and ?_)
    · exact (hpc.add hrc).eventually (lt_mem_nhds (add_pos hp0 hr0))
    · exact hgc.eventually (lt_mem_nhds (half_lt_self hg0))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set c := g τ₀ / 2 with hcdef
  have hc : 0 < c := half_pos hg0
  have hq_ball : ∀ τ ∈ Metric.ball τ₀ ε, ∀ w : Fin 2 → ℝ, c * (w 0 ^ 2 + w 1 ^ 2) ≤ qf τ w := by
    intro τ hτ w
    obtain ⟨-, hpr, hgt⟩ := hball τ hτ
    have hl := quad_lower (p τ) (q τ) (r τ) (w 0) (w 1) hpr
    have hw : 0 ≤ w 0 ^ 2 + w 1 ^ 2 := by positivity
    calc c * (w 0 ^ 2 + w 1 ^ 2) ≤ g τ * (w 0 ^ 2 + w 1 ^ 2) :=
          mul_le_mul_of_nonneg_right hgt.le hw
      _ ≤ _ := by
        refine hl.trans (le_of_eq ?_)
        simp only [qf, hp, hq, hr]
        ring
  have hdiff : ∀ n, DifferentiableOn ℂ (thTerm m n) (Metric.ball τ₀ ε) := by
    intro n σ hσ
    have hσU : (0 : ℝ) < σ.im := (hball σ hσ).1
    have hΩ := fun i j => differentiableAt_omega hσU.ne' i j
    apply DifferentiableAt.differentiableWithinAt
    set V : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2 with hV
    set Bv : Fin 2 → ℂ := fun k => ((m.2 k : ℕ) : ℂ) with hBv
    have key : thTerm m n = fun τ => Complex.exp (Real.pi * I * (V ⬝ᵥ (PkgI1.Omega τ *ᵥ V)) +
        Real.pi * I * (V ⬝ᵥ Bv)) := rfl
    have hq : DifferentiableAt ℂ (fun τ => V ⬝ᵥ (PkgI1.Omega τ *ᵥ V)) σ := by
      simp only [dotProduct, Matrix.mulVec]
      refine DifferentiableAt.fun_sum fun i _ => ?_
      refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun j _ => ?_) _
      exact (hΩ i j).mul_const _
    rw [key]
    exact ((hq.const_mul _).add_const _).cexp
  have hdon : DifferentiableOn ℂ (fun τ => PkgI1.thetaConst m (PkgI1.Omega τ))
      (Metric.ball τ₀ ε) :=
    differentiableOn_tsum_of_summable_norm (summable_gb2 hc) hdiff Metric.isOpen_ball
      (fun n τ hτ => norm_thTerm_le hc m n τ (hq_ball τ hτ))
  exact hdon.analyticAt (Metric.ball_mem_nhds τ₀ hε)



/-! ## 6. Modularity of the Siegel Eisenstein series (proved) -/

/-! ### Positivity of the imaginary part on complex vectors -/

/-- `v̄ᵀ (Im Ω) v` for complex `v` (written with `Ω`). -/
def qIm (Ω : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) : ℝ :=
  ∑ i, ∑ j, (Ω i j).im * ((v i).re * (v j).re + (v i).im * (v j).im)

theorem qIm_pos {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    0 < qIm Ω v := by
  obtain ⟨-, hpd⟩ := hΩ
  have hq := (posDef_iff_dotProduct_mulVec.mp hpd).2
  set a : Fin 2 → ℝ := fun i => (v i).re
  set b : Fin 2 → ℝ := fun i => (v i).im
  have ha : 0 ≤ star a ⬝ᵥ ((Ω.map Complex.im) *ᵥ a) := by
    by_cases h : a = 0
    · simp [h]
    · exact (hq h).le
  have hb : 0 ≤ star b ⬝ᵥ ((Ω.map Complex.im) *ᵥ b) := by
    by_cases h : b = 0
    · simp [h]
    · exact (hq h).le
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    apply Complex.ext
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  have key : qIm Ω v = star a ⬝ᵥ ((Ω.map Complex.im) *ᵥ a) + star b ⬝ᵥ ((Ω.map Complex.im) *ᵥ b) := by
    simp only [qIm, dotProduct, mulVec, Matrix.map_apply, star_trivial, Fin.sum_univ_two, a, b]
    ring
  rw [key]
  rcases hab with h | h
  · have := hq h; linarith
  · have := hq h; linarith

/-- `ω(u, u)` for `u = (Ωv, v)`: `star(Ωv)·(−v) + star v·(Ωv) = 2i·qIm`. -/
theorem omega_form {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ωᵀ = Ω) (v : Fin 2 → ℂ) :
    star (Ω *ᵥ v) ⬝ᵥ (-v) + star v ⬝ᵥ (Ω *ᵥ v) = 2 * Complex.I * (qIm Ω v : ℂ) := by
  have h10 : Ω 1 0 = Ω 0 1 := by
    have := congrFun (congrFun hs 0) 1; simpa using this
  apply Complex.ext <;>
    simp [qIm, dotProduct, mulVec, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, h10] <;> ring

/-! ### Symplectic invariance of `ω(a, b) = a·Jb` -/

/-- Integer matrices cast to `ℂ`. -/
abbrev cM (M : GapTheta.Mat4) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := M.map (Int.cast : ℤ → ℂ)

theorem cM_mul (M N : GapTheta.Mat4) : cM (M * N) = cM M * cM N := by
  have := Matrix.map_mul (f := Int.castRingHom ℂ) (L := M) (M := N)
  simpa using this

theorem J_map : (Matrix.J (Fin 2) ℤ).map (Int.cast : ℤ → ℂ) = Matrix.J (Fin 2) ℂ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.J, Matrix.one_apply] <;> split_ifs <;> simp

theorem sp_transpose_J {M : GapTheta.Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) :
    (cM M)ᵀ * Matrix.J (Fin 2) ℂ * cM M = Matrix.J (Fin 2) ℂ := by
  have h := (SymplecticGroup.mem_iff').mp hM
  have h2 := congrArg (fun X : GapTheta.Mat4 => cM X) h
  simp only [cM_mul] at h2
  rw [← J_map]
  convert h2 using 2
  · ext i j; rfl

theorem cM_conjTranspose (M : GapTheta.Mat4) : (cM M)ᴴ = (cM M)ᵀ := by
  ext i j; simp [Matrix.conjTranspose_apply]

theorem bil_inv {M : GapTheta.Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) (a b : Fin 2 ⊕ Fin 2 → ℂ) :
    (cM M *ᵥ a) ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ (cM M *ᵥ b)) = a ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ b) := by
  calc (cM M *ᵥ a) ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ (cM M *ᵥ b))
      = a ⬝ᵥ ((cM M)ᵀ *ᵥ (Matrix.J (Fin 2) ℂ *ᵥ (cM M *ᵥ b))) := by
        rw [Matrix.mulVec_transpose, dotProduct_comm (cM M *ᵥ a), Matrix.dotProduct_mulVec, dotProduct_comm]
    _ = a ⬝ᵥ (((cM M)ᵀ * Matrix.J (Fin 2) ℂ * cM M) *ᵥ b) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = a ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ b) := by rw [sp_transpose_J hM]

theorem star_cM_mulVec (M : GapTheta.Mat4) (a : Fin 2 ⊕ Fin 2 → ℂ) : star (cM M *ᵥ a) = cM M *ᵥ star a := by
  rw [Matrix.star_mulVec, cM_conjTranspose, Matrix.vecMul_transpose]

theorem herm_inv {M : GapTheta.Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) (a b : Fin 2 ⊕ Fin 2 → ℂ) :
    star (cM M *ᵥ a) ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ (cM M *ᵥ b)) = star a ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ b) := by
  rw [star_cM_mulVec, bil_inv hM]

/-! ### Block form of `cM M` acting on `(p, q)` -/

theorem cM_mulVec_elim (M : GapTheta.Mat4) (p q : Fin 2 → ℂ) :
    cM M *ᵥ Sum.elim p q = Sum.elim ((cM M).toBlocks₁₁ *ᵥ p + (cM M).toBlocks₁₂ *ᵥ q)
      ((cM M).toBlocks₂₁ *ᵥ p + (cM M).toBlocks₂₂ *ᵥ q) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (cM M)]
  rw [Matrix.fromBlocks_mulVec]
  rfl

theorem J_mulVec_elim (p q : Fin 2 → ℂ) : Matrix.J (Fin 2) ℂ *ᵥ Sum.elim p q = Sum.elim (-q) p := by
  rw [Matrix.J, Matrix.fromBlocks_mulVec]
  simp [Matrix.neg_mulVec]

theorem star_elim (p q : Fin 2 → ℂ) : star (Sum.elim p q) = Sum.elim (star p) (star q) := by
  funext x; cases x <;> rfl

theorem form_elim (p q p' q' : Fin 2 → ℂ) :
    Sum.elim p q ⬝ᵥ (Matrix.J (Fin 2) ℂ *ᵥ Sum.elim p' q') = p ⬝ᵥ (-q') + q ⬝ᵥ p' := by
  rw [J_mulVec_elim, sumElim_dotProduct_sumElim]

/-- `W = AΩ + B`, `X = CΩ + D`. -/
def Wm (M : GapTheta.Mat4) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (cM M).toBlocks₁₁ * Ω + (cM M).toBlocks₁₂
def Xm (M : GapTheta.Mat4) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (cM M).toBlocks₂₁ * Ω + (cM M).toBlocks₂₂

theorem spFactor_eq (M : GapTheta.Mat4) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : PkgI1.spFactor M Ω = (Xm M Ω).det := rfl
theorem spAct_eq (M : GapTheta.Mat4) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : PkgI1.spAct M Ω = Wm M Ω * (Xm M Ω)⁻¹ := rfl

theorem cM_mulVec_u (M : GapTheta.Mat4) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    cM M *ᵥ Sum.elim (Ω *ᵥ v) v = Sum.elim (Wm M Ω *ᵥ v) (Xm M Ω *ᵥ v) := by
  rw [cM_mulVec_elim, Wm, Xm, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- The fundamental identity: `ω((Wv, Xv), (Wv, Xv)) = 2i·v̄ᵀ(Im Ω)v`. -/
theorem key_form {M : GapTheta.Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (hs : Ωᵀ = Ω) (v : Fin 2 → ℂ) :
    star (Wm M Ω *ᵥ v) ⬝ᵥ (-(Xm M Ω *ᵥ v)) + star (Xm M Ω *ᵥ v) ⬝ᵥ (Wm M Ω *ᵥ v) =
      2 * Complex.I * (qIm Ω v : ℂ) := by
  have h := herm_inv hM (Sum.elim (Ω *ᵥ v) v) (Sum.elim (Ω *ᵥ v) v)
  rw [cM_mulVec_u, star_elim, star_elim, form_elim, form_elim] at h
  rw [h, omega_form hs v]

/-- **`det(CΩ + D) ≠ 0` on `𝔥₂` (proved).** -/
theorem spFactor_ne_zero {M : GapTheta.Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) : PkgI1.spFactor M Ω ≠ 0 := by
  intro h0
  rw [spFactor_eq] at h0
  obtain ⟨v, hv, hXv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h := key_form hM hΩ.1 v
  rw [hXv] at h
  simp only [neg_zero, dotProduct_zero, star_zero, zero_dotProduct, add_zero] at h
  have hq := qIm_pos hΩ hv
  have h2 : (qIm Ω v : ℂ) = 0 := by
    have hI : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    exact (mul_eq_zero.mp h.symm).resolve_left hI
  exact hq.ne' (by exact_mod_cast h2)

theorem isUnit_Xm {M : GapTheta.Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) : IsUnit (Xm M Ω).det :=
  isUnit_iff_ne_zero.mpr (spFactor_ne_zero hM hΩ)

/-- `ω` for real `a`: `star(Za)·(−a) + star a·(Za) = 2i·aᵀ(Im Z)a`. -/
theorem real_form (Z : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 2 → ℝ) :
    star (Z *ᵥ (fun i => (a i : ℂ))) ⬝ᵥ (-(fun i => (a i : ℂ))) + star (fun i => (a i : ℂ)) ⬝ᵥ (Z *ᵥ (fun i => (a i : ℂ))) =
      2 * Complex.I * ((star a ⬝ᵥ ((Z.map Complex.im) *ᵥ a) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [dotProduct, mulVec, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- **`Sp₄(ℤ)` preserves `𝔥₂` (proved).** -/
theorem spAct_mem {M : GapTheta.Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) : PkgI1.spAct M Ω ∈ PkgI1.SiegelH2 := by
  have hX := isUnit_Xm hM hΩ
  set W := Wm M Ω
  set X := Xm M Ω
  have hZX : ∀ v, (W * X⁻¹) *ᵥ (X *ᵥ v) = W *ᵥ v := by
    intro v; rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hX, Matrix.mul_one]
  have hXX : ∀ a, X *ᵥ (X⁻¹ *ᵥ a) = a := by
    intro a; rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]
  rw [spAct_eq]
  -- symmetry from the bilinear invariance
  have hbil : ∀ v₁ v₂ : Fin 2 → ℂ, (X *ᵥ v₁) ⬝ᵥ (W *ᵥ v₂) = (W *ᵥ v₁) ⬝ᵥ (X *ᵥ v₂) := by
    intro v₁ v₂
    have h := bil_inv hM (Sum.elim (Ω *ᵥ v₁) v₁) (Sum.elim (Ω *ᵥ v₂) v₂)
    rw [cM_mulVec_u, cM_mulVec_u, form_elim, form_elim] at h
    have hs : v₁ ⬝ᵥ (Ω *ᵥ v₂) = (Ω *ᵥ v₁) ⬝ᵥ v₂ := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hΩ.1]
    rw [dotProduct_neg, dotProduct_neg, hs, neg_add_cancel] at h
    linear_combination h
  have hsym : (W * X⁻¹)ᵀ = W * X⁻¹ := by
    ext i j
    have h := hbil (X⁻¹ *ᵥ Pi.single i 1) (X⁻¹ *ᵥ Pi.single j 1)
    rw [hXX, hXX, ← hZX (X⁻¹ *ᵥ Pi.single i 1), ← hZX (X⁻¹ *ᵥ Pi.single j 1), hXX, hXX] at h
    simp [Matrix.mulVec_single, dotProduct_single, single_dotProduct] at h
    simpa [Matrix.transpose_apply] using h.symm
  refine ⟨hsym, ?_⟩
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun a ha => ?_⟩
  · ext i j
    have := congrFun (congrFun hsym j) i
    simp only [Matrix.transpose_apply] at this
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial]
    exact congrArg Complex.im this.symm
  · set ac : Fin 2 → ℂ := fun i => (a i : ℂ)
    set v := X⁻¹ *ᵥ ac
    have hv : v ≠ 0 := by
      intro h0
      apply ha
      have h1 : ac = 0 := by rw [← hXX ac]; show X *ᵥ v = 0; rw [h0, Matrix.mulVec_zero]
      funext i
      have := congrFun h1 i
      simpa [ac] using this
    have hk := key_form hM hΩ.1 v
    rw [hXX ac, ← hZX v, hXX ac] at hk
    rw [real_form] at hk
    have hI : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    have e := mul_left_cancel₀ hI hk
    have e' : star a ⬝ᵥ ((W * X⁻¹).map Complex.im *ᵥ a) = qIm Ω v := by exact_mod_cast e
    rw [e']
    exact qIm_pos hΩ hv

/-! ### The cocycle `det(C_{NM}Ω + D_{NM}) = det(C_N(MΩ) + D_N)·det(C_MΩ + D_M)` -/

theorem toBlocks₂₁_mul' {R : Type*} [CommRing R] (P Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    (P * Q).toBlocks₂₁ = P.toBlocks₂₁ * Q.toBlocks₁₁ + P.toBlocks₂₂ * Q.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks₂₂_mul' {R : Type*} [CommRing R] (P Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    (P * Q).toBlocks₂₂ = P.toBlocks₂₁ * Q.toBlocks₁₂ + P.toBlocks₂₂ * Q.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

theorem cocycle_aux (P Q W X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X⁻¹ * X = 1) :
    (P * (W * X⁻¹) + Q) * X = P * W + Q * X := by
  rw [Matrix.add_mul, Matrix.mul_assoc P, Matrix.mul_assoc W, hX, Matrix.mul_one]

/-- **The automorphy cocycle (proved).** -/
theorem spFactor_mul (N : GapTheta.Mat4) {M : GapTheta.Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) :
    PkgI1.spFactor (N * M) Ω = PkgI1.spFactor N (PkgI1.spAct M Ω) * PkgI1.spFactor M Ω := by
  have hX := isUnit_Xm hM hΩ
  have hX' : (Xm M Ω)⁻¹ * Xm M Ω = 1 := Matrix.nonsing_inv_mul _ hX
  rw [spFactor_eq, spFactor_eq, spFactor_eq, spAct_eq, ← Matrix.det_mul]
  congr 1
  rw [show Xm N (Wm M Ω * (Xm M Ω)⁻¹) = (cM N).toBlocks₂₁ * (Wm M Ω * (Xm M Ω)⁻¹) + (cM N).toBlocks₂₂ from rfl,
    cocycle_aux _ _ _ _ hX']
  simp only [Xm, Wm, cM_mul, toBlocks₂₁_mul', toBlocks₂₂_mul']
  noncomm_ring

/-! ### Right multiplication on `Γ_∞\Sp₄(ℤ)` -/

theorem botRel_mul {N N' : Matrix.symplecticGroup (Fin 2) ℤ} (h : botRel N N')
    (M : Matrix.symplecticGroup (Fin 2) ℤ) : botRel (N * M) (N' * M) := by
  obtain ⟨U, h1, h2⟩ := h
  refine ⟨U, ?_, ?_⟩
  · show ((N' : GapTheta.Mat4) * (M : GapTheta.Mat4)).toBlocks₂₁ = _ * ((N : GapTheta.Mat4) * (M : GapTheta.Mat4)).toBlocks₂₁
    rw [toBlocks₂₁_mul', toBlocks₂₁_mul', h1, h2, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
  · show ((N' : GapTheta.Mat4) * (M : GapTheta.Mat4)).toBlocks₂₂ = _ * ((N : GapTheta.Mat4) * (M : GapTheta.Mat4)).toBlocks₂₂
    rw [toBlocks₂₂_mul', toBlocks₂₂_mul', h1, h2, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]

def rightAct (M : Matrix.symplecticGroup (Fin 2) ℤ) : SiegelCosets → SiegelCosets :=
  Quotient.map (fun N => N * M) (fun _ _ h => botRel_mul h M)

theorem rightAct_mk (M N : Matrix.symplecticGroup (Fin 2) ℤ) :
    rightAct M (Quotient.mk botSetoid N) = Quotient.mk botSetoid (N * M) := rfl

def rightEquiv (M : Matrix.symplecticGroup (Fin 2) ℤ) : SiegelCosets ≃ SiegelCosets where
  toFun := rightAct M
  invFun := rightAct M⁻¹
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h N => rw [rightAct_mk, rightAct_mk, mul_inv_cancel_right]
  right_inv c := by
    induction c using Quotient.inductionOn with
    | h N => rw [rightAct_mk, rightAct_mk, inv_mul_cancel_right]

/-- The summand does not depend on the coset representative (even weight). -/
theorem spFactor_botRel {N N' : Matrix.symplecticGroup (Fin 2) ℤ} (h : botRel N N')
    (Ω : Matrix (Fin 2) (Fin 2) ℂ) {k : ℕ} (hk : Even k) :
    (PkgI1.spFactor (N' : GapTheta.Mat4) Ω)⁻¹ ^ k = (PkgI1.spFactor (N : GapTheta.Mat4) Ω)⁻¹ ^ k := by
  obtain ⟨U, h1, h2⟩ := h
  have hc : ∀ P : Matrix (Fin 2) (Fin 2) ℤ, (((U : Matrix (Fin 2) (Fin 2) ℤ) * P).map (Int.cast : ℤ → ℂ)) =
      (U : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℂ) * P.map (Int.cast : ℤ → ℂ) := by
    intro P
    have := Matrix.map_mul (f := Int.castRingHom ℂ) (L := (U : Matrix (Fin 2) (Fin 2) ℤ)) (M := P)
    simpa using this
  have hX : Xm (N' : GapTheta.Mat4) Ω = (U : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℂ) * Xm (N : GapTheta.Mat4) Ω := by
    have e1 : (cM (N' : GapTheta.Mat4)).toBlocks₂₁ = ((N' : GapTheta.Mat4).toBlocks₂₁).map (Int.cast : ℤ → ℂ) := rfl
    have e2 : (cM (N' : GapTheta.Mat4)).toBlocks₂₂ = ((N' : GapTheta.Mat4).toBlocks₂₂).map (Int.cast : ℤ → ℂ) := rfl
    have e3 : (cM (N : GapTheta.Mat4)).toBlocks₂₁ = ((N : GapTheta.Mat4).toBlocks₂₁).map (Int.cast : ℤ → ℂ) := rfl
    have e4 : (cM (N : GapTheta.Mat4)).toBlocks₂₂ = ((N : GapTheta.Mat4).toBlocks₂₂).map (Int.cast : ℤ → ℂ) := rfl
    simp only [Xm, e1, e2, e3, e4, h1, h2, hc, Matrix.mul_add, Matrix.mul_assoc]
  have hdet : ((U : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℂ)).det =
      (((U : Matrix (Fin 2) (Fin 2) ℤ).det : ℤ) : ℂ) := by
    have := (Int.castRingHom ℂ).map_det (U : Matrix (Fin 2) (Fin 2) ℤ)
    simpa using this.symm
  have hu : IsUnit (U : Matrix (Fin 2) (Fin 2) ℤ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp U.isUnit
  rw [spFactor_eq, spFactor_eq, hX, Matrix.det_mul, hdet, mul_inv, mul_pow]
  rcases Int.isUnit_iff.mp hu with h | h <;> rw [h] <;> simp [hk.neg_one_pow]

/-- **Modularity of the Siegel Eisenstein series (proved, no convergence needed).** For `M ∈ Sp₄(ℤ)`, `Ω ∈ 𝔥₂` and
even `k`: `ψ_k(M·Ω) = det(CΩ + D)^k ψ_k(Ω)`. The proof reindexes the `tsum` by the bijection `c ↦ c·M` of
`Γ_∞\Sp₄(ℤ)` and uses the cocycle; it holds for the `tsum` whether or not the series converges. -/
theorem siegelEis_modular {M : GapTheta.Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) {k : ℕ} (hk : Even k) :
    siegelEis k (PkgI1.spAct M Ω) = PkgI1.spFactor M Ω ^ k * siegelEis k Ω := by
  set Ms : Matrix.symplecticGroup (Fin 2) ℤ := ⟨M, hM⟩
  have hj : PkgI1.spFactor M Ω ≠ 0 := spFactor_ne_zero hM hΩ
  have step : ∀ c : SiegelCosets,
      (PkgI1.spFactor ((Quotient.out c : Matrix.symplecticGroup (Fin 2) ℤ) : GapTheta.Mat4) (PkgI1.spAct M Ω))⁻¹ ^ k =
        PkgI1.spFactor M Ω ^ k *
          (PkgI1.spFactor ((Quotient.out (rightEquiv Ms c) : Matrix.symplecticGroup (Fin 2) ℤ) : GapTheta.Mat4) Ω)⁻¹ ^ k := by
    intro c
    have h1 : PkgI1.spFactor (((Quotient.out c * Ms : Matrix.symplecticGroup (Fin 2) ℤ)) : GapTheta.Mat4) Ω =
        PkgI1.spFactor ((Quotient.out c : Matrix.symplecticGroup (Fin 2) ℤ) : GapTheta.Mat4) (PkgI1.spAct M Ω) *
          PkgI1.spFactor M Ω :=
      spFactor_mul _ hM hΩ
    have hrel : botRel (Quotient.out (rightEquiv Ms c)) (Quotient.out c * Ms) := by
      have e : rightEquiv Ms c = Quotient.mk botSetoid (Quotient.out c * Ms) := by
        conv_lhs => rw [← Quotient.out_eq c]
        rfl
      rw [e]
      exact Quotient.mk_out (s := botSetoid) _
    rw [← spFactor_botRel hrel Ω hk, h1, mul_inv, mul_pow, inv_pow (PkgI1.spFactor M Ω)]
    field_simp
  unfold siegelEis
  rw [tsum_congr step, tsum_mul_left]
  congr 1
  exact (rightEquiv Ms).tsum_eq
    (fun c => (PkgI1.spFactor ((Quotient.out c : Matrix.symplecticGroup (Fin 2) ℤ) : GapTheta.Mat4) Ω)⁻¹ ^ k)


/-- Igusa's `χ₁₀` (a combination of Eisenstein series) is modular of weight 10. -/
theorem igusaChi10E_modular {M : GapTheta.Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) :
    igusaChi10E (PkgI1.spAct M Ω) = PkgI1.spFactor M Ω ^ 10 * igusaChi10E Ω := by
  unfold igusaChi10E
  rw [siegelEis_modular hM hΩ (k := 4) ⟨2, rfl⟩, siegelEis_modular hM hΩ (k := 6) ⟨3, rfl⟩,
    siegelEis_modular hM hΩ (k := 10) ⟨5, rfl⟩]
  ring

end HDec.HSyn.G0Split.ThetaPt.LinYangPrinted
