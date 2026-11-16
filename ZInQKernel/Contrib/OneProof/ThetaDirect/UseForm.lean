import ZInQKernel.OneProof.H.TailZ19

/-! # theta-direct (helper 1/5): the use form `ThetaRatiosAtQM` (copied verbatim)

Copied verbatim from origin/wip/theta-fold (8e3dbdea) `ZInQKernel/OneProof/H/TailK.lean` lines 283-346
(theta-split's `ThetaRatiosAtQM`, `Jmap_ne_zero`, `thetaPointOfFibre_of_qm_atQM`; scratch/theta-split/ThetaUse.lean §1).
They are not on this base (fork main a40d5c4d): theta-fold moved them into TailK, which this task does not edit.
The enclosing `namespace HDec`, `set_option maxHeartbeats 1000000`, `noncomputable section`, `namespace HSyn` and
`open CategoryTheory AlgebraicGeometry G0Split` are those of TailK at that point (its lines 7, 9, 29, 31, 33). -/

namespace HDec

set_option maxHeartbeats 1000000

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry G0Split

theta-split's `ThetaRatiosAtQM` (scratch/theta-split/ThetaUse.lean §1, via igusa-alg and linyang-printed) is how
`gluePieces_of_open4` uses the theta algebraicity: only along pkg-I1's QM period matrices `Ω(τ)`. igusa-alg and
linyang-printed prove it from the printed leaves `IgusaThetaExpressions` and `LinYangEx29All` (with `QMHauptmodul`;
`ZInQKernel/Contrib/OneProof/LinYangPrinted.lean`), which replace the universal field `thetaRatiosAlgebraic`. -/

namespace G0Split.ThetaPt.ThetaSplit

open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open _root_.ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst
  absLogHeight)
open Complex Polynomial

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

end G0Split.ThetaPt.ThetaSplit

end HSyn

end

end HDec
