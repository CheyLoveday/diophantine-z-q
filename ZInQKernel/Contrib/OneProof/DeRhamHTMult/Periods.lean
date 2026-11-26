import ZInQKernel.Contrib.OneProof.PanBergerPst
import ZInQKernel.Contrib.OneProof.DeRhamHTMult.TiltValuation
import ZInQKernel.Contrib.OneProof.DeRhamHTMult.CyclotomicAction

/-! # `t = log [ε]` is a uniformizer of `B_dR^+`, and `σ(t) = χ(σ) t`

For a generator `ε` of `ℤ_p(1)` in the tilt (`IsGenEps`) and `t = log [ε] ∈ B_dR^+` (the tree's
`logTeich`):

* `logTeich_irreducible`: `t` is a uniformizer of the discrete valuation ring `B_dR^+`. Modulo
  `(ker θ)²`, `t ≡ y + y² r` with `y = [ε] − 1`, and `y ∉ (ker θ)²` (`[ε] − 1 ∉ (ξ²)`,
  `TiltValuation`), so `irreducible_of_evalTwo` applies.
* `logTeich_flat`, `bdrAct_tOf`: `σ(t) = χ(σ) t`. The proof is the tree's
  `BmaxOne.logTeich_eq_mul` with the exponent identified: `(σ♭ ε)^{(k)} = (ε^{(k)})^{b_k}`,
  `b_k ≡ χ(σ) mod p^k` (`CyclotomicAction`), then `log_decomp` and `amax_sep`.
-/

set_option autoImplicit false

namespace DeRhamHTMult

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.G9.BdrKer.Cp

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- `[ε] − 1` in `W(𝓞_ℂ_p♭)[1/p]`. -/
abbrev yEps (ε : PreTilt 𝓞_ℂ_[p] p) : HDec.PkgI4.PanBergerSplit.AinfP p :=
  algebraMap (HDec.PkgI4.PanBergerSplit.Ainf p) (HDec.PkgI4.PanBergerSplit.AinfP p)
    (WittVector.teichmuller p ε - 1)

/-- `log [ε] ≡ y + y² r (mod (ker θ)²)` with `y = [ε] − 1`. -/
theorem evalTwo_logTeich {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) :
    ∃ r, AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) 2
        (HDec.PkgI4.BergerBst.logTeich p h) =
      Ideal.Quotient.mk _ (yEps p ε + yEps p ε ^ 2 * r) := by
  obtain ⟨R, hR⟩ := HDec.PkgI4.BergerBst.trunc_logSeries_sub_X p 0
  refine ⟨R.eval (yEps p ε), ?_⟩
  have e : (PowerSeries.trunc (0 + 2) (HDec.PkgI4.BergerBst.logSeries p)).eval (yEps p ε) =
      yEps p ε + yEps p ε ^ 2 * R.eval (yEps p ε) := by
    have := congrArg (Polynomial.eval (yEps p ε)) hR
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X] at this
    linear_combination this
  rw [← e]
  exact HDec.PkgI4.BergerBst.evalₐ_psEval _ (HDec.PkgI4.BergerBst.teich_sub_one_mem p h) _ 2

theorem yEps_not_mem_sq {ε : PreTilt 𝓞_ℂ_[p] p} (h1 : PreTilt.untilt ε = 1)
    (h2 : root ε 1 ≠ 1) :
    yEps p ε ∉ RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p) ^ 2 := by
  intro hmem
  rw [ker_fontaineThetaInvertP_Cp, Ideal.span_singleton_pow] at hmem
  have hmem' : yEps p ε ∈ Ideal.span {algebraMap (HDec.PkgI4.PanBergerSplit.Ainf p)
      (HDec.PkgI4.PanBergerSplit.AinfP p) (xi p) ^ 2} := hmem
  exact teich_sub_one_not_mem_span_xi_sq h1 h2
    (HDec.PkgI4.BergerBst.mem_xi_pow_of_algebraMap p 2 _ hmem')

/-- **`t = log [ε]` is a uniformizer of `B_dR^+`.** -/
theorem logTeich_irreducible {ε : PreTilt 𝓞_ℂ_[p] p} (h : HDec.PkgI4.BmaxOne.IsGenEps p ε) :
    Irreducible (HDec.PkgI4.BergerBst.logTeich p h.1) := by
  obtain ⟨r, hr⟩ := evalTwo_logTeich p h.1
  exact irreducible_of_evalTwo p _
    (HDec.PkgI4.BergerBst.logTeich_ne_zero p h.1 (HDec.PkgI4.BmaxOne.ne_one_of_isGenEps p h))
    (yEps p ε) r (HDec.PkgI4.BergerBst.teich_sub_one_mem p h.1) (yEps_not_mem_sq p h.1 h.2) hr

/-- **`log [σ♭ ε] = χ(σ) log [ε]`** in `B_dR^+`. -/
theorem logTeich_flat {ε : PreTilt 𝓞_ℂ_[p] p} (h : HDec.PkgI4.BmaxOne.IsGenEps p ε) (σ : GQp p)
    (hε : PreTilt.untilt (HDec.PkgI4.PanBergerSplit.flatAct p σ ε) = 1) :
    HDec.PkgI4.BergerBst.logTeich p hε =
      HDec.PkgI4.BmaxOne.zpB p (cyc p σ : ℤ_[p]) * HDec.PkgI4.BergerBst.logTeich p h.1 := by
  refine sub_eq_zero.mp (HDec.PkgI4.BmaxOne.amax_sep p _ fun k => ?_)
  obtain ⟨z, hz, hlog⟩ := HDec.PkgI4.BmaxOne.log_decomp p h hε k _ (val_le p _ k)
    (root_flat_eq_pow p σ h.1 k).symm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (sub_val_mem p (cyc p σ : ℤ_[p]) k)
  have hac : (cyc p σ : ℤ_[p]) =
      ((PadicInt.toZModPow k (cyc p σ : ℤ_[p])).val : ℤ_[p]) + c * (p : ℤ_[p]) ^ k := by
    linear_combination -hc
  refine ⟨z - HDec.PkgI4.BmaxOne.zpB p c * HDec.PkgI4.BergerBst.logTeich p h.1,
    Subring.sub_mem _ hz (Subring.mul_mem _ (HDec.PkgI4.BmaxOne.zpB_mem p c)
      (HDec.PkgI4.BergerBst.logTeich_mem_amax p h.1)), ?_⟩
  rw [hlog, hac, map_add, map_mul, map_pow, map_natCast, map_natCast]
  ring

/-- **`σ(t) = χ(σ) t`** in `B_dR`, `t = log [ε]`. -/
theorem bdrAct_tOf {ε : PreTilt 𝓞_ℂ_[p] p} (h : HDec.PkgI4.BmaxOne.IsGenEps p ε) (σ : GQp p) :
    bdrAct p σ (HDec.PkgI4.BmaxOne.tOf p h) =
      algebraMap ℚ_[p] (BdR p) (cycPow p σ 1) * HDec.PkgI4.BmaxOne.tOf p h := by
  unfold HDec.PkgI4.BmaxOne.tOf
  rw [HDec.PkgI4.BergerBst.bdrAct_logTeich, logTeich_flat p h σ, map_mul,
    HDec.PkgI4.BmaxOne.toBdR_zpB]
  congr 2
  simp only [cycPow, zpow_one]
  rfl

theorem tOf_ne_zero {ε : PreTilt 𝓞_ℂ_[p] p} (h : HDec.PkgI4.BmaxOne.IsGenEps p ε) :
    HDec.PkgI4.BmaxOne.tOf p h ≠ 0 := fun h0 =>
  HDec.PkgI4.BergerBst.logTeich_ne_zero p h.1 (HDec.PkgI4.BmaxOne.ne_one_of_isGenEps p h)
    ((HDec.PkgI4.BergerBst.toBdR_injective p) (h0.trans (map_zero _).symm))

/-- `t` as a unit of the field `B_dR`. -/
def tUnit {ε : PreTilt 𝓞_ℂ_[p] p} (h : HDec.PkgI4.BmaxOne.IsGenEps p ε) : (BdR p)ˣ :=
  Units.mkOfMulEqOne _ _
    (Classical.choose_spec ((BdrKer.Cp.isField_BDeRham p).mul_inv_cancel (tOf_ne_zero p h)))

theorem tUnit_val {ε : PreTilt 𝓞_ℂ_[p] p} (h : HDec.PkgI4.BmaxOne.IsGenEps p ε) :
    (tUnit p h : BdR p) = HDec.PkgI4.BmaxOne.tOf p h := rfl

end

end DeRhamHTMult
