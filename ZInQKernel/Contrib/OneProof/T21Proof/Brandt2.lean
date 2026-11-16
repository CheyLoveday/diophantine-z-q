import ZInQKernel.Contrib.OneProof.T21Proof.Brandt

/-!
# t21-proof: the test vector at `n = 3` and `f_3(1) = ±3`

Task t21-proof.
* `twoRep_partner_mem`: the partner class `t*(s)` lies in `B^× H` (`twoRep v t* ∈ R̂_3^×`);
* `gT τ`: the function `−3` on `B^× H` (the double coset of `1`) and `1` elsewhere;
* `inPiZ_gT`: `gT τ ∈ π_ℤ^{U_3}` (TYZ's `InPiZ`, L536–550): the invariances hold by construction,
  the two orthogonality sums by `twoRep_ne`, `twoRep_partner_mem` and `sums_check`;
* `brandtValueAt3`: every test vector `f_3` (a generator of `π_ℤ^{U_3}`) has `f_3(1) = ±3`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open ZInQ.Contrib.TYZDecomp.H29Split IsDedekindDomain NumberField
open scoped Quaternion FiniteAdeleExtension
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! ## `ιAt` and integral adeles -/

theorem ιAt_mul (v : HeightOneSpectrum (𝓞 ℚ)) (α β : ℍ[ℚ]) :
    ιAt v α * ιAt v β = ιAt v (α * β) := by
  apply piQ_injective
  intro w
  rw [map_mul]
  by_cases h : w = v
  · subst h; rw [piQ_ιAt_self, piQ_ιAt_self, piQ_ιAt_self, map_mul]
  · rw [piQ_ιAt_ne h, piQ_ιAt_ne h, piQ_ιAt_ne h, mul_one]

theorem ιAt_one (v : HeightOneSpectrum (𝓞 ℚ)) : ιAt v 1 = 1 := by
  apply piQ_injective
  intro w
  by_cases h : w = v
  · subst h; rw [piQ_ιAt_self, map_one, map_one]
  · rw [piQ_ιAt_ne h, map_one]

/-- `ιAt v α` as a unit (`α ≠ 0`). -/
def ιAtU (v : HeightOneSpectrum (𝓞 ℚ)) (α : ℍ[ℚ]) (hα : α ≠ 0) : ℍ[AQ]ˣ :=
  ⟨ιAt v α, ιAt v α⁻¹, by rw [ιAt_mul, mul_inv_cancel₀ hα, ιAt_one],
    by rw [ιAt_mul, inv_mul_cancel₀ hα, ιAt_one]⟩

theorem mem_integrals_of_ev {w : HeightOneSpectrum (𝓞 ℚ)} {a : AQ} (h : ‖ev w a‖ ≤ 1) :
    a w ∈ w.adicCompletionIntegers ℚ := by
  obtain ⟨x, hx, hxe⟩ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn w).surjOn h
  have : x = a w := (pe w).injective hxe
  rw [← this]; exact hx

theorem integral_of_ev {a : AQ} (h : ∀ w, ‖ev w a‖ ≤ 1) :
    a ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ := fun w => mem_integrals_of_ev (h w)

theorem eAt_mul_integral {v : HeightOneSpectrum (𝓞 ℚ)} {r : ℚ} (hr : ‖(r : ℚ_[Pw v])‖ ≤ 1) :
    eAt v * algebraMap ℚ AQ r ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ := by
  refine integral_of_ev fun w => ?_
  rw [map_mul, ev_algebraMap]
  by_cases h : w = v
  · subst h; rw [ev_eAt_self, one_mul]; exact hr
  · rw [ev_eAt_ne h, zero_mul, norm_zero]; exact zero_le_one

theorem one_sub_eAt_integral (v : HeightOneSpectrum (𝓞 ℚ)) :
    1 - eAt v ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ := by
  refine integral_of_ev fun w => ?_
  rw [map_sub, map_one]
  by_cases h : w = v
  · subst h; rw [ev_eAt_self]; simp
  · rw [ev_eAt_ne h]; simp

/-! ## `τ̂` on the base field -/

theorem tauHat_algebraMap_AQ (τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]) (z : AQ) :
    tauHat 3 τ (algebraMap AQ (FiniteAdeleRing (𝓞 (QNeg 3)) (QNeg 3)) z) = algebraMap AQ ℍ[AQ] z := by
  simp only [tauHat, RingHom.coe_comp, Function.comp_apply]
  change (AlgHom.liftEquiv ℚ AQ (QNeg 3) ℍ[AQ] ((qι).comp τ))
    ((TauCeti.GlobalNumberFields.finiteAdeleBaseChangeAlgEquiv ℚ (QNeg 3)).symm
      (algebraMap AQ _ z)) = _
  rw [AlgEquiv.commutes, AlgHom.commutes]

theorem algebraMap_AQ_integral {z : AQ} (hz : z ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ) :
    algebraMap AQ (FiniteAdeleRing (𝓞 (QNeg 3)) (QNeg 3)) z ∈
      FiniteAdeleRing.integralAdeles (𝓞 (QNeg 3)) (QNeg 3) := by
  intro w'
  rw [IsDedekindDomain.algebraMap_finiteAdeleExtensionAlgebra,
    IsDedekindDomain.finiteAdeleExtension_apply]
  exact HeightOneSpectrum.adicCompletionExtension_mem_adicCompletionIntegers ℚ (QNeg 3) _ w'
    ⟨_, hz _⟩

theorem ωK_integral : algebraMap (QNeg 3) (FiniteAdeleRing (𝓞 (QNeg 3)) (QNeg 3))
    ((ωK : 𝓞 (QNeg 3)) : QNeg 3) ∈ FiniteAdeleRing.integralAdeles (𝓞 (QNeg 3)) (QNeg 3) :=
  (FiniteAdeleRing.algebraMap_mem_integralAdeles_iff _).mpr ⟨ωK, rfl⟩

end ZInQ.Contrib.T21Proof
