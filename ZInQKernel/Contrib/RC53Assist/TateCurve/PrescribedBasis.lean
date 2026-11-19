import ZInQKernel.Contrib.RC53Assist.GlobalTrace.CoinvariantReadings

/-!
# Prescribed bases of an inverse-limit Tate module

Independent prescribed generators at each finite level give a basis of the
inverse limit. Surjectivity follows from compactness, rather than choosing
compatible coordinate lifts. This separates the inverse-limit argument from
the Kummer calculation in a multiplicative uniformization.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, III.7; the pages
have not been checked. All results in this module are proved.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open TauCeti Module

section PrescribedBasis

variable {ℓ : ℕ} [Fact ℓ.Prime] {P : Type*} [AddCommGroup P] {r : ℕ}

/-- **PROVED**: finite-level injectivity becomes finite-level bijectivity
when the torsion has the expected cardinality. Locator: finite cardinality
and `Nat.card_zmod`. -/
theorem level_combination_bijective (e : Fin r → TateModule ℓ P)
    (hcard : ∀ n, Nat.card (TateModuleLevel ℓ P n) = (ℓ ^ n) ^ r)
    (hinj : ∀ n, Function.Injective fun c : Fin r → ZMod (ℓ ^ n) =>
      ∑ i, c i • TateModule.proj n (e i)) (n : ℕ) :
    Function.Bijective fun c : Fin r → ZMod (ℓ ^ n) =>
      ∑ i, c i • TateModule.proj n (e i) := by
  classical
  have : Finite (TateModuleLevel ℓ P n) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero))
  exact (hinj n).bijective_of_nat_card_le (by
    rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin])

/-- **PROVED**: the prescribed generators give an isomorphism
`ℤ_ℓ^r ≃ T_ℓ(P)`. Locator: the finite-level independence hypothesis and
`TateModule.surjective_of_forall_surjective_proj`. -/
def prescribedTateEquiv (e : Fin r → TateModule ℓ P)
    (hcard : ∀ n, Nat.card (TateModuleLevel ℓ P n) = (ℓ ^ n) ^ r)
    (hinj : ∀ n, Function.Injective fun c : Fin r → ZMod (ℓ ^ n) =>
      ∑ i, c i • TateModule.proj n (e i)) :
    (Fin r → ℤ_[ℓ]) ≃ₗ[ℤ_[ℓ]] TateModule ℓ P := by
  classical
  let f := Fintype.linearCombination ℤ_[ℓ] e
  have hf : Function.Injective f := by
    intro c d h
    funext i
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    have hn : (fun j => PadicInt.toZModPow n (c j)) =
        (fun j => PadicInt.toZModPow n (d j)) := by
      apply hinj n
      simpa only [f, Fintype.linearCombination_apply, map_sum,
        TateModule.proj_smul] using congrArg (TateModule.proj n) h
    exact congrFun hn i
  have hc : Continuous f := by
    change Continuous fun c : Fin r → ℤ_[ℓ] => ∑ i, c i • e i
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hs : Function.Surjective f := by
    apply TateModule.surjective_of_forall_surjective_proj hc
    intro n y
    obtain ⟨c, hc⟩ := (level_combination_bijective e hcard hinj n).2 y
    refine ⟨fun i => ((c i).val : ℤ_[ℓ]), ?_⟩
    simpa only [f, Fintype.linearCombination_apply, map_sum,
      TateModule.proj_smul, map_natCast, ZMod.natCast_zmod_val] using hc
  exact LinearEquiv.ofBijective f ⟨hf, hs⟩

/-- **PROVED DEFINITION**: a basis made from the prescribed compatible
finite-level generators. Locator: `prescribedTateEquiv`. -/
def prescribedTateBasis (e : Fin r → TateModule ℓ P)
    (hcard : ∀ n, Nat.card (TateModuleLevel ℓ P n) = (ℓ ^ n) ^ r)
    (hinj : ∀ n, Function.Injective fun c : Fin r → ZMod (ℓ ^ n) =>
      ∑ i, c i • TateModule.proj n (e i)) :
    Basis (Fin r) ℤ_[ℓ] (TateModule ℓ P) :=
  (Pi.basisFun ℤ_[ℓ] (Fin r)).map (prescribedTateEquiv e hcard hinj)

/-- **PROVED**: the constructed basis is exactly the prescribed family,
not an unrelated basis of the same rank. Locator: `Fintype.linearCombination`. -/
theorem prescribedTateBasis_apply (e : Fin r → TateModule ℓ P)
    (hcard : ∀ n, Nat.card (TateModuleLevel ℓ P n) = (ℓ ^ n) ^ r)
    (hinj : ∀ n, Function.Injective fun c : Fin r → ZMod (ℓ ^ n) =>
      ∑ i, c i • TateModule.proj n (e i)) (i : Fin r) :
    prescribedTateBasis e hcard hinj i = e i := by
  classical
  rw [prescribedTateBasis, Basis.map_apply, Pi.basisFun_apply]
  change Fintype.linearCombination ℤ_[ℓ] e (Pi.single i 1) = e i
  rw [Fintype.linearCombination_apply]
  simp

end PrescribedBasis

end ZInQ.Contrib.RC53Assist.TateCurve
