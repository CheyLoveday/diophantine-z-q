import ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalReciprocitySign
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Residue
import ZInQKernel.Contrib.TauCeti.RingTheory.Frobenius
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-! The residue exponent and the cyclotomic unit of geometric reciprocity
on the Weil subgroup at the chosen absolute prime (tex 9784–9785). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine O12 O12Local Polynomial PrintsArith Symbols
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

attribute [local instance] Ideal.Quotient.field

variable {p : ℕ} [Fact p.Prime] (Q : LocalPair p)

private abbrev residueAction :=
  Ideal.Quotient.stabilizerHom Q.Q (Q.Q.under ℤ) GalQ

private abbrev localFrob : DecompositionAt Q :=
  letI := Q.maximal.isPrime
  ⟨Q.φ, Q.frob.mem_stabilizer⟩

private theorem residueFrob_infinite :
    ¬ IsOfFinOrder (residueAction Q (localFrob Q)) := by
  let := Q.maximal
  let v : WitnessSpec.FrobeniusPlace Q.φ p :=
    ⟨Q.Q, Q.maximal.isPrime, under_eq_span_of_isMaximal Q.maximal Fact.out Q.above, by
      intro x y hy
      have h : Q.φ • x - x ^ p = y := by
        apply Subtype.ext
        push_cast
        exact hy.symm
      rw [← h]
      have hF := Q.frob x
      change Q.φ • x - x ^ Nat.card (ℤ ⧸ Q.Q.under ℤ) ∈ Q.Q at hF
      rwa [card_quot_under_of_isMaximal Q.maximal (Fact.out : p.Prime) Q.above] at hF⟩
  let : IsAlgClosed (Zbar ⧸ Q.Q) := v.isAlgClosed_residue
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, he⟩
  have hall (x : Zbar ⧸ Q.Q) : x ^ p ^ n = x := by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    have e := congrArg (fun a => a (Ideal.Quotient.mk Q.Q t)) he
    rw [← map_pow] at e
    change Ideal.Quotient.mk Q.Q ((Q.φ ^ n) • t) = Ideal.Quotient.mk Q.Q t at e
    simpa only [Q.frob.mk_pow_smul, card_quot_under_of_isMaximal Q.maximal
      (Fact.out : p.Prime) Q.above] using e
  have hne : p ^ n ≠ 1 :=
    (one_lt_pow₀ (Fact.out : p.Prime).one_lt hn.ne').ne'
  have hpoly : (Polynomial.X ^ (p ^ n) : (Zbar ⧸ Q.Q)[X]) - Polynomial.X = 0 := by
    apply Polynomial.funext
    intro x
    simp [hall x]
  have hc := congrArg (fun f : (Zbar ⧸ Q.Q)[X] => f.coeff 1) hpoly
  simp [Polynomial.coeff_X_pow, Ne.symm hne] at hc

private abbrev residueActionWeil :=
  (residueAction Q).comp (Subgroup.inclusion (weilAt_le_decomposition Q))

omit [Fact p.Prime] in
private theorem residueAction_inertia (w : weilAt Q) (hw : (w : GalQ) ∈ Q.Q.inertia GalQ) :
    residueActionWeil Q w = 1 := by
  ext x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.Quotient.eq.mpr (hw t)

private def residueExponentData :
    { exp : weilAt Q →* Multiplicative ℤ // ∀ w : weilAt Q,
      (residueAction Q (localFrob Q)) ^ (exp w).toAdd = residueActionWeil Q w } := by
  letI := Q.maximal.isPrime
  let a := residueAction Q (localFrob Q)
  let m := zpowersHom _ a
  have hι : Function.Injective m :=
    injective_zpow_iff_not_isOfFinOrder.mpr (residueFrob_infinite Q)
  have hm (w : weilAt Q) : residueActionWeil Q w ∈ m.range := by
    let S := m.range.comap (residueAction Q)
    have hle : weilAt Q ≤ S.map (Subgroup.subtype (DecompositionAt Q)) := by
      apply (Subgroup.closure_le _).2
      rintro g (hg | hg)
      · let w : weilAt Q := ⟨g, Subgroup.subset_closure (Or.inl hg)⟩
        let d : DecompositionAt Q := Subgroup.inclusion (weilAt_le_decomposition Q) w
        refine ⟨d, ?_, rfl⟩
        change residueActionWeil Q w ∈ m.range
        rw [residueAction_inertia Q w hg]
        exact m.range.one_mem
      · have h : g = Q.φ := hg
        subst g
        exact ⟨localFrob Q, ⟨Multiplicative.ofAdd 1, by simp [m, a]⟩, rfl⟩
    obtain ⟨d, hd, he⟩ := hle w.property
    have h : d = Subgroup.inclusion (weilAt_le_decomposition Q) w := Subtype.ext he
    change residueAction Q (Subgroup.inclusion (weilAt_le_decomposition Q) w) ∈ m.range
    rw [← h]
    exact hd
  let lift := (residueActionWeil Q).codRestrict m.range hm
  let e : Multiplicative ℤ ≃* m.range :=
    MulEquiv.ofBijective m.rangeRestrict ⟨fun _ _ h => hι (congrArg Subtype.val h),
      m.rangeRestrict_surjective⟩
  refine ⟨e.symm.toMonoidHom.comp lift, fun w => ?_⟩
  change (e (e.symm (lift w))).val = (lift w).val
  rw [MulEquiv.apply_symm_apply]

private def residueExponentMap : weilAt Q →* Multiplicative ℤ := (residueExponentData Q).val

private theorem residueExponent_spec (w : weilAt Q) :
    (residueAction Q (localFrob Q)) ^ (residueExponentMap Q w).toAdd =
      residueActionWeil Q w := by
  exact (residueExponentData Q).property w

private theorem residueExponent_inertia (w : weilAt Q) (hw : (w : GalQ) ∈ Q.Q.inertia GalQ) :
    residueExponentMap Q w = 1 := by
  apply Multiplicative.toAdd.injective
  apply (injective_zpow_iff_not_isOfFinOrder.mpr (residueFrob_infinite Q))
  change (residueAction Q (localFrob Q)) ^ (residueExponentMap Q w).toAdd =
    (residueAction Q (localFrob Q)) ^ (0 : ℤ)
  rw [residueExponent_spec, residueAction_inertia Q w hw, zpow_zero]

private theorem residueExponent_frob (w : weilAt Q) (hw : (w : GalQ) = Q.φ) :
    residueExponentMap Q w = Multiplicative.ofAdd 1 := by
  apply Multiplicative.toAdd.injective
  apply (injective_zpow_iff_not_isOfFinOrder.mpr (residueFrob_infinite Q))
  change (residueAction Q (localFrob Q)) ^ (residueExponentMap Q w).toAdd =
    (residueAction Q (localFrob Q)) ^ (1 : ℤ)
  rw [residueExponent_spec, zpow_one]
  exact congrArg (residueAction Q) (Subtype.ext hw)

/-- The geometric convention takes a Weil element of residue exponent `n`
to `p^(-n)` times its p-adic cyclotomic unit. These are the valuation and
unit coordinates of the inverse of the arithmetic Artin map. -/
def localWeilReciprocity : ReciprocityAt Q := by
  let χ := (cyclotomicCharacter Qbar p).comp
    (MulSemiringAction.toRingAut GalQ Qbar)
  let unit : weilAt Q →* ℤ_[p]ˣ := χ.comp (weilAt Q).subtype
  let ι : ℤ_[p]ˣ →* ℚ_[p]ˣ := Units.map PadicInt.Coe.ringHom.toMonoidHom
  let m := (zpowersHom _ (uniformizer p)⁻¹).comp (residueExponentMap Q)
  have hunit (w : weilAt Q) : ‖(ι (unit w) : ℚ_[p])‖ = 1 := PadicInt.norm_units _
  refine ⟨m * (ι.comp unit), ?_, ?_⟩
  · intro w hw
    change ‖(m w * ι (unit w) : ℚ_[p]ˣ).val‖ = 1
    simp [m, residueExponent_inertia Q w hw, hunit w]
  · intro w hw
    refine ⟨ι (unit w), hunit w, ?_⟩
    change m w * ι (unit w) = _
    simp [m, residueExponent_frob Q w hw]

theorem localWeilReciprocity_residue : ReciprocityAt.ResidueCyclotomic (localWeilReciprocity Q) := by
  intro w hw ζ hζ
  let c := cyclotomicCharacter Qbar p (w : GalQ).toRingEquiv
  have hu : (localWeilReciprocity Q).toUnits w = Units.map PadicInt.Coe.ringHom.toMonoidHom c := by
    change (uniformizer p)⁻¹ ^ (residueExponentMap Q w).toAdd *
      Units.map PadicInt.Coe.ringHom.toMonoidHom c = _
    simp [residueExponent_inertia Q w hw]
  have hu' : ((localUnitResidue ((localWeilReciprocity Q).toUnits w)
      ((localWeilReciprocity Q).inertia_unit w hw) : (ZMod p)ˣ) : ZMod p) =
      PadicInt.toZMod (c : ℤ_[p]) := by
    change PadicInt.toZMod (PadicInt.mkUnits ((localWeilReciprocity Q).inertia_unit w hw) :
      ℤ_[p]) = PadicInt.toZMod (c : ℤ_[p])
    apply congrArg PadicInt.toZMod
    apply Subtype.ext
    exact congrArg Units.val hu
  let e := ZMod.ringEquivCongr (pow_one p)
  have hred : e.toRingHom.comp (PadicInt.toZModPow (p := p) 1) = PadicInt.toZMod := by
    apply ZMod.ringHom_eq_of_ker_eq
    rw [RingHom.ker_comp_of_injective _ e.injective, PadicInt.ker_toZModPow,
      PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, pow_one]
  have hval : (PadicInt.toZMod c : ZMod p).val = (PadicInt.toZModPow 1 (c : ℤ_[p])).val := by
    rw [← hred, RingHom.comp_apply]
    exact ZMod.ringEquivCongr_val _ _
  rw [hu', hval]
  exact cyclotomicCharacter.spec (L := Qbar) p (n := 1) (w : GalQ).toRingEquiv ζ
    (by simpa only [pow_one] using hζ.pow_eq_one)

end ZInQ.Manuscript.RC.EvenJoin
