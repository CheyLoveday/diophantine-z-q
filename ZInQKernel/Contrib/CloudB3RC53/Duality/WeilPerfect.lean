import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Duality area: the Weil pairing `E[m] × E[m] → μ_m` is perfect

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`, tex L2797–2803: "The Weil
pairing gives the following `R_i`-linear perfect pairing". Over the coefficients `ℤ/m` this is the
perfectness of the Weil pairing `e_m : E[m] × E[m] → μ_m` itself: both adjoints
`E[m] → Hom(E[m], μ_m)` are bijective (`weilPairing_perfect`).

Proof: `e_m` is nondegenerate (`WeierstrassCurve.torsionCoeffWeilPairing_nondegenerate`) and
alternating, so both adjoints are injective; and `#Hom(T, μ_m) ≤ #T` for a finite abelian group
`T`, since `μ_m ≃ ℤ/m` embeds in `ℂˣ` and a finite abelian group has at most `#T` complex
characters (`AddChar.card_addChar_le`).

**Classification.** GLUE, PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Duality

open TauCeti

/-- A finite abelian group `T` has at most `#T` homomorphisms to `ℤ/n`. -/
theorem natCard_addMonoidHom_zmod_le (T : Type*) [AddCommGroup T] [Finite T] (n : ℕ) [NeZero n] :
    Nat.card (T →+ ZMod n) ≤ Nat.card T := by
  have hinj : Function.Injective
      (fun f : T →+ ZMod n => (ZMod.stdAddChar : AddChar (ZMod n) ℂ).compAddMonoidHom f) := by
    intro f g hfg
    ext t
    have := congrArg (fun ψ : AddChar T ℂ => ψ t) hfg
    exact ZMod.injective_stdAddChar this
  have := Fintype.ofFinite T
  calc Nat.card (T →+ ZMod n) ≤ Nat.card (AddChar T ℂ) := Nat.card_le_card_of_injective _ hinj
    _ = Fintype.card (AddChar T ℂ) := Nat.card_eq_fintype_card
    _ ≤ Fintype.card T := AddChar.card_addChar_le T ℂ
    _ = Nat.card T := Nat.card_eq_fintype_card.symm

theorem finite_addMonoidHom (T M : Type*) [AddCommGroup T] [AddCommGroup M] [Finite T]
    [Finite M] : Finite (T →+ M) :=
  Finite.of_injective (fun f : T →+ M => (f : T → M)) DFunLike.coe_injective

section Weil

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ)
  (hm : IsUnit (m : K))

/-- The Weil pairing is skew: `e_m(P, Q) = -e_m(Q, P)`. -/
theorem weilPairing_skew (P Q : W.TorsionCoeff m) :
    W.torsionCoeffWeilPairing m hm P Q = -W.torsionCoeffWeilPairing m hm Q P := by
  have h := W.torsionCoeffWeilPairing_self m hm (P + Q)
  simp only [map_add, AddMonoidHom.add_apply, W.torsionCoeffWeilPairing_self, zero_add,
    add_zero] at h
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h

include hm in
theorem natCard_hom_kummerCoeff_le :
    Nat.card (W.TorsionCoeff m →+ KummerCoeff K m) ≤ Nat.card (W.TorsionCoeff m) := by
  have : NeZero (m : K) := ⟨hm.ne_zero⟩
  have : NeZero m := NeZero.of_neZero_natCast K
  have e := kummerCoeffAddEquivZMod hm
  calc Nat.card (W.TorsionCoeff m →+ KummerCoeff K m)
      = Nat.card (W.TorsionCoeff m →+ ZMod m) :=
        Nat.card_congr (AddEquiv.addMonoidHomCongrRight e).toEquiv
    _ ≤ _ := natCard_addMonoidHom_zmod_le _ m

/-- **The Weil pairing `e_m : E[m] × E[m] → μ_m` is perfect**: both adjoints
`E[m] → Hom(E[m], μ_m)` are bijective. -/
theorem weilPairing_perfect :
    Function.Bijective (W.torsionCoeffWeilPairing m hm) ∧
      Function.Bijective (W.torsionCoeffWeilPairing m hm).flip := by
  have : NeZero (m : K) := ⟨hm.ne_zero⟩
  have : NeZero m := NeZero.of_neZero_natCast K
  have : Finite (KummerCoeff K m) := by
    have e := kummerCoeffAddEquivZMod hm
    exact Finite.of_equiv _ e.symm.toEquiv
  have := finite_addMonoidHom (W.TorsionCoeff m) (KummerCoeff K m)
  have hinj : Function.Injective (W.torsionCoeffWeilPairing m hm) := by
    intro P P' h
    have h0 : ∀ Q, W.torsionCoeffWeilPairing m hm (P - P') Q = 0 := fun Q => by
      rw [map_sub, AddMonoidHom.sub_apply, h, sub_self]
    exact sub_eq_zero.mp (W.torsionCoeffWeilPairing_nondegenerate m hm h0)
  have hinj' : Function.Injective (W.torsionCoeffWeilPairing m hm).flip := by
    intro Q Q' h
    have h0 : ∀ P, W.torsionCoeffWeilPairing m hm (Q - Q') P = 0 := fun P => by
      have := congrArg (fun f => f P) h
      simp only [AddMonoidHom.flip_apply] at this
      rw [weilPairing_skew W m hm, map_sub, this, sub_self, neg_zero]
    exact sub_eq_zero.mp (W.torsionCoeffWeilPairing_nondegenerate m hm h0)
  exact ⟨hinj.bijective_of_nat_card_le (natCard_hom_kummerCoeff_le W m hm),
    hinj'.bijective_of_nat_card_le (natCard_hom_kummerCoeff_le W m hm)⟩

end Weil

end ZInQ.Contrib.CloudB3RC53.Duality
