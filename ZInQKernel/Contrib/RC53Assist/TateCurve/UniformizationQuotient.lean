import ZInQKernel.Contrib.RC53Assist.TateCurve.PrintedUniformization

/-!
# The quotient form of Tate uniformization

The surjective homomorphism with kernel `q^ℤ` in the uniformization print
is explicitly converted to the literal quotient-group isomorphism
`Fˣ/q^ℤ ≃ E(F)`. This is the first isomorphism theorem, not an extra
arithmetic hypothesis.

Locator: Silverman, AEC, Appendix C, §14, C.14.1; the quotient conversion
below is proved.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open scoped Classical WithZero

section Quotient

variable {F P : Type*} [Field F] [AddCommGroup P] {q : Fˣ}

/-- **PROVED DEFINITION**: the multiplicative quotient isomorphism
associated to the exact uniformization kernel.
Locator: the first isomorphism theorem for groups. -/
def uniformizationQuotientEquiv (U : MultiplicativeUniformization (P := P) q) :
    Additive (Fˣ ⧸ Subgroup.zpowers q) ≃+ P := by
  let f : Fˣ →* Multiplicative P :=
    { toFun := fun x => Multiplicative.ofAdd (U.map (Additive.ofMul x))
      map_one' := by simp
      map_mul' := fun x y => by simp only [ofMul_mul, map_add, ofAdd_add] }
  have hk : f.ker = Subgroup.zpowers q := by
    ext x
    change U.map (Additive.ofMul x) = 0 ↔ x ∈ Subgroup.zpowers q
    rw [Subgroup.mem_zpowers_iff]
    constructor
    · intro h
      obtain ⟨m, hm⟩ := (U.kernel x).mp h
      exact ⟨m, hm.symm⟩
    · rintro ⟨m, hm⟩
      exact (U.kernel x).mpr ⟨m, hm.symm⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := U.surjective (Multiplicative.toAdd y)
    refine ⟨Additive.toMul x, ?_⟩
    exact congrArg Multiplicative.ofAdd hx
  let e₁ : (Fˣ ⧸ Subgroup.zpowers q) ≃* (Fˣ ⧸ f.ker) :=
    MulEquiv.cast (M := fun H : Subgroup Fˣ => Fˣ ⧸ H) hk.symm
  let e₂ := QuotientGroup.quotientKerEquivOfSurjective f hf
  exact (e₁.trans e₂).toAdditive

end Quotient

section TateQuotient

variable {K : Type*} [Field K] [CharZero K] [Valued K ℤᵐ⁰]

/-- **PROVED DEFINITION**: the literal quotient form of the uniformization
of the Tate curve over the algebraic closure.
Locator: `uniformizationQuotientEquiv` and C.14.1. -/
def EquivariantTateUniformization.quotientEquiv {q : Kˣ}
    (U : EquivariantTateUniformization q) :
    Additive ((AlgebraicClosure K)ˣ ⧸ Subgroup.zpowers (closureParameter q)) ≃+
      ((tateEquation q).baseChange (AlgebraicClosure K)).toAffine.Point :=
  uniformizationQuotientEquiv U.uniformization

end TateQuotient

end ZInQ.Contrib.RC53Assist.TateCurve
