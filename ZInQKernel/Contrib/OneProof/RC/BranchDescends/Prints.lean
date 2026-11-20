import ZInQKernel.Contrib.OneProof.RC.CMScope.Field

/-! The value form of the CM input for tex 2915–2916. -/

open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
  ZInQ.Contrib.CloudB3RC53.CST

namespace ZInQ.Manuscript.RC.BranchDescends

/-- **Printed-form leaf, GLUE (unread).** For an oriented Heegner form in
the scope of tex 2839–2844 and 2915–2916, every modular function in
`ℚ(j, j_N)` finite at its CM parameter has value in the associated ring
class field, with one complex embedding for all the values at that parameter.
The finite-germ condition excludes poles, not vanishing denominators of
individual presentations of the function.

Candidate sources: Shimura, *Introduction to the Arithmetic Theory of
Automorphic Functions* (1971), Ch. 6, Thm. 6.31 and subsequent CM results
(UNVERIFIED); Gross, *Heegner points on X₀(N)* (1984), §1 (UNVERIFIED).
The conductor is explicitly prime to the level (in fact to `2N |D_K|`).
The locators, coefficient field, and coverage of nonmaximal orders need
a page check. No action of the class group or norm relation is assumed. -/
def HeegnerValuesInRingClassField (N : ℕ) [NeZero N] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K →
    (∀ p : ℕ, p.Prime → p ∣ 2 * N → SplitsIn K p) →
    discr K ≠ -4 → discr K ≠ -3 →
    ∀ (β : ℤ), Int.ModEq (4 * (N : ℤ)) (β ^ 2) (discr K) →
    ∀ (c : ℕ) [NeZero c], Nat.Coprime c (2 * N * (discr K).natAbs) →
    ∀ (d A B C : ℤ), (conductorOrder K c).discr = d → d < 0 →
      IsCoprime d (N : ℤ) → IsHeegnerForm N d A B C →
      Int.ModEq (2 * (N : ℤ)) B ((c : ℤ) * β) →
      let H := ringClassField (conductorOrder K c)
      let τ := cmPoint A B d
      ∃ ι : H →ₐ[ℚ] ℂ, ∀ (g : ModularCurve.modularFunctionField N)
        (s : X0Model.meromorphicValuation (τ : ℂ)),
        s.val = X0Model.fieldGerm N τ g →
        X0Model.valueOfGerm (τ : ℂ) s ∈ Set.range ι

end ZInQ.Manuscript.RC.BranchDescends
