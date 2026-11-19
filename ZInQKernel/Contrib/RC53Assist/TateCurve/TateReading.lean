import ZInQKernel.Contrib.RC53Assist.TateCurve.FrobeniusSign
import ZInQKernel.Contrib.RC53Assist.TateCurve.WeilInertia
import ZInQKernel.Contrib.RC53Assist.TateCurve.RootSystems
import ZInQKernel.Contrib.RC53Assist.TateCurve.Cocycle

/-!
# The retained Tate-module reading from literal uniformization

The basis is constructed from compatible roots of unity and roots of the
Tate parameter. The quadratic sign is derived from an actual Weierstrass
isomorphism. Unipotence at multiplicative reduction forces that sign to be
unramified. The cyclotomic coefficient is one on inertia by the proved
root-of-unity reduction argument. The Kummer coefficient is nonzero on
inertia by the unramified value-group theorem. Frobenius reads the sign of
the splitting extension through its procyclic unramified quotient.

Inputs: Silverman AEC, Appendix C, §14, Theorem C.14.1;
Silverberg-Zarhin, *Reduction of Abelian Varieties*, arXiv:alg-geom/9602014v2,
Theorem 4.1, PDF page 4 (text body read), referring to SGA 7 I, IX,
Proposition 3.5 and Corollaire 3.8; Serre, *Local Fields*, I, §8 and III, §5.
The Silverman pages have been checked (Theorem 14.1, page 445); the Serre and original SGA
pages have not. The printed existence form of Tate's theorem is used in `LiteralTate.lean`.
No basis, cocycle formula, inertia reading, or Frobenius sign is an input.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open Module TauCeti WeierstrassCurve
open ZInQ.Contrib.RC53Assist.GlobalTrace
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open scoped Classical WithZero

/-- **PROVED FROM C.14.1**: its parameter and uniformization specialized
to the actual completion used by the retained target. The unique-parameter
clause remains in the print; only existence is needed here.
Locator: `multiplicative_j_nonintegral` and `SilvermanC141TateUniformizationPrint`. -/
theorem exists_local_tate_parameter (hT : SilvermanC141TateUniformizationPrint)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) (hp : p.Prime)
    (hM : ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ)) :
    ∃ q : ((primeIdealQ p hp).adicCompletion ℚ)ˣ,
      ∃ hqE : (tateEquation q).IsElliptic, letI := hqE;
      Valued.v (q : (primeIdealQ p hp).adicCompletion ℚ) < 1 ∧
      (tateEquation q).j = (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).j ∧
      Nonempty (EquivariantTateUniformization q) ∧
      ((∃ A : VariableChange ((primeIdealQ p hp).adicCompletion ℚ),
          A • E.baseChange ((primeIdealQ p hp).adicCompletion ℚ) = tateEquation q) ↔
        ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
          ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasSplitMultiplicativeReduction
            ((primeIdealQ p hp).adicCompletionIntegers ℚ)) := by
  let K := (primeIdealQ p hp).adicCompletion ℚ
  letI : Finite (IsLocalRing.ResidueField (Valued.v.valuationSubring : ValuationSubring K)) :=
    Nat.finite_of_card_ne_zero (by
      change Nat.card (IsLocalRing.ResidueField
        ((primeIdealQ p hp).adicCompletionIntegers ℚ)) ≠ 0
      rw [card_residueField_primeIdealQ p hp]
      exact hp.ne_zero)
  obtain ⟨q, hq, _⟩ := (hT K).2 (E.baseChange K)
    (multiplicative_j_nonintegral (E.baseChange K) hM)
  obtain ⟨hqE, hq⟩ := hq
  letI := hqE
  obtain ⟨had, hj, hsplit⟩ := hq
  obtain ⟨_, hU⟩ := (hT K).1 q had
  exact ⟨q, hqE, had, hj, hU, hsplit⟩

end ZInQ.Contrib.RC53Assist.TateCurve

namespace ZInQ.Contrib.RC53Assist.GlobalTrace

open Module TauCeti WeierstrassCurve
open ZInQ.Contrib.RC53Assist.TateCurve
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open scoped Classical WithZero

/-- **PROVED FROM THE NAMED PRINTED THEOREMS**: the exact retained
`TateCurveTateModulePrint`. The additional sources are independent local
field and semistability theorems, not equivalent Tate-module readings.
The Kummer basis, both Galois columns, both inertia character readings,
nonzero Kummer inertia, and the arithmetic Frobenius sign are derived.
Locators: C.14.1; Silverberg-Zarhin, *Reduction of Abelian Varieties*, Theorem 4.1 (SGA 7 I, IX,
Proposition 3.5 and Corollaire 3.8); Serre, *Local Fields*, I, §8 and III, §5. -/
theorem tateCurveTateModulePrint_of_literature
    (hT : SilvermanC141TateUniformizationPrint)
    (hS : LocalSemistableTatePrint) (hV : LocalUnramifiedValueGroupPrint)
    (hF : LocalFrobeniusGenerationPrint) : TateCurveTateModulePrint := by
  classical
  intro E _ p hp ℓ _ hℓp hM Γ _ w hw
  let K := (primeIdealQ p hp).adicCompletion ℚ
  let F := AlgebraicClosure K
  let W := E.baseChange K
  letI : W.IsElliptic := by dsimp [W]; infer_instance
  obtain ⟨q, hqE, hq⟩ := exists_local_tate_parameter hT E p hp hM
  letI := hqE
  obtain ⟨had, hj, ⟨Uq⟩, hsplit⟩ := hq
  let E' := tateEquation q
  letI : E'.IsElliptic := hqE
  have hJ : 1 < Valued.v W.j := multiplicative_j_nonintegral W hM
  have hJE : (W.baseChange F).j = (E'.baseChange F).j := by
    simp only [WeierstrassCurve.baseChange, map_j]
    exact congrArg (algebraMap K F) hj.symm
  obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq (W.baseChange F) (E'.baseChange F) hJE
  obtain ⟨h4, h6⟩ := nonintegral_j_invariants Valued.v W hJ
  have h4F : (W.baseChange F).c₄ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, map_c₄]
    exact (map_ne_zero_iff (algebraMap K F) (algebraMap K F).injective).mpr h4
  have h6F : (W.baseChange F).c₆ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, map_c₆]
    exact (map_ne_zero_iff (algebraMap K F) (algebraMap K F).injective).mpr h6
  let U := descendedUniformization W q C hC Uq
  obtain ⟨S⟩ := kummerRoots_nonempty (ℓ := ℓ) (closureParameter q)
  have hqi := closureParameter_infinite_order q had
  have hℓF : (ℓ : F) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hcard : ∀ n, Nat.card (TateModuleLevel ℓ (W.baseChange F).toAffine.Point n) =
      (ℓ ^ n) ^ 2 := fun n => (W.baseChange F).natCard_tateModuleLevel hℓF n
  let b := kummerTateBasis U S hqi hcard
  let ρ : Representation ℤ_[ℓ] (LocalGaloisQ p hp)
      (TateModule ℓ (W.baseChange F).toAffine.Point) := W.tateModuleGaloisRepresentation ℓ
  let pointAct := fun σ : LocalGaloisQ p hp => Affine.Point.map (W' := W) σ.toAlgHom
  let unitAct := fun σ : LocalGaloisQ p hp => Units.map σ.toAlgHom.toMonoidHom
  let ε := fun σ : LocalGaloisQ p hp => galoisSign C σ
  have hqfix : ∀ σ : LocalGaloisQ p hp, unitAct σ (closureParameter q) = closureParameter q := by
    intro σ
    apply Units.ext
    exact σ.commutes (q : K)
  have hproj : ∀ σ t n, (TateModule.proj n (ρ σ t) : (W.baseChange F).toAffine.Point) =
      pointAct σ (TateModule.proj n t : (W.baseChange F).toAffine.Point) :=
    fun σ t n => W.coe_proj_tateModuleGaloisRepresentation σ t n
  have hU : ∀ σ x, pointAct σ (U.map (Additive.ofMul x)) =
      ε σ • U.map (Additive.ofMul (unitAct σ x)) :=
    fun σ x => descendedUniformization_equivariant W q C hC h4F h6F Uq σ x
  obtain ⟨χ, κ, h0, h1⟩ := signed_kummer_columns U S hqi hcard ρ pointAct unitAct ε
    (fun σ => galoisSign_square C σ) hqfix hproj hU
  have hεI : ∀ σ ∈ localInertia w, ε σ = 1 := by
    intro σ hσ
    have hu := hS E p hp ℓ hℓp hM Γ w hw σ hσ
    have he := tate_sign_eq_one_of_unipotent ρ b (fun σ => (ε σ : ℤ_[ℓ])) χ κ σ
      (h0 σ) (h1 σ) hu
    apply (Int.cast_injective : Function.Injective (fun n : ℤ => (n : ℤ_[ℓ])))
    simpa only [Int.cast_one] using he
  have hχI : ∀ σ ∈ localInertia w, χ σ = 1 := by
    intro σ hσ
    exact kummer_chi_eq_one_of_unity_fixed U S hqi hcard ρ pointAct unitAct ε χ σ
      (hεI σ hσ) (h0 σ) (hproj σ) (hU σ)
      (fun n => local_inertia_fixes_unity p hp ℓ hℓp.symm Γ w hw n
        (S.unity n) (S.primitive n).pow_eq_one σ hσ)
  have hκ : ∃ σ ∈ localInertia w, κ σ ≠ 0 := by
    obtain ⟨σ, hσ, n, hn⟩ := inertia_moves_parameter_root hV p hp ℓ Γ w hw q had S
    exact ⟨σ, hσ, kummer_kappa_ne_zero_of_root_moved U S hqi hcard ρ pointAct unitAct ε κ σ
      (hεI σ hσ) (h1 σ) (hproj σ) (hU σ) (hqfix σ) n hn⟩
  refine ⟨b, (fun σ => (ε σ : ℤ_[ℓ])), χ, κ, h0, h1, ?_, hκ, ?_⟩
  · intro σ hσ
    exact ⟨by
      change (ε σ : ℤ_[ℓ]) = 1
      rw [hεI σ hσ, Int.cast_one], hχI σ hσ⟩
  · intro σ hσ
    have hf := frobenius_sign_of_unramified hF p hp Γ w hw σ hσ W E' C hC h4F h6F hεI
    have hf' : ε σ = if WeierstrassCurve.HasSplitMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ)
        ((E.baseChange K).minimal ((primeIdealQ p hp).adicCompletionIntegers ℚ))
        then 1 else -1 := by
      have hi : (∃ A : VariableChange K, A • W = E') ↔
          WeierstrassCurve.HasSplitMultiplicativeReduction
            ((primeIdealQ p hp).adicCompletionIntegers ℚ)
            ((E.baseChange K).minimal ((primeIdealQ p hp).adicCompletionIntegers ℚ)) := hsplit
      rw [propext hi] at hf
      exact hf
    split_ifs with hs
    · change (ε σ : ℤ_[ℓ]) = 1
      rw [ite_eq_left hs] at hf'
      rw [hf', Int.cast_one]
    · change (ε σ : ℤ_[ℓ]) = -1
      rw [ite_eq_right hs] at hf'
      rw [hf', Int.cast_neg, Int.cast_one]

end ZInQ.Contrib.RC53Assist.GlobalTrace
