import ZInQKernel.Contrib.RC53Assist.GlobalTrace.CoinvariantReadings
import ZInQKernel.Contrib.RC53Assist.DecompositionGlue.LocalGlobal

/-!
# The local–global decomposition-group glue

This file proves `GlobalTrace.DecompositionGroupLocalGlobalGlue` exactly as stated: for every
rational prime `p` and every place `D.place` of `\bar ℚ` above `p` with arithmetic Frobenius
`D.element`, there are a valuation `w` on `\bar ℚ_p` extending the `p`-adic valuation, an
embedding `ι : \bar ℚ → \bar ℚ_p` and a homomorphism `r : Gal(\bar ℚ_p / ℚ_p) → G_ℚ` with
`ι ∘ r(σ) = σ ∘ ι`, carrying the inertia group of `w` onto the inertia group of `D.place` and some
local arithmetic Frobenius to `D.element`.

The witnesses, in order:

* `w` is the spectral valuation on `\bar ℚ_p` (values in `ℝ≥0`), the unique extension of the
  absolute value of `ℚ_p` (Milne, *Algebraic Number Theory*, v3.08, Cor. 7.40, p. 124);
* `ι` is constructed after `D.place`, so that it induces it: `x ∈ D.place ↔ w (ι x) ≤ 1`
  (`exists_algHom_comap_eq`, from the transitivity of `G_ℚ` on the places above `p`);
* `r` is restriction along `ι` (`restrictionHom`); it lands in the decomposition group, and every
  element of the decomposition group is a restriction (`exists_galois_lift`; at finite level Milne,
  Prop. 8.10, p. 139), by density of `ι (\bar ℚ)` in `\bar ℚ_p` (Lang, *Algebraic Number Theory*,
  Ch. II, §2, Prop. 3–4, pp. 43–44; Milne, Cor. 7.62, p. 132);
* the residue identification induced by `ι` is onto (`exists_residue_lift`), which transfers the
  inertia groups (`map_restrictionHom_localInertia`) and the given arithmetic Frobenius
  (`exists_frobenius_lift`), with the arithmetic `p`-power convention of Milne, p. 141.

## Classification

PROVED. `decompositionGroupLocalGlobalGlue` discharges the glue statement with no hypotheses.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.DecompositionGlue

open IsDedekindDomain NumberField
open scoped NNReal WithZero
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.GlobalTrace

/-- **DEFINITION**, the nontrivially normed field structure on `ℚ_p` determined by its rank-one
`p`-adic valuation; its underlying normed field is Mathlib's
`NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion`. Locator: Mathlib
`Valued.toNontriviallyNormedField`. -/
@[reducible]
def padicNontriviallyNormedField (p : ℕ) (hp : p.Prime) :
    NontriviallyNormedField ((primeIdealQ p hp).adicCompletion ℚ) :=
  Valued.toNontriviallyNormedField _ ℤᵐ⁰

/-- **PROVED**, `0 < ‖p‖ < 1` in `ℚ_p`. Locator: Mathlib
`NumberField.FinitePlace.norm_lt_one_iff_mem` (`p` lies in the prime ideal `(p)`). -/
theorem norm_prime_pos_lt_one (p : ℕ) (hp : p.Prime) :
    0 < ‖((p : ℚ) : (primeIdealQ p hp).adicCompletion ℚ)‖ ∧
      ‖((p : ℚ) : (primeIdealQ p hp).adicCompletion ℚ)‖ < 1 := by
  constructor
  · rw [norm_pos_iff, Rat.cast_natCast]
    exact_mod_cast hp.ne_zero
  · have h := (FinitePlace.norm_lt_one_iff_mem ℚ (primeIdealQ p hp) (p : 𝓞 ℚ)).2
      (Ideal.mem_span_singleton_self _)
    simpa using h

/-- **PROVED**, `ℚ` is dense in `ℚ_p`. Locator: Mathlib
`IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap`. -/
theorem denseRange_ratCast_padic (p : ℕ) (hp : p.Prime) :
    DenseRange ((↑) : ℚ → (primeIdealQ p hp).adicCompletion ℚ) := by
  convert HeightOneSpectrum.denseRange_algebraMap ℚ (primeIdealQ p hp) using 1
  funext q
  exact (eq_ratCast _ q).symm

/-- **PROVED**, the glue `DecompositionGroupLocalGlobalGlue`, exactly as stated. Witnesses: the
spectral valuation, an embedding constructed after the given place so that it induces it, and the
restriction along it. Locator: `exists_algHom_comap_eq`, `restrictionHom_apply`,
`map_restrictionHom_localInertia`, `exists_frobenius_lift`; Milne, Prop. 8.2, p. 136 and
Prop. 8.10, p. 139; Lang, Ch. II, §2, Prop. 3–4, pp. 43–44; Milne, Cor. 7.42 and Cor. 7.52,
pp. 124–128 for the residue fields. -/
theorem decompositionGroupLocalGlobalGlue : DecompositionGroupLocalGlobalGlue := by
  intro p hp D
  let _ : NontriviallyNormedField ((primeIdealQ p hp).adicCompletion ℚ) :=
    padicNontriviallyNormedField p hp
  have hd := denseRange_ratCast_padic p hp
  obtain ⟨hq0, hq1⟩ := norm_prime_pos_lt_one p hp
  have h₀ : (p : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) ∈
      (spectralValuation ((primeIdealQ p hp).adicCompletion ℚ)).valuationSubring.nonunits := by
    rw [mem_valuationSubring_nonunits_iff, ← NNReal.coe_lt_coe, NNReal.coe_one,
      ← map_natCast (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))) p,
      spectralValuation_algebraMap]
    simpa using hq1
  obtain ⟨ι, hι⟩ := exists_algHom_comap_eq _ hp h₀ D.place D.liesOver
  have hι' : ∀ x, x ∈ D.place ↔
      spectralValuation ((primeIdealQ p hp).adicCompletion ℚ) (ι x) ≤ 1 := fun x =>
    (hι x).trans (Valuation.mem_valuationSubring_iff _ _)
  obtain ⟨σ, hσF, hσr⟩ := exists_frobenius_lift hd hq0 hq1 hι' D.isFrob
  refine ⟨ℝ≥0, inferInstance, spectralValuation ((primeIdealQ p hp).adicCompletion ℚ), ι,
    restrictionHom ι, ?_, restrictionHom_apply ι, map_restrictionHom_localInertia hd hq0 hq1 hι',
    σ, ?_, hσr⟩
  · intro r s
    rw [Valuation.comap_apply, Valuation.comap_apply, ← NNReal.coe_le_coe,
      spectralValuation_algebraMap, spectralValuation_algebraMap]
    exact Valued.toNormedField.norm_le_iff
  · intro y hy
    rw [primeIdealQ_absNorm]
    exact hσF y hy

/-! ## Non-vacuity

The hypothesis of the glue is satisfiable (Frobenius data exist at every prime, by
`localArithmeticFrobenius_nonempty`), so the conclusion is obtained for actual data; and the
inputs of the local step are met by `ℚ_p` itself. -/

/-- Non-vacuity: the conclusion of the glue for actual Frobenius data at `p = 2`. -/
example : ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ)
    (w : Valuation (AlgebraicClosure ((primeIdealQ 2 Nat.prime_two).adicCompletion ℚ)) Γ)
    (ι : AlgebraicClosure ℚ →ₐ[ℚ]
      AlgebraicClosure ((primeIdealQ 2 Nat.prime_two).adicCompletion ℚ))
    (r : LocalGaloisQ 2 Nat.prime_two →* GlueC10.GQ),
    (∀ (σ : LocalGaloisQ 2 Nat.prime_two) (x : AlgebraicClosure ℚ), ι (r σ x) = σ (ι x)) ∧
      (localInertia w).map r =
        inertiaAt (Classical.choice (localArithmeticFrobenius_nonempty 2 Nat.prime_two)) := by
  obtain ⟨Γ, inst, w, ι, r, -, hcomm, hinert, -⟩ := decompositionGroupLocalGlobalGlue 2
    Nat.prime_two (Classical.choice (localArithmeticFrobenius_nonempty 2 Nat.prime_two))
  exact ⟨Γ, inst, w, ι, r, hcomm, hinert⟩

/-- Non-vacuity: the density and norm inputs of the local step hold for `ℚ_3`. -/
example : DenseRange ((↑) : ℚ → (primeIdealQ 3 Nat.prime_three).adicCompletion ℚ) ∧
    0 < ‖(((3 : ℕ) : ℚ) : (primeIdealQ 3 Nat.prime_three).adicCompletion ℚ)‖ ∧
      ‖(((3 : ℕ) : ℚ) : (primeIdealQ 3 Nat.prime_three).adicCompletion ℚ)‖ < 1 :=
  ⟨denseRange_ratCast_padic 3 Nat.prime_three, norm_prime_pos_lt_one 3 Nat.prime_three⟩

end ZInQ.Contrib.RC53Assist.DecompositionGlue
