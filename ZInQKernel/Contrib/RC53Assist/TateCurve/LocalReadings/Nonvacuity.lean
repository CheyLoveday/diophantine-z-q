import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.LocalFrobenius

/-!
# Non-vacuity of the local readings

Every prime has an extending valuation, an arithmetic Frobenius, and a nonzero
inertia-fixed algebraic element of value strictly less than one. The element is
the rational prime itself. Thus both readings concern actual nontrivial valuation
data. The residue Frobenius is also nonidentity in a quadratic finite-field extension.

Kinds: proved non-vacuity examples.
Locators: Serre, *Local Fields*, I, §8 and III, §5; arithmetic Frobenius and the base
uniformizer. The book is not Serre's chapter in Cassels--Fröhlich.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open ZInQ.Contrib.RC53Assist.DecompositionGlue
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.GlobalTrace
open scoped WithZero NNReal

/-- **PROVED NON-VACUITY**: quadratic finite-field Frobenius is not the identity.
Locator: its order is the extension degree, Serre I, §8. -/
theorem finiteField_frobenius_nonidentity_quadratic (p : ℕ) [Fact p.Prime] :
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (GaloisField p 2) ≠ 1 := by
  have ho : orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p)
      (GaloisField p 2)) = 2 := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      GaloisField.finrank p (by decide : (2 : ℕ) ≠ 0)]
  intro h
  rw [h, orderOf_one] at ho
  norm_num at ho

/-- **PROVED NON-VACUITY**: actual inputs of both local targets exist at every prime.
The inertia-fixed field unit has nontrivial value, and the open-subgroup
hypotheses are realized by the full subgroup. Locator: spectral extension,
existence of arithmetic Frobenius, and the base uniformizer. -/
theorem local_readings_nonvacuity (p : ℕ) (hp : p.Prime) :
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ)
      (w : Valuation (LocalClosureQ p hp) Γ) (σ : LocalGaloisQ p hp)
      (x : (LocalClosureQ p hp)ˣ),
      (w.comap (algebraMap (LocalBaseQ p hp) (LocalClosureQ p hp))).IsEquiv
        (Valued.v : Valuation (LocalBaseQ p hp) ℤᵐ⁰) ∧
      IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ ∧
      w (x : LocalClosureQ p hp) < 1 ∧
      (∀ τ ∈ localInertia w, Units.map τ.toAlgHom.toMonoidHom x = x) ∧
      ∃ H : Subgroup (LocalGaloisQ p hp), IsOpen (H : Set (LocalGaloisQ p hp)) ∧
        localInertia w ≤ H ∧ σ ∈ H := by
  letI := padicNontriviallyNormedField p hp
  let K := LocalBaseQ p hp
  let w := spectralValuation K
  have hw : (w.comap (algebraMap K (AlgebraicClosure K))).IsEquiv
      (Valued.v : Valuation K ℤᵐ⁰) :=
    (spectral_hasExtension (Valued.v : Valuation K ℤᵐ⁰)
      (fun _ => Valued.toNormedField.norm_le_one_iff)).val_isEquiv_comap.symm
  obtain ⟨σ, hσ⟩ := local_arithmeticFrobenius_exists p hp ℝ≥0 w hw
  let x : (AlgebraicClosure K)ˣ := Units.mk0 (p : AlgebraicClosure K)
    (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hpw : w (x : AlgebraicClosure K) < 1 := by
    change spectralValuation K (p : AlgebraicClosure K) < 1
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)) p, ← NNReal.coe_lt_coe,
      spectralValuation_algebraMap, NNReal.coe_one]
    simpa only [Rat.cast_natCast] using (norm_prime_pos_lt_one p hp).2
  have hfix : ∀ τ ∈ localInertia w, Units.map τ.toAlgHom.toMonoidHom x = x := by
    intro τ _
    apply Units.ext
    change τ (p : AlgebraicClosure K) = p
    exact map_natCast τ p
  exact ⟨ℝ≥0, inferInstance, w, σ, x, hw, hσ, hpw, hfix,
    ⊤, isOpen_univ, le_top, Subgroup.mem_top σ⟩

end ZInQ.Contrib.RC53Assist.TateCurve
