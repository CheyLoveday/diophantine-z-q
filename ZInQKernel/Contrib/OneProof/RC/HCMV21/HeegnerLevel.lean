import ZInQKernel.Contrib.OneProof.RC.HCMV21.HeegnerModels
import ZInQKernel.Contrib.OneProof.RC.HCMV21.GoodModels

/-! Attach the analytic level subgroup and the common good-field construction
to the conductor-one Heegner datum. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField Module TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open scoped WeierstrassCurve nonZeroDivisors Classical

/-- Preimage of (A[\mathfrak n]) in the complex line for (A=\mathbb C/I).
This statement includes the embedding used to let the maximal order act. -/
theorem mem_levelLattice_iff {F : Type*} [Field F] [NumberField F]
    (κ : F →+* ℂ) (I : FractionalIdeal (𝓞 F)⁰ F)
    (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) (z : ℂ) :
    z ∈ κ '' (idealTranslate n I : Set F) ↔
      ∀ r ∈ n, κ (r : F) * z ∈ κ '' (I : Set F) := by
  let h := κ.comp (algebraMap (𝓞 F) F)
  letI : Algebra (𝓞 F) ℂ := h.toAlgebra
  letI : Module.IsTorsionFree (𝓞 F) ℂ :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := 𝓞 F) (A := ℂ)).mpr
      (κ.injective.comp (IsFractionRing.injective (𝓞 F) F))
  let e : F →ₗ[𝓞 F] ℂ :=
    { toFun := κ
      map_add' := κ.map_add
      map_smul' := fun r x => by
        change κ ((r : F) * x) = κ (r : F) * κ x
        exact κ.map_mul _ _ }
  have hh := ker_idealQuotientMap e κ.injective n hn I
  have he := congrArg (fun U : Submodule (𝓞 F) (ℂ ⧸ imageLattice e I) =>
    (imageLattice e I).mkQ z ∈ U) hh
  change ((Submodule.Quotient.mk z : ℂ ⧸ imageLattice e (idealTranslate n I)) = 0) =
    (∀ r ∈ n, (Submodule.Quotient.mk (r • z) : ℂ ⧸ imageLattice e I) = 0) at he
  simp only [Submodule.Quotient.mk_eq_zero] at he
  exact Iff.of_eq he

/-- The two ideals for the specific Heegner datum used in the
parametrization, with complex embedding induced by that datum. -/
theorem heegnerDatum_ideal_pair {E : WeierstrassCurve ℚ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) :
      Subgroup (GL (Fin 2) ℝ)) 2} {L : PeriodPair} {s : ℂ} {d t : ℤ}
    (dat : HeegnerDatum E f L s d 1 t) [NeZero (newformLevel E)]
    (hd : d < 0) (hcop : IsCoprime d (newformLevel E : ℤ)) :
    letI := dat.field
    letI := dat.nf
    letI := dat.nz
    let κ := dat.ι.toRingHom.comp (algebraMap dat.K (ringClassField (conductorOrder dat.K 1)))
    ∃ (a : ℤ) (ha : 0 < a) (_ : dat.A = (newformLevel E : ℤ) * a)
      (I : FractionalIdeal (𝓞 dat.K)⁰ dat.K) (n : Ideal (𝓞 dat.K)),
        I ≠ 0 ∧ n ≠ ⊥ ∧
        IsIdealPeriod κ I (formPeriod dat.A dat.B (d * (1 : ℤ) ^ 2) dat.form.1) ∧
        IsIdealPeriod κ (idealTranslate n I) (formPeriod a dat.B d ha) ∧
        X0Model.dilate (newformLevel E) (cmPoint dat.A dat.B (d * (1 : ℤ) ^ 2)) =
          cmPoint a dat.B d ∧
        ∃ w : 𝓞 dat.K, n = Ideal.span {(newformLevel E : 𝓞 dat.K), w} ∧
          κ (w : dat.K) = (-(dat.B : ℂ) + Complex.I * (Real.sqrt (-(d : ℝ)) : ℂ)) / 2 := by
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  let κ := dat.ι.toRingHom.comp (algebraMap dat.K (ringClassField (conductorOrder dat.K 1)))
  have hf : IsHeegnerForm (newformLevel E) (discr dat.K) dat.A dat.B dat.C := by
    simpa [dat.disc] using dat.form
  simpa [dat.disc, κ] using
    heegnerForm_ideal_pair dat.finrank_two dat.totallyComplex κ (by simpa [dat.disc] using hd)
      (by simpa [dat.disc] using hcop) hf

/-- The descended equations simultaneously have good models at the chosen
place, conditional on the one integral-(j) criterion. The auxiliary field
can retain morphism data once their fields of definition are supplied. -/
theorem simultaneous_good_models_of_descended_j {H K Γ₀ ι : Type}
    [Field H] [Field K] [CharZero K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    [IsDiscreteValuationRing (Valued.v (R := K)).valuationSubring] [Finite ι]
    (j : H →+* K) (x : ι → H) (hx : ∀ i, IsIntegral ℤ (x i))
    (hgood : IntegralJHasPotentiallyGoodReduction)
    (B : ValuationSubring (AlgebraicClosure K))
    (hB : B.comap (algebraMap K (AlgebraicClosure K)) = (Valued.v (R := K)).valuationSubring)
    (D : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K D] :
    ∃ M : IntermediateField K (AlgebraicClosure K), FiniteDimensional K M ∧ D ≤ M ∧
      ∀ i, HasGoodModelAt B M (WeierstrassCurve.ofJ (j (x i))) := by
  let jZ : H →ₐ[ℤ] K := { toRingHom := j, commutes' := map_intCast j }
  apply simultaneous_good_models_of_integral_j hgood B hB (fun i => WeierstrassCurve.ofJ (j (x i)))
    _ D
  intro i
  rw [WeierstrassCurve.ofJ_j]
  exact (hx i).map jZ

end ZInQ.Manuscript.RC.HCMV21
