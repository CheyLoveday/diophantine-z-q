import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusSqrtMem
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusTheoryReduction
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.SqrtDiscr

/-!
# GenusOdd: `GenusRoots` PROVED

`genusRoots_proof : GenusRoots`: `s₁ = √d₁ ∈ H_c` (`exists_sqrt_mem_ringClassField`), acted on by
`χ` (`genus_action`), and `s₂ = c √(disc K) / s₁` (`exists_sq_eq_discr`), so `s₂² = d₂` from
`d₁ d₂ = disc(K) c²`, acted on by `χ` as well since `√(disc K) ∈ K`. Hence the GLUE of (3.4) reduces
to `ArtinFactorization`, `RingClassGalois` and `SplittingCriterion` (`genusLower34_of_reduced'`).
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

/-- **`GenusRoots`, PROVED** from Tau Ceti's class field theory (splitting law, Frobenius
generation) and Euler's criterion. -/
theorem genusRoots_proof : GenusRoots := by
  intro K _ _ hK2 hTC hDodd c _ d₁ d₂ hprod hd₁ hsq hcd hcD χ hχ
  obtain ⟨s₁, hs₁⟩ := exists_sqrt_mem_ringClassField hd₁ hχ
  obtain ⟨r, hr⟩ := exists_sq_eq_discr hK2
  have hchar : CharZero (ringClassField (conductorOrder K c)) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have hd₁0 : d₁ ≠ 0 := by rintro rfl; norm_num at hd₁
  have hs₁0 : s₁ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hs₁
    exact hd₁0 (by exact_mod_cast hs₁.symm)
  set R : ringClassField (conductorOrder K c) :=
    algebraMap K (ringClassField (conductorOrder K c)) r * (c : ringClassField (conductorOrder K c))
  have hR : R ^ 2 = ((discr K * c ^ 2 : ℤ) : ringClassField (conductorOrder K c)) := by
    simp only [R, mul_pow, ← map_pow, hr, map_intCast]; push_cast; ring
  refine ⟨s₁, R / s₁, hs₁, ?_, fun σ => ⟨genus_action hd₁ hχ s₁ hs₁ σ, ?_⟩⟩
  · rw [div_pow, hR, hs₁, ← hprod]
    push_cast
    field_simp
  · have h1 := genus_action hd₁ hχ s₁ hs₁ σ
    have hσR : σ R = R := by
      simp only [R, map_mul, map_natCast, AlgEquiv.commutes]
    rw [map_div₀, hσR, h1]
    have hsq := chiSign_sq (χ := χ) ((ringClassArtinEquiv (conductorOrder K c)).symm σ)
    have hcs : ((chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) :
        ringClassField (conductorOrder K c)) ^ 2 = 1 := by
      rw [sq]; exact_mod_cast hsq
    have hne : ((chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) :
        ringClassField (conductorOrder K c)) ≠ 0 := by
      intro h0; rw [h0] at hcs; norm_num at hcs
    field_simp
    rw [hcs, mul_one]

/-- The GLUE of (3.4) after `GenusRoots`: `ArtinFactorization`, `RingClassGalois`,
`SplittingCriterion`. -/
structure GlueAfterRoots : Prop where
  artin : ArtinFactorization
  galois : RingClassGalois
  split : SplittingCriterion

theorem glueFinal_of_roots (G : GlueAfterRoots) : GlueFinal :=
  ⟨G.artin, G.galois, genusRoots_proof, G.split⟩

/-- **(3.4)** from the printed leaves and `GlueAfterRoots`. -/
theorem genusLower34_of_afterRoots (P : Prints) (G : GlueAfterRoots) : GenusLower34 :=
  genusLower34_of_final P (glueFinal_of_roots G)

end ZInQ.Contrib.CloudB3RC53.GenusOdd
