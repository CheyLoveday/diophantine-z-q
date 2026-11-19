import ZInQKernel.Contrib.RC53Assist.CentralUniversal.CoefficientComplex
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Universal coefficients for the coefficient quotient: the corank of `H¹(C ⊗ ℚ₂/ℤ₂)`

Let `C` be a cochain complex of torsion-free `ℤ₂`-modules and let `C ⊗ ℚ₂/ℤ₂` be its coefficient
quotient, the cokernel complex `coefficientQuotientComplex C` of the canonical coefficient map
`C → ℚ₂ ⊗ C`. The universal-coefficient sequence
`0 → ℚ₂/ℤ₂ ⊗ H¹(C) → H¹(C ⊗ ℚ₂/ℤ₂) → H²(C)[tors] → 0`
is exact (`universalCoefficientSequence_shortExact`). When `H¹(C)` and `H²(C)` are finitely
generated, this file shows that the `ℤ₂`-corank of `H¹(C ⊗ ℚ₂/ℤ₂)` is the integral rank of `H¹(C)`
and that the finite part is the torsion of `H²(C)`:
`H¹(C ⊗ ℚ₂/ℤ₂) ≃+ (ℚ₂/ℤ₂)^r × H²(C)[tors]` with `r = finrank ℤ₂ H¹(C)`.

* `z2Corank_of_addEquiv`: a corank is transported along an additive equivalence.
* `finite_torsion_of_moduleFinite`: the torsion submodule of a finitely generated `ℤ₂`-module is a
  finite set. It is killed by a power `2^n`, so it is a finitely generated module over the quotient
  of `ℤ₂` by the kernel of the reduction `ℤ₂ → ℤ/2^n`, a finite ring.
* `coefficientCorank_q2z2_zsmul_surjective`: `ℚ₂/ℤ₂` is divisible by every nonzero integer.
* `coefficientCorank_homology_one_splitting`: the additive splitting
  `H¹(C ⊗ ℚ₂/ℤ₂) ≃+ (ℚ₂/ℤ₂)^r × H²(C)[tors]`. The first term `ℚ₂/ℤ₂ ⊗ H¹(C)` has the divisible
  coordinates `(ℚ₂/ℤ₂)^r` in a basis of `H¹(C)` modulo torsion (`divisibleCoordinates`); a
  divisible abelian group is injective (Baer's criterion), so the injective universal-coefficient
  map has an additive retraction and the exact sequence splits additively.
* `z2Corank_coefficientQuotient_homology_one`: `corank_{ℤ₂} H¹(C ⊗ ℚ₂/ℤ₂) = finrank ℤ₂ H¹(C)`.

Kinds: PROVED.
-/

namespace ZInQ.Manuscript.RC

open ZInQ.Manuscript.RC53Assist.CentralUniversal ZInQ.Manuscript.SelmerTwoPower

/-- **Transport of a `ℤ₂`-corank along an additive equivalence**: if `M` has `ℤ₂`-corank `r`,
i.e. `M ≃+ (ℚ₂/ℤ₂)^r × F` with `F` finite, and `M ≃+ N`, then `N` has `ℤ₂`-corank `r`, with the
same finite part `F`. Kind: PROVED. -/
theorem z2Corank_of_addEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N] {r : ℕ}
    (h : Z2Corank M r) (e : M ≃+ N) : Z2Corank N r := by
  obtain ⟨F, hF, hFin, ⟨e'⟩⟩ := h
  exact ⟨F, hF, hFin, ⟨e.symm.trans e'⟩⟩

/-- **The torsion of a finitely generated `ℤ₂`-module is finite**: for a finitely generated
`ℤ₂`-module `M`, the torsion submodule `M[tors]` is a finite set. A power `2^n` kills `M[tors]`,
which is finitely generated (`ℤ₂` is Noetherian); hence `M[tors]` is a finitely generated module
over `ℤ₂ ⧸ ker(ℤ₂ → ℤ/2^n)`, a ring embedded in the finite ring `ℤ/2^n` (the residue field is
finite). Kind: PROVED. -/
theorem finite_torsion_of_moduleFinite (M : Type) [AddCommGroup M] [Module ℤ_[2] M]
    [Module.Finite ℤ_[2] M] : Finite (Submodule.torsion ℤ_[2] M) := by
  obtain ⟨n, hn⟩ := finite_torsion_two_power M
  let I : Ideal ℤ_[2] := RingHom.ker (PadicInt.toZModPow (p := 2) n)
  have hT : Module.IsTorsionBySet ℤ_[2] (Submodule.torsion ℤ_[2] M) (I : Set ℤ_[2]) := by
    intro x a
    have ha : (a : ℤ_[2]) ∈ Ideal.span {(2 : ℤ_[2]) ^ n} := by
      have h2 := a.2
      change (a : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow (p := 2) n) at h2
      rw [PadicInt.ker_toZModPow] at h2
      exact_mod_cast h2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    have hx : ((2 : ℤ_[2]) ^ n) • x = 0 := by
      apply Subtype.ext
      have h1 := hn x.1 x.2
      rw [← Nat.cast_smul_eq_nsmul ℤ_[2]] at h1
      simpa using h1
    rw [← hc, mul_smul, hx, smul_zero]
  let _ : Module (ℤ_[2] ⧸ I) (Submodule.torsion ℤ_[2] M) := hT.module
  have : IsScalarTower ℤ_[2] (ℤ_[2] ⧸ I) (Submodule.torsion ℤ_[2] M) := hT.isScalarTower
  have : Module.Finite (ℤ_[2] ⧸ I) (Submodule.torsion ℤ_[2] M) :=
    Module.Finite.of_restrictScalars_finite ℤ_[2] _ _
  have : Finite (ℤ_[2] ⧸ I) := Finite.of_injective _ (RingHom.kerLift_injective _)
  exact Module.finite_of_finite (ℤ_[2] ⧸ I)

/-- **`ℚ₂/ℤ₂` is divisible by the nonzero integers**: for every integer `n ≠ 0`, multiplication
by `n` is surjective on `ℚ₂/ℤ₂`. Kind: PROVED. -/
theorem coefficientCorank_q2z2_zsmul_surjective {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun d : Q2Z2 => n • d) := by
  intro d
  obtain ⟨e, he⟩ := divisible_smul_surjective (n : ℤ_[2]) (Int.cast_ne_zero.mpr hn) d
  refine ⟨e, ?_⟩
  change n • e = d
  rw [← Int.cast_smul_eq_zsmul ℤ_[2]]
  exact he

/-- **Additive splitting of universal coefficients**: for a cochain complex `C` of torsion-free
`ℤ₂`-modules with finitely generated `H¹(C)`, the first cohomology of the coefficient quotient
`C ⊗ ℚ₂/ℤ₂` is additively isomorphic to `(ℚ₂/ℤ₂)^r × H²(C)[tors]`, where `r` is the integral rank
`finrank ℤ₂ H¹(C)` and `H²(C)[tors]` is the torsion submodule of `H²(C)`. Kind: PROVED. -/
theorem coefficientCorank_homology_one_splitting (C : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ)
    [∀ n : ℤ, Module.IsTorsionFree ℤ_[2] (C.X n)] [Module.Finite ℤ_[2] (C.homology 1)] :
    Nonempty ((coefficientQuotientComplex C).homology 1 ≃+
      (Fin (Module.finrank ℤ_[2] (C.homology 1)) → Q2Z2) ×
        Submodule.torsion ℤ_[2] (C.homology 2)) := by
  have hrank : freeRank (C.homology 1) = Module.finrank ℤ_[2] (C.homology 1) :=
    finrank_quotient_eq_of_le_torsion (le_refl _)
  rw [← hrank]
  let ι : (Fin (freeRank (C.homology 1)) → Q2Z2) →ₗ[ℤ_[2]]
      (coefficientQuotientComplex C).homology 1 :=
    (universalCoefficientMap C).comp (divisibleCoordinates (C.homology 1)).symm.toLinearMap
  have hι : Function.Injective ι :=
    (universalCoefficientMap_injective C).comp (LinearEquiv.injective _)
  have hex : Function.Exact ι (coefficientTorsionConnecting C) := by
    intro y
    rw [universalCoefficient_exact C y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨divisibleCoordinates (C.homology 1) x, by simp [ι]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  let _ : DivisibleBy Q2Z2 ℤ :=
    divisibleByOfSMulRightSurj _ _ coefficientCorank_q2z2_zsmul_surjective
  have hB := Module.Baer.of_divisible (Fin (freeRank (C.homology 1)) → Q2Z2)
  obtain ⟨ρ, hρ⟩ := hB.extension_property_addMonoidHom ι.toAddMonoidHom hι (AddMonoidHom.id _)
  have hρ' : ρ.toIntLinearMap ∘ₗ ι.toAddMonoidHom.toIntLinearMap = LinearMap.id :=
    LinearMap.ext fun x => DFunLike.congr_fun hρ x
  exact ⟨(Function.Exact.splitInjectiveEquiv (f := ι.toAddMonoidHom.toIntLinearMap)
    (g := (coefficientTorsionConnecting C).toAddMonoidHom.toIntLinearMap) hex
    (coefficientTorsionConnecting_surjective C) ⟨_, hρ'⟩).1.toAddEquiv⟩

/-- **Universal coefficients with finite torsion `H²`**: for a cochain complex `C` of torsion-free
`ℤ₂`-modules with finitely generated `H¹(C)` and `H²(C)`, the first cohomology of the coefficient
quotient `C ⊗ ℚ₂/ℤ₂` has `ℤ₂`-corank equal to the integral rank of `H¹(C)`:
`H¹(C ⊗ ℚ₂/ℤ₂) ≃+ (ℚ₂/ℤ₂)^r × F` with `F` finite and `r = finrank ℤ₂ H¹(C)`; the finite part is
`F = H²(C)[tors]`. Kind: PROVED. -/
theorem z2Corank_coefficientQuotient_homology_one (C : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ)
    [∀ n : ℤ, Module.IsTorsionFree ℤ_[2] (C.X n)]
    [Module.Finite ℤ_[2] (C.homology 1)] [Module.Finite ℤ_[2] (C.homology 2)] :
    Z2Corank ((coefficientQuotientComplex C).homology 1)
      (Module.finrank ℤ_[2] (C.homology 1)) :=
  ⟨Submodule.torsion ℤ_[2] (C.homology 2), inferInstance,
    finite_torsion_of_moduleFinite (C.homology 2), coefficientCorank_homology_one_splitting C⟩

end ZInQ.Manuscript.RC
