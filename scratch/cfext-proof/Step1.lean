import Mathlib

open scoped TensorProduct
open IsLocalRing

set_option linter.style.haveILetI false

namespace CFExtProof

theorem unram_step {K R L : Type*} [Field K] [Field L] [CommRing R] [IsLocalRing R] [Algebra K R]
    [Algebra K L] [Algebra.FormallyUnramified K L] [Module.Finite K L]
    (p : Ideal (R ⊗[K] L)) [p.IsPrime]
    (hp : p.comap (algebraMap R (R ⊗[K] L)) = maximalIdeal R)
    (π : R) (hπ : maximalIdeal R = Ideal.span {π})
    (a : R ⊗[K] L) (ha : a ∈ p) :
    ∃ s ∉ p, ∃ b, s * a = algebraMap R _ π * b := by
  let Ap := Localization.AtPrime p
  haveI : IsLocalHom (algebraMap R Ap) := by
    constructor
    intro x hx
    rw [IsScalarTower.algebraMap_apply R (R ⊗[K] L) Ap] at hx
    have h1 : algebraMap R (R ⊗[K] L) x ∈ p.primeCompl :=
      (IsLocalization.AtPrime.isUnit_to_map_iff Ap p _).mp hx
    by_contra hu
    refine h1 (show algebraMap R (R ⊗[K] L) x ∈ p from ?_)
    rw [← Ideal.mem_comap, hp]; exact hu
  haveI : Algebra.FormallyUnramified R Ap := Algebra.FormallyUnramified.comp R (R ⊗[K] L) Ap
  haveI : Algebra.EssFiniteType R Ap := Algebra.EssFiniteType.comp R (R ⊗[K] L) Ap
  have hmax := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := Ap)
  have hmem : algebraMap (R ⊗[K] L) Ap a ∈ maximalIdeal Ap := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ ha
  rw [← hmax, hπ, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hmem
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  have hz' : algebraMap (R ⊗[K] L) Ap (b * algebraMap R (R ⊗[K] L) π) = algebraMap (R ⊗[K] L) Ap (a * s) := by
    rw [map_mul, map_mul, ← hz, IsScalarTower.algebraMap_apply R (R ⊗[K] L) Ap, mul_right_comm,
      IsLocalization.mk'_spec]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl Ap).mp hz'
  refine ⟨c * s, p.primeCompl.mul_mem c.2 s.2, c * b, ?_⟩
  linear_combination -hc

end CFExtProof
