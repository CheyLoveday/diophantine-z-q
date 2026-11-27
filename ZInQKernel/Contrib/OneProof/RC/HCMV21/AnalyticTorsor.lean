import ZInQKernel.Contrib.OneProof.RC.HCMV21.IdealLattice
import Mathlib.RingTheory.ClassGroup.Basic

/-! Fixed-type analytic CM ideal classes. The selected level subgroup of
each torus is the torsion for the same ideal `n`; it is not a further
choice varying with the fractional ideal. -/

namespace ZInQ.Manuscript.RC.HCMV21

open scoped nonZeroDivisors
open FractionalIdeal

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The analytic class set: nonzero invertible ideal lattices modulo
homothety. The ambient embedding and level ideal are fixed. -/
abbrev IdealLatticeClass (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  (FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range

/-- A class acts by the inverse ideal, i.e. by the lattice containing the
original lattice when the acting ideal is integral. -/
noncomputable instance : SMul (ClassGroup R) (IdealLatticeClass R K) :=
  ⟨fun c x => (ClassGroup.equiv K c)⁻¹ * x⟩

noncomputable instance : MulAction (ClassGroup R) (IdealLatticeClass R K) where
  one_smul x := by change (ClassGroup.equiv K 1)⁻¹ * x = x; simp
  mul_smul c d x := by
    change (ClassGroup.equiv K (c * d))⁻¹ * x =
      (ClassGroup.equiv K c)⁻¹ * ((ClassGroup.equiv K d)⁻¹ * x)
    rw [map_mul, mul_inv_rev, ← mul_assoc, mul_comm ((ClassGroup.equiv K d)⁻¹), mul_assoc]

/-- Free and transitive before constructing any reduction map. -/
theorem analytic_orbit_bijective (x : IdealLatticeClass R K) :
    Function.Bijective (fun c : ClassGroup R => c • x) := by
  exact (Equiv.mulRight x).bijective.comp (inv_bijective.comp (ClassGroup.equiv K).bijective)

/-- The quotient really identifies complex homotheties of embedded ideals:
for normalized nonzero lattices the scalar is in the quadratic field. -/
theorem idealClass_eq_iff_complexHomothety
    {E : Type*} [Field E] (ι : K →+* E) (I J : (FractionalIdeal R⁰ K)ˣ) :
    (QuotientGroup.mk I : IdealLatticeClass R K) = QuotientGroup.mk J ↔
      ∃ z : E, z ≠ 0 ∧
        (fun x => z * ι x) '' ((I : FractionalIdeal R⁰ K) : Set K) =
          ι '' ((J : FractionalIdeal R⁰ K) : Set K) := by
  rw [QuotientGroup.eq_iff_div_mem]
  constructor
  · rintro ⟨u, hu⟩
    have hJ : I * toPrincipalIdeal R K u⁻¹ = J := by rw [map_inv, hu, inv_div, mul_comm, div_mul_cancel]
    have hJ' : spanSingleton R⁰ ((u⁻¹ : Kˣ) : K) * (I : FractionalIdeal R⁰ K) = J := by
      rw [mul_comm, ← coe_toPrincipalIdeal, ← Units.val_mul, hJ]
    refine ⟨ι (↑u⁻¹ : K), (map_ne_zero ι).2 (Units.ne_zero u⁻¹), ?_⟩
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨↑u⁻¹ * x, by rw [← hJ']; exact mem_singleton_mul.mpr ⟨x, hx, rfl⟩,
        map_mul ι _ _⟩
    · rintro ⟨y, hy, rfl⟩
      rw [← hJ'] at hy
      obtain ⟨x, hx, rfl⟩ := mem_singleton_mul.mp hy
      exact ⟨x, hx, (map_mul ι _ _).symm⟩
  · rintro ⟨z, hz, h⟩
    obtain ⟨u, hu⟩ := homothety_scalar_in_fractionField ι I.ne_zero z hz
      (fun x hx => by rw [← h]; exact ⟨x, hx, rfl⟩)
    have hJ : I * toPrincipalIdeal R K u = J := by
      apply Units.ext
      rw [Units.val_mul, coe_toPrincipalIdeal, mul_comm, eq_comm, eq_spanSingleton_mul]
      constructor
      · intro y hy
        obtain ⟨x, hx, he⟩ : ι y ∈ (fun x => z * ι x) '' ((I : FractionalIdeal R⁰ K) : Set K) :=
          h.symm ▸ ⟨y, hy, rfl⟩
        exact ⟨x, hx, ι.injective (by rwa [map_mul, hu])⟩
      · intro x hx
        obtain ⟨y, hy, he⟩ : z * ι x ∈ ι '' ((J : FractionalIdeal R⁰ K) : Set K) :=
          h ▸ ⟨x, hx, rfl⟩
        have heq : (u : K) * x = y := ι.injective (by rw [map_mul, hu, he])
        rwa [heq]
    refine ⟨u⁻¹, ?_⟩
    rw [map_inv, ← hJ, div_mul_cancel_left]

end ZInQ.Manuscript.RC.HCMV21
