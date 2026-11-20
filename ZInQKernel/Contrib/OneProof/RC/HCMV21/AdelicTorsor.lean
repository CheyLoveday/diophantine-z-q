import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
import Mathlib.GroupTheory.DoubleCoset

/-! The adelic calculation applies to the orbit with the pointwise
centralizer on the left. The only local arithmetic premise here is the
intersection with the unit group on the right. -/

namespace ZInQ.Manuscript.RC.HCMV21

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped NumberField

variable {R F G : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F] [Group G]

local notation "T" => 𝔸ᶠ[R, F]ˣ

/-- The diagonal rational units of the embedded quadratic torus. -/
noncomputable def rationalTorusUnits (j : T →* G) : Subgroup G :=
  (j.comp (unitEmbedding R F)).range

/-- The class-set map using the pointwise stabilizer. -/
noncomputable def torusOrbitMap (j : T →* G) (U : Subgroup G) (z : G) (s : T) :
    DoubleCoset.Quotient (rationalTorusUnits j : Set G) (U : Set G) :=
  DoubleCoset.mk (rationalTorusUnits j) U (j s * z)

/-- On this adelic orbit, equality of classes is precisely equality of
ideal classes. The hypothesis identifies the preimage of the conjugated
right order units, without making any claim about geometric reduction. -/
theorem torusOrbitMap_eq_iff (j : T →* G)
    (U : Subgroup G) (z : G)
    (hunit : ∀ s : T, z⁻¹ * j s * z ∈ U ↔ s ∈ integralUnits R F)
    (s t : T) :
    torusOrbitMap j U z s = torusOrbitMap j U z t ↔
      toClassGroup R F s = toClassGroup R F t := by
  rw [torusOrbitMap, torusOrbitMap, DoubleCoset.eq]
  let f := toClassGroup R F
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, u, hu, he⟩
    let r := unitEmbedding R F a
    let v := (r * s)⁻¹ * t
    have hev : z⁻¹ * j v * z = u := by
      change j t * z = j r * (j s * z) * u at he
      have ht : j t = j r * (j s * z) * u * z⁻¹ := by rw [← he]; group
      dsimp [v]
      rw [map_mul, map_inv, map_mul, ht]
      group
    have hv : v ∈ integralUnits R F := (hunit v).mp (hev ▸ hu)
    have hv' : f v = 1 := by
      change v ∈ f.ker
      rw [ker_toClassGroup]
      exact Subgroup.mem_sup_left hv
    have hr : f r = 1 := by
      change r ∈ f.ker
      rw [ker_toClassGroup]
      exact Subgroup.mem_sup_right ⟨a, rfl⟩
    have ht : t = r * s * v := by dsimp [v]; group
    change f s = f t
    rw [ht, map_mul, map_mul, hr, hv', one_mul, mul_one]
  · intro h
    have hk : t * s⁻¹ ∈ f.ker := by
      change f (t * s⁻¹) = 1
      rw [map_mul, map_inv, show f t = f s from h.symm, mul_inv_cancel]
    rw [ker_toClassGroup, sup_comm, Subgroup.mem_sup] at hk
    obtain ⟨_, ⟨a, rfl⟩, v, hv, he⟩ := hk
    let r := unitEmbedding R F a
    have ht : t = r * s * v := by
      change r * v = t * s⁻¹ at he
      calc
        t = (t * s⁻¹) * s := by group
        _ = r * s * v := by rw [← he, mul_assoc, mul_comm v s, ← mul_assoc]
    refine ⟨j r, ⟨a, rfl⟩, z⁻¹ * j v * z, (hunit v).mpr hv, ?_⟩
    rw [ht, map_mul, map_mul]
    group

/-- An independently computed class-group parametrization of the adelic
orbit (tex 9150–9169). The argument never uses the map from CM points. -/
noncomputable def adelicOrbitEquivClassGroup (j : T →* G)
    (U : Subgroup G) (z : G)
    (hunit : ∀ s : T, z⁻¹ * j s * z ∈ U ↔ s ∈ integralUnits R F) :
    Set.range (torusOrbitMap j U z) ≃ ClassGroup R := by
  let pick := fun x : Set.range (torusOrbitMap j U z) => x.property.choose
  have hp (x : Set.range (torusOrbitMap j U z)) : torusOrbitMap j U z (pick x) = x.val :=
    x.property.choose_spec
  refine Equiv.ofBijective (fun x => toClassGroup R F (pick x)) ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    rw [← hp x, ← hp y]
    exact (torusOrbitMap_eq_iff j U z hunit _ _).mpr h
  · intro c
    obtain ⟨s, rfl⟩ := toClassGroup_surjective (R := R) (K := F) c
    refine ⟨⟨torusOrbitMap j U z s, ⟨s, rfl⟩⟩, ?_⟩
    exact (torusOrbitMap_eq_iff j U z hunit _ _).mp (hp _)

/-- In the orbit coordinates the representative `s z` has class `[s]`. -/
theorem adelicOrbitEquivClassGroup_apply (j : T →* G)
    (U : Subgroup G) (z : G)
    (hunit : ∀ s : T, z⁻¹ * j s * z ∈ U ↔ s ∈ integralUnits R F) (s : T) :
    adelicOrbitEquivClassGroup j U z hunit ⟨torusOrbitMap j U z s, ⟨s, rfl⟩⟩ =
      toClassGroup R F s := by
  apply (torusOrbitMap_eq_iff j U z hunit _ _).mp
  exact (show ∃ t, torusOrbitMap j U z t = torusOrbitMap j U z s from ⟨s, rfl⟩).choose_spec

end ZInQ.Manuscript.RC.HCMV21
