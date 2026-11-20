import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Module.LinearMap.End

/-! The linear algebra in the geometric right-ideal dictionary (tex
9150–9169 and 9273–9279). In covariant Hom coordinates a quotient
enlarges the target lattice; a positive ideal generator acts inversely. -/

namespace ZInQ.Manuscript.RC.HCMV21

section LeftOrder

variable {B : Type*} [Ring B]

/-- The left multipliers of the principal right ideal `g R` form
`g R g⁻¹`. This uses the generator itself and works over the division
algebra and over split matrix algebras. -/
theorem preserves_principalRightIdeal_iff (R : Subring B) (g : Bˣ) (x : B) :
    Set.MapsTo (fun y : B => x * y)
        ((fun r : B => (g : B) * r) '' (R : Set B))
        ((fun r : B => (g : B) * r) '' (R : Set B)) ↔
      (↑g⁻¹ : B) * x * (g : B) ∈ R := by
  constructor
  · intro h
    obtain ⟨r, hr, he⟩ := h (Set.mem_image_of_mem _ (R.one_mem : (1 : B) ∈ R))
    have he' : (g : B) * r = x * (g : B) := by simpa only [mul_one] using he
    rw [mul_assoc, ← he', ← mul_assoc, Units.inv_mul, one_mul]
    exact hr
  · intro h y hy
    obtain ⟨r, hr, rfl⟩ := hy
    refine ⟨((↑g⁻¹ : B) * x * (g : B)) * r, R.mul_mem h hr, ?_⟩
    simp only [← mul_assoc, Units.mul_inv, one_mul]

end LeftOrder

section Tate

variable {B k V : Type*} [Ring B] [CommRing k] [AddCommGroup V] [Module k V]

/-- The lattice of maps sending the source lattice to the target lattice
in a fixed rational Tate representation. -/
def latticeOfMaps (ρ : B →+* Module.End k V) (L₀ L : Set V) : Set B :=
  {b | Set.MapsTo (ρ b) L₀ L}

private theorem end_mul_apply (ρ : B →+* Module.End k V) (a b : B) (v : V) :
    ρ (a * b) v = ρ a (ρ b v) := by rw [map_mul]; rfl

private theorem end_unit_cancel (ρ : B →+* Module.End k V) (a : Bˣ) (v : V) :
    ρ (a : B) (ρ (↑a⁻¹ : B) v) = v := by
  rw [← end_mul_apply, Units.mul_inv, map_one]
  rfl

/-- For a principal local ideal, the preimage of its torsion in the
rational Tate space is the inverse translate of the original lattice.
The predicate uses all left multiples of the ideal generator. -/
theorem all_leftMultiples_map_iff (ρ : B →+* Module.End k V)
    (R : Subring B) (a : Bˣ) (L : Set V) (hL : ∀ r ∈ R, Set.MapsTo (ρ r) L L) (v : V) :
    (∀ r ∈ R, ρ (r * (a : B)) v ∈ L) ↔ v ∈ (ρ (↑a⁻¹ : B)) '' L := by
  constructor
  · intro h
    have hv : ρ (a : B) v ∈ L := by simpa only [one_mul] using h 1 R.one_mem
    exact ⟨_, hv, end_unit_cancel ρ a⁻¹ v⟩
  · rintro ⟨w, hw, rfl⟩ r hr
    rw [end_mul_apply, end_unit_cancel]
    exact hL r hr hw

/-- Replacing the target lattice by the inverse translate changes the
covariant Hom lattice by the same left inverse factor. -/
theorem latticeOfMaps_inverseTranslate (ρ : B →+* Module.End k V)
    (L₀ L : Set V) (a : Bˣ) :
    latticeOfMaps ρ L₀ ((ρ (↑a⁻¹ : B)) '' L) =
      (fun b : B => (↑a⁻¹ : B) * b) '' latticeOfMaps ρ L₀ L := by
  ext b
  constructor
  · intro hb
    refine ⟨(a : B) * b, ?_, ?_⟩
    swap
    · change (↑a⁻¹ : B) * ((a : B) * b) = b
      rw [← mul_assoc, Units.inv_mul, one_mul]
    intro v hv
    obtain ⟨w, hw, he⟩ := hb hv
    rw [end_mul_apply, ← he, end_unit_cancel]
    exact hw
  · rintro ⟨c, hc, rfl⟩ v hv
    exact ⟨ρ c v, hc hv, (end_mul_apply ρ _ _ v).symm⟩

/-- The inverse factor multiplies the chosen reference generator, even
when the reference lattice has a nontrivial local generator. -/
theorem latticeOfMaps_inverseTranslate_principal (ρ : B →+* Module.End k V)
    (L₀ L : Set V) (a g₀ : Bˣ) (R : Subring B)
    (h₀ : latticeOfMaps ρ L₀ L = (fun b : B => (g₀ : B) * b) '' (R : Set B)) :
    latticeOfMaps ρ L₀ ((ρ (↑a⁻¹ : B)) '' L) =
      (fun b : B => (↑(a⁻¹ * g₀) : B) * b) '' (R : Set B) := by
  rw [latticeOfMaps_inverseTranslate, h₀, Set.image_image]
  simp only [Units.val_mul, mul_assoc]

end Tate

end ZInQ.Manuscript.RC.HCMV21
