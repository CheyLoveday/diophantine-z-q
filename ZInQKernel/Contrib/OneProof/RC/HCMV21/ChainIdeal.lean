import ZInQKernel.Contrib.OneProof.RC.HCMV21.RightIdealCoordinates

/-! Local principality in common rational coordinates on the two
level chains. This calculation is valid at every split prime, including
two. The level orientations are then those on the chain stabilizer. -/

namespace ZInQ.Manuscript.RC.HCMV21

section Chains

variable {B K V : Type*} [Ring B] [CommRing K] [AddCommGroup V] [Module K V]

/-- A map of lattice chains is integral at both ends of the level
isogeny. All sets are in one rational representation. -/
def latticeChainMaps (ρ : B →+* Module.End K V) (L₁ L₂ M₁ M₂ : Set V) : Set B :=
  latticeOfMaps ρ L₁ M₁ ∩ latticeOfMaps ρ L₂ M₂

/-- A simultaneous change of basis in the target level chain multiplies
the two-lattice Hom group on the left by that change of basis. -/
theorem latticeChainMaps_translate (ρ : B →+* Module.End K V) (g : Bˣ) (L₁ L₂ : Set V) :
    latticeChainMaps ρ L₁ L₂ (ρ (g : B) '' L₁) (ρ (g : B) '' L₂) =
      (fun x : B => (g : B) * x) '' latticeChainMaps ρ L₁ L₂ L₁ L₂ := by
  unfold latticeChainMaps
  rw [show ρ (g : B) '' L₁ = ρ (↑(g⁻¹)⁻¹ : B) '' L₁ by rw [inv_inv],
    show ρ (g : B) '' L₂ = ρ (↑(g⁻¹)⁻¹ : B) '' L₂ by rw [inv_inv],
    latticeOfMaps_inverseTranslate, latticeOfMaps_inverseTranslate]
  simp only [inv_inv]
  exact (Set.image_inter (Units.mulLeft_bijective g).injective).symm

/-- Once the two actual chains are expressed in matching cyclic-chain
bases, their enhanced Hom lattice is principal over the source
stabilizer ring. -/
theorem latticeChainMaps_eq_principal (ρ : B →+* Module.End K V)
    (R : Subring B) (g : Bˣ) (L₁ L₂ M₁ M₂ : Set V)
    (h₁ : M₁ = ρ (g : B) '' L₁) (h₂ : M₂ = ρ (g : B) '' L₂)
    (hR : latticeChainMaps ρ L₁ L₂ L₁ L₂ = (R : Set B)) :
    latticeChainMaps ρ L₁ L₂ M₁ M₂ = (fun x : B => (g : B) * x) '' (R : Set B) := by
  rw [h₁, h₂, latticeChainMaps_translate, hR]

/-- The left order of that Hom lattice is exactly the stabilizer
of the target chain. -/
theorem mapsTo_latticeChainMaps_iff (ρ : B →+* Module.End K V)
    (L₁ L₂ M₁ M₂ : Set V) (g : Bˣ)
    (h₁ : M₁ = ρ (g : B) '' L₁) (h₂ : M₂ = ρ (g : B) '' L₂) (b : B) :
    Set.MapsTo (fun x : B => b * x) (latticeChainMaps ρ L₁ L₂ M₁ M₂)
        (latticeChainMaps ρ L₁ L₂ M₁ M₂) ↔
      b ∈ latticeChainMaps ρ M₁ M₂ M₁ M₂ := by
  constructor
  · intro hb
    have hg : (g : B) ∈ latticeChainMaps ρ L₁ L₂ M₁ M₂ := by
      rw [h₁, h₂]
      exact ⟨fun x hx => ⟨x, hx, rfl⟩, fun x hx => ⟨x, hx, rfl⟩⟩
    have hbg := hb hg
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := h₁ ▸ hx
      have hy' := hbg.1 hy
      rwa [map_mul] at hy'
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := h₂ ▸ hx
      have hy' := hbg.2 hy
      rwa [map_mul] at hy'
  · rintro ⟨h₁', h₂'⟩ x ⟨hx₁, hx₂⟩
    exact ⟨fun y hy => by rw [map_mul]; exact h₁' (hx₁ hy),
      fun y hy => by rw [map_mul]; exact h₂' (hx₂ hy)⟩

end Chains

end ZInQ.Manuscript.RC.HCMV21
