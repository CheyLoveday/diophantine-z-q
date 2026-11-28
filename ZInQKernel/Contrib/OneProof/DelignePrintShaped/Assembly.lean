import ZInQKernel.Contrib.OneProof.DelignePrintShaped.LevelOnto
import ZInQKernel.Contrib.OneProof.DelignePrintShaped.LevelClass

/-! # The row `deligneCanonicalModelY3EveryPrint`: assembly

* **B2.1 in full** (`moduli_clauses_of_prints`): from T2a (Voight), T2c′ (Boutot–Carayol, Prop. 1.5 over `ℂ`) and the
  existing textbook field `ZInQ.HomLattice.GAGAMorphism`, on every `ℚ`-scheme `Y` with moduli bijections `Φ`, the map
  `Ψ := (Φ ℂ)⁻¹ ∘ [X]` (`X(z, g)` the moduli object of `[z, g]`) is onto, has fibres exactly the double cosets
  `B^× \ (ℍ^± × (B ⊗ 𝔸_f)^× / K₃)` (both directions; in particular at CM points), and satisfies the moduli clause
  in the print's `H₁` form at `g = 1` and at every `u ∈ 𝒪̂^×`. No model identification and no GLUE is used.
* **The discharge** (`deligneCanonicalModelY3EveryPrint_of_prints`, in the bridges file) needs, in addition,
  T2b (Cornut–Vatsal) and the GLUE W-a, for holomorphy and the reciprocity law.
* `moduli_map_eq_of_glue`: under W-a the two descriptions agree: the uniformization `f⁻¹ ∘ ψ` of the discharge is the
  moduli map of B2.1.
-/

set_option autoImplicit false

noncomputable section

namespace DelignePS

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open ShimuraCFT RayClassCFT
open Y3Hodge (HPM DCRelPM toPM)

/-- **B2.1 in full.** The complex clauses of the row on every `ℚ`-scheme with moduli bijections, from T2a, T2c′ and
the textbook field `GAGAMorphism` (through `levelOnto_of` and `levelClassification_of`). -/
theorem moduli_clauses_of_prints (hV : VoightQMComplexModuliPrint) (hP : BoutotCarayolPolarizationPrint)
    (hG : ZInQ.HomLattice.GAGAMorphism) (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) :
    ∃ Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y),
      (∀ y : fieldPt ℂ ⟶ Y, ∃ z g, Ψ z g = y) ∧
      (∀ z g z' g', Ψ z g = Ψ z' g' ↔ DCRelPM z g z' g') ∧
      (∀ (z : HPM) (g : BAQˣ) (P : QML3 ℂ), IsLevelPoint P z g → Φ ℂ (Ψ z g) = M3.mk P) ∧
      (∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (Ψ (toPM τ) 1) = M3.mk P ∧ Y3Hodge.IsHodgeH1Print P τ) ∧
      Y3Hodge.ModuliAtUnitsHP Y Φ Ψ :=
  moduli_clauses_of_print hV (levelOnto_of hV hP) (levelClassification_of hG) Y Φ

/-- **The two descriptions agree.** If `Ψ` sends every point to the class of its moduli object (as the map of
B2.1 does), and W-a's isomorphism `f` carries moduli points to `ψ`, then `ψ = f ∘ Ψ`. -/
theorem moduli_map_eq_of_glue (hV : VoightQMComplexModuliPrint) {Y M : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ M)} {f : Y ≅ M}
    (hf : ∀ (z : HPM) (g : BAQˣ) (P : QML3 ℂ), IsLevelPoint P z g → ψ z g = (Φ ℂ).symm (M3.mk P) ≫ f.hom)
    {Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)}
    (hΨ : ∀ (z : HPM) (g : BAQˣ) (P : QML3 ℂ), IsLevelPoint P z g → Φ ℂ (Ψ z g) = M3.mk P)
    (z : HPM) (g : BAQˣ) : ψ z g = Ψ z g ≫ f.hom := by
  obtain ⟨P, hP⟩ := exists_levelPoint hV z g
  rw [hf z g P hP, ← hΨ z g P hP, Equiv.symm_apply_apply]

end DelignePS
