import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.CharP.Defs

namespace ZInQ.Manuscript.RC.HCMV21

variable {R O : Type*} [CommRing R] [CommRing O] [IsLocalRing O]

/-- The scalar action on the special tangent line, obtained by reducing the
integral scalar action. It factors through the order modulo the residue prime. -/
noncomputable def residueCharacter (q : ℕ) [CharP (IsLocalRing.ResidueField O) q] (ρ : R →+* O) :
    R ⧸ Ideal.span {(q : R)} →+* IsLocalRing.ResidueField O :=
  Ideal.Quotient.lift _ ((IsLocalRing.residue O).comp ρ) fun x hx => by
    have hle : Ideal.span {(q : R)} ≤ RingHom.ker ((IsLocalRing.residue O).comp ρ) := by
      rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    exact hle hx

@[simp]
theorem residueCharacter_mk (q : ℕ) [CharP (IsLocalRing.ResidueField O) q]
    (ρ : R →+* O) (x : R) :
    residueCharacter q ρ (Ideal.Quotient.mk _ x) = IsLocalRing.residue O (ρ x) :=
  rfl

/-- If `(q)` is maximal, the residue character embeds the quadratic residue
field; reducing two integral actions that have the same generic scalar cannot
switch that embedding. -/
theorem residueCharacter_injective (q : ℕ) [CharP (IsLocalRing.ResidueField O) q]
    [(Ideal.span {(q : R)}).IsMaximal] (ρ : R →+* O) :
    Function.Injective (residueCharacter q ρ) := by
  let := Ideal.Quotient.field (Ideal.span {(q : R)})
  exact (residueCharacter q ρ).injective

/-- If two integral scalar actions agree after passage to the generic field,
the induced residue characters agree at the same place. -/
theorem residueCharacter_eq_of_generic_eq {K : Type*} [Field K] (j : O →+* K)
    (hj : Function.Injective j) (q : ℕ) [CharP (IsLocalRing.ResidueField O) q]
    (ρ σ : R →+* O) (h : j.comp ρ = j.comp σ) :
    residueCharacter q ρ = residueCharacter q σ := by
  congr 1
  ext x
  exact hj (RingHom.congr_fun h x)

end ZInQ.Manuscript.RC.HCMV21
