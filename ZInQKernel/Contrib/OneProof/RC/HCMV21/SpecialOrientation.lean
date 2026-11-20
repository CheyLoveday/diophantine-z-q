import ZInQKernel.Contrib.OneProof.RC.HCMV21.ResidueCharacter
import Mathlib.FieldTheory.Finite.Basic

/-! The orientation is the character on the special tangent line. The
scalar of an étale isogeny on this line is a unit, so it can be cancelled. -/

namespace ZInQ.Manuscript.RC.HCMV21
open scoped Polynomial

variable {R V k : Type*} [CommRing R] [CommRing V] [IsLocalRing V] [Field k]

/-- The actual residue character over the geometric residue field, via
the residue embedding for the fixed place. -/
noncomputable def geometricResidueCharacter (q : ℕ) [CharP (IsLocalRing.ResidueField V) q]
    (ρ : R →+* V) (i : IsLocalRing.ResidueField V →+* k) :
    R ⧸ Ideal.span {(q : R)} →+* k :=
  i.comp (residueCharacter q ρ)

/-- Pullback of invariant differentials along a labelled isogeny
intertwines the two characters. A nonzero special pullback scalar
forces equality on the whole order modulo `q`. -/
theorem geometricResidueCharacter_eq_of_intertwines (q : ℕ)
    [CharP (IsLocalRing.ResidueField V) q] (ρ σ : R →+* V)
    (i : IsLocalRing.ResidueField V →+* k) (u : k) (hu : u ≠ 0)
    (h : ∀ a, i (IsLocalRing.residue V (ρ a)) * u =
      i (IsLocalRing.residue V (σ a)) * u) :
    geometricResidueCharacter q ρ i = geometricResidueCharacter q σ i := by
  ext x
  exact mul_right_cancel₀ hu (h x)

/-- The Frobenius twist switches orientation when the residue order has
`q²` elements. In particular the two embeddings do not arise as
different images of quotients preserving the same character. -/
theorem frobenius_comp_ne_of_card_sq {S : Type*} [Field S] [Fintype S]
    (q : ℕ) [Fact q.Prime] [CharP k q] (r : S →+* k)
    (hcard : Fintype.card S = q ^ 2) :
    (frobenius k q).comp r ≠ r := by
  intro h
  classical
  have hroot (x : S) : Polynomial.IsRoot (Polynomial.X ^ q - Polynomial.X : k[X]) (r x) := by
    have he := RingHom.congr_fun h x
    simpa [Polynomial.IsRoot, frobenius_def, sub_eq_zero] using he
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  have hle := Polynomial.card_le_degree_of_subset_roots
    (Z := (Finset.univ : Finset S).map ⟨r, r.injective⟩)
    (p := (Polynomial.X ^ q - Polynomial.X : k[X])) (by
      intro x hx
      obtain ⟨s, -, rfl⟩ := Finset.mem_map.mp hx
      simpa [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero k hq)] using hroot s)
  rw [Finset.card_map, Finset.card_univ, hcard,
    FiniteField.X_pow_card_sub_X_natDegree_eq k hq] at hle
  nlinarith

end ZInQ.Manuscript.RC.HCMV21
