import ZInQKernel.Contrib.G9.I4Layer

/-!
# Milne, *Abelian Varieties*, Theorem 7.1: every abelian variety is projective

The printed leaf `MilneThm71Projective`: an abelian variety `A` over a field `K` (in the form
`ZInQ.Contrib.G9.PkgI4.I3.AbVar K`) admits a closed immersion over `Spec K` into
`ℙᴺ_ℤ ×_{Spec ℤ} Spec K` for some `N` (canonically isomorphic to `ℙᴺ_K` over `K`, EGA II
(4.1.3.1)). Here `ℙᴺ_ℤ` is `projSpaceZ N`, the `Proj` of `ℤ[x_0, …, x_N]` with the total-degree
grading, and both maps to `Spec ℤ` are the unique ones (`Spec ℤ` is terminal). It is the only
input of the construction of a proper model of `A` over the ring of integers of a finite
extension of `ℚ_p` (`MilneModel.lean`).
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.ColmezProperModel

/- The total-degree grading of `MvPolynomial σ R` is the Mathlib definition
`MvPolynomial.gradedAlgebra`; it is used here as a local instance. -/
attribute [local instance] MvPolynomial.gradedAlgebra

/-- **`ℙᴺ_ℤ = Proj ℤ[x_0, …, x_N]`**, the `Proj` of the polynomial ring
`S_ℤ(ℤ^{N+1}) = ℤ[x_0, …, x_N]` in `N + 1` variables over `ℤ`, graded by total degree (EGA II
(4.1.1)). It is the same scheme as the projective space over `ℤ` used for the level-three moduli
rows (the `Proj` of the same graded ring). -/
noncomputable abbrev projSpaceZ (N : ℕ) : Scheme.{0} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ)

/-- **Milne, Theorem 7.1** (every abelian variety is projective), in the form: for every field
`K` and every abelian variety `A` over `K`, there are `N` and a closed immersion
`i : A ⟶ ℙᴺ_ℤ ×_{Spec ℤ} Spec K` over `Spec K`, where `ℙᴺ_ℤ = projSpaceZ N = Proj ℤ[x_0, …, x_N]`
and `ℙᴺ_ℤ ×_{Spec ℤ} Spec K ≅ ℙᴺ_K`, canonically over `K` (EGA II (4.1.3.1)).

Print: J. S. Milne, *Abelian Varieties*, in *Arithmetic Geometry* (Storrs 1984), Springer 1986,
§7 "Abelian Varieties Are Projective", p. 10 of the author's retyped edition: "THEOREM 7.1. Every
abelian variety is projective." The retyped edition records corrections, so both the wording and
the page of the 1986 printing are unchecked.

* Milne's definition (p. 10, in the proof): "Recall (Hartshorne 1977, II, 7.8.2) that a variety
  is projective if it has a very ample linear system, and that a linear system 𝔡 is very ample if:
  (a) it separates points … (b) it separates tangent vectors …" (p. 11). In (b) the tangent
  vectors are the nonzero ones. In Milne, `L(D)` is already `H⁰(V, ℒ(D))` (p. 10). A very ample
  complete linear system `|D|` gives a closed immersion into `ℙ(L(D)) ≅ ℙᴺ_k` over `k`, choosing
  a basis of `L(D)` (Hartshorne II 7.1, 7.8.2; background; the convention for `ℙ(·)` is
  immaterial).
* The ground field is not assumed algebraically closed. p. 11: "(a) Let D be a divisor on A; if
  |D_k̄| is very ample, then so also is |D|. (The map A_k̄ ↪ ℙⁿ defined by |D_k̄| is obtained by
  base change from that defined by |D|.)"
* p. 2 (Conventions): "All statements are relative to a fixed ground field: if V and W are
  varieties over k, then a sheaf of divisor [sic] on V, or a morphism V → W is automatically meant
  to be defined over k", so the immersion is over `k`. p. 2: "A variety V over k is a separated
  scheme of finite type over k such that V_k̄ is integral". p. 3: "A complete connected group
  variety is called an abelian variety." So every `AbVar K` (a group object over `Spec K` whose
  structure morphism is proper, smooth and geometrically integral) is an abelian variety in
  Milne's sense: properness gives separated, universally closed (hence quasi-compact, Stacks 04XU;
  background) and locally of finite type, so of finite type and complete; geometric integrality
  gives `V_k̄` integral, hence connected. Smoothness is not needed (p. 3: "A group variety is
  automatically nonsingular").
* `ℙᴺ_k ≅ ℙᴺ_ℤ ×_{Spec ℤ} Spec k`, canonically over `k`: EGA II (4.1.1), (4.1.3.1), with
  `ℙᴺ_ℤ = Proj S_ℤ(ℤ^{N+1})` and `S_ℤ(ℤ^{N+1}) = ℤ[x_0, …, x_N]` graded by total degree
  (background). Milne's "projective" (a very ample linear system) gives a closed immersion into
  some `ℙᴺ_k` over `k` (Hartshorne II 7.1, 7.8.2; background); EGA II (5.5.4)(ii) is not needed.

Fidelity: the statement is for fields `K : Type` only and asks only for the existence of `N` and
of the closed immersion over `Spec K` (no linear system is recorded), so it is weaker than or equal
to the print. -/
def MilneThm71Projective : Prop :=
  ∀ (K : Type) [Field K] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar K),
    ∃ (N : ℕ) (i : A.X.left ⟶ pullback (specZIsTerminal.from (projSpaceZ N))
        (specZIsTerminal.from (Spec (CommRingCat.of K)))),
      IsClosedImmersion i ∧ i ≫ pullback.snd _ _ = A.X.hom

end ZInQ.Contrib.ColmezProperModel
