import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map

/-!
# Duality area: the universal quadratic character is trivial at the old places

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-local-kummer`, tex L3427–3434:

> In the universal binary family every `h_x` has the same local squareclasses at `2N` as
> `h_0 = 1`. Hence every sign character evaluates the universal character `ε` trivially on
> `G_{K_v}`, and therefore `ε|_{G_{K_v}} = 1` in `G`, before reduction modulo two.

The universal character `ε : G_K → G` records the action of `σ` on the square roots `√h` of the
discriminants of the family; it is trivial on the decomposition group `G_{K_v}` (the image of
`G_{K_v} → G_K` along an embedding of separable closures, `TauCeti.absoluteGaloisGroupMap`)
exactly when that group fixes every `√h`. This file proves that it does as soon as every `h` is
a square in `K_v`:

* `absoluteGaloisGroupMap_fixes_sqrt`: if `α² = a ∈ K` and `a` is a square in the extension
  `L`, every element of the image of `G_L` fixes `α`;
* `LocalSquareclassNode` (PROVED): for a family `h_j ∈ K` of local squares at `L = K_v` with
  chosen square roots `α_j ∈ Kˢ`, the decomposition group fixes every `α_j`, i.e. every quadratic
  character `σ ↦ σ(α_j)/α_j`, and hence `ε`, is trivial on `G_{K_v}`.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Duality

open TauCeti

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]

/-- If `α² = a` with `a ∈ K` a square in `L`, then `G_L` (through an embedding `τ` of separable
closures) fixes `α`. -/
theorem absoluteGaloisGroupMap_fixes_sqrt (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
    (a : K) (α : SeparableClosure K) (hα : α ^ 2 = algebraMap K (SeparableClosure K) a)
    (hsq : IsSquare (algebraMap K L a)) (g : AbsoluteGaloisGroup L) :
    absoluteGaloisGroupMap τ g α = α := by
  obtain ⟨b, hb⟩ := hsq
  set β : SeparableClosure L := algebraMap L (SeparableClosure L) b with hβ
  have hτα : τ α ^ 2 = β ^ 2 := by
    rw [← map_pow, hα, AlgHom.commutes, hβ, ← map_pow, sq, ← hb,
      IsScalarTower.algebraMap_apply K L (SeparableClosure L)]
  have hgβ : g β = β := g.commutes b
  have hfix : g (τ α) = τ α := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hτα with h | h
    · rw [h, hgβ]
    · rw [h, map_neg, hgβ]
  apply τ.toRingHom.injective
  change τ (absoluteGaloisGroupMap τ g α) = τ α
  rw [absoluteGaloisGroupMap_commutes, hfix]

/-- **The universal character is trivial at the old places** (proof of `ex:arith-local-kummer`,
tex L3427–3434). Let `K` be a field, `L = K_v` an extension with an embedding of separable
closures `τ`, and `(h_j)` a family of elements of `K` (the discriminants of the binary family)
each of which is a square in `L` ("the same local squareclass as `h_0 = 1`"), with square roots
`α_j ∈ Kˢ`. Then every element of the decomposition group `G_L → G_K` fixes every `α_j`: each
quadratic character `σ ↦ σ(α_j)/α_j`, and hence the universal character `ε`, is trivial on
`G_{K_v}`. -/
def LocalSquareclassNode : Prop :=
  ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L) (ι : Type) (h : ι → K)
    (α : ι → SeparableClosure K),
    (∀ j, α j ^ 2 = algebraMap K (SeparableClosure K) (h j)) →
    (∀ j, IsSquare (algebraMap K L (h j))) →
    ∀ (g : AbsoluteGaloisGroup L) (j : ι), absoluteGaloisGroupMap τ g (α j) = α j

theorem localSquareclassNode_proof : LocalSquareclassNode := by
  intro K _ L _ _ τ ι h α hα hsq g j
  exact absoluteGaloisGroupMap_fixes_sqrt τ (h j) (α j) (hα j) (hsq j) g

end ZInQ.Contrib.CloudB3RC53.Duality
