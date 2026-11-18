import Mathlib

/-!
# Genus bound, setup: the conjugation of an imaginary quadratic field

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:limits-residual-bound`, tex 4494–4517 (the
class-group inequality of (5.1b), "the imaginary quadratic genus argument"). This file fixes, for a
number field `K` of degree two, the nontrivial automorphism `σ = conjAut` ("conjugation"), and
proves the elementary facts used throughout: `σ² = 1`, every automorphism is `1` or `σ`, the
elements fixed by `σ` are rational, `N_{K/ℚ}(x) = x σ(x)`, and, for `K` imaginary (totally complex),
`x σ(x)` is a positive rational for `x ≠ 0` ("this norm is positive", tex 4500–4501). It also records
how `σ` acts on ideals of `𝒪_K` (Mathlib's pointwise action of `Gal(K/ℚ)`). Kinds: PROVED.
-/

noncomputable section

open NumberField Pointwise

namespace ZInQ.Contrib.CloudB3RC53.RankCounts.Genus

variable {K : Type} [Field K] [NumberField K]

theorem isGalois_of_finrank_two (hK2 : Module.finrank ℚ K = 2) : IsGalois ℚ K :=
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK2⟩
  inferInstance

theorem card_aut (hK2 : Module.finrank ℚ K = 2) : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
  have := isGalois_of_finrank_two hK2
  rw [IsGalois.card_aut_eq_finrank, hK2]

theorem exists_ne_one (hK2 : Module.finrank ℚ K = 2) : ∃ g : K ≃ₐ[ℚ] K, g ≠ 1 := by
  by_contra h
  push Not at h
  have : Subsingleton (K ≃ₐ[ℚ] K) := ⟨fun a b => (h a).trans (h b).symm⟩
  have := card_aut hK2
  rw [Nat.card_unique] at this
  omega

/-- The nontrivial automorphism of the quadratic field `K` ("conjugation", tex 4497). -/
def conjAut (hK2 : Module.finrank ℚ K = 2) : K ≃ₐ[ℚ] K := (exists_ne_one hK2).choose

theorem conjAut_ne_one (hK2 : Module.finrank ℚ K = 2) : conjAut hK2 ≠ 1 :=
  (exists_ne_one hK2).choose_spec

/-- Every automorphism of `K` is `1` or `σ`. -/
theorem eq_one_or_eq_conjAut (hK2 : Module.finrank ℚ K = 2) (g : K ≃ₐ[ℚ] K) :
    g = 1 ∨ g = conjAut hK2 := by
  classical
  have hc := card_aut hK2
  let _ : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hc
  by_contra h
  push Not at h
  have : ({1, conjAut hK2, g} : Finset (K ≃ₐ[ℚ] K)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h.2)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(conjAut_ne_one hK2).symm, h.1.symm⟩
  have := Finset.card_le_univ ({1, conjAut hK2, g} : Finset (K ≃ₐ[ℚ] K))
  omega

/-- `σ² = 1`. -/
theorem conjAut_mul_self (hK2 : Module.finrank ℚ K = 2) : conjAut hK2 * conjAut hK2 = 1 := by
  rcases eq_one_or_eq_conjAut hK2 (conjAut hK2 * conjAut hK2) with h | h
  · exact h
  · exfalso
    exact conjAut_ne_one hK2 (mul_left_cancel (h.trans (mul_one _).symm))

theorem conjAut_conjAut (hK2 : Module.finrank ℚ K = 2) (x : K) :
    conjAut hK2 (conjAut hK2 x) = x := by
  have := congrArg (fun g : K ≃ₐ[ℚ] K => g x) (conjAut_mul_self hK2)
  simpa using this

/-- Elements fixed by `σ` are rational. -/
theorem exists_rat_of_conjAut_eq (hK2 : Module.finrank ℚ K = 2) {x : K}
    (hx : conjAut hK2 x = x) : ∃ q : ℚ, x = algebraMap ℚ K q := by
  have := isGalois_of_finrank_two hK2
  have hmem : x ∈ IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[ℚ] K)) := by
    rintro ⟨g, -⟩
    rcases eq_one_or_eq_conjAut hK2 g with rfl | rfl
    · rfl
    · exact hx
  rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, hq.symm⟩

/-- `N_{K/ℚ}(x) = x σ(x)`. -/
theorem norm_eq_mul_conjAut (hK2 : Module.finrank ℚ K = 2) (x : K) :
    algebraMap ℚ K (Algebra.norm ℚ x) = x * conjAut hK2 x := by
  classical
  have := isGalois_of_finrank_two hK2
  rw [Algebra.norm_eq_prod_automorphisms]
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, conjAut hK2} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact eq_one_or_eq_conjAut hK2 g
  rw [huniv, Finset.prod_pair (conjAut_ne_one hK2).symm]
  rfl

/-- The ring embeddings `K → ℂ` of an imaginary quadratic field are an embedding and its complex
conjugate. -/
theorem embeddings_eq (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (φ ψ : K →+* ℂ) :
    ψ = φ ∨ ψ = ComplexEmbedding.conjugate φ := by
  classical
  have hcard : Fintype.card (K →+* ℂ) = 2 := by rw [Embeddings.card, hK2]
  have hφ : ComplexEmbedding.conjugate φ ≠ φ := by
    intro h
    have hreal : (InfinitePlace.mk φ).IsReal :=
      InfinitePlace.isReal_mk_iff.mpr (ComplexEmbedding.isReal_iff.mpr h)
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex _)) hreal
  by_contra hne
  push Not at hne
  have : ({φ, ComplexEmbedding.conjugate φ, ψ} : Finset (K →+* ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hne.2)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hφ.symm, (hne.1).symm⟩
  have := Finset.card_le_univ ({φ, ComplexEmbedding.conjugate φ, ψ} : Finset (K →+* ℂ))
  omega

/-- **The norm of a nonzero element of an imaginary quadratic field is positive** (tex 4500–4501,
"since this norm is positive"). -/
theorem norm_pos (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) {x : K} (hx : x ≠ 0) :
    0 < Algebra.norm ℚ x := by
  classical
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hcard : Fintype.card (K →+* ℂ) = 2 := by rw [Embeddings.card, hK2]
  have hφ : ComplexEmbedding.conjugate φ ≠ φ := by
    intro h
    have : (InfinitePlace.mk φ).IsReal :=
      InfinitePlace.isReal_mk_iff.mpr (ComplexEmbedding.isReal_iff.mpr h)
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex _)) this
  have huniv : (Finset.univ : Finset (K →+* ℂ)) = {φ, ComplexEmbedding.conjugate φ} := by
    ext ψ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact embeddings_eq hK2 hTC φ ψ
  have hN := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have hprod : ∏ σ : K →ₐ[ℚ] ℂ, σ x = φ x * starRingEnd ℂ (φ x) := by
    rw [← Equiv.prod_comp (RingHom.equivRatAlgHom (R := K) (S := ℂ)) (fun σ : K →ₐ[ℚ] ℂ => σ x)]
    change ∏ ψ : K →+* ℂ, ψ x = _
    rw [huniv, Finset.prod_pair hφ.symm]
    rfl
  rw [hprod, Complex.mul_conj] at hN
  have hφx : φ x ≠ 0 := (map_ne_zero φ).mpr hx
  have hpos : (0 : ℝ) < Complex.normSq (φ x) := Complex.normSq_pos.mpr hφx
  have : ((Algebra.norm ℚ x : ℚ) : ℝ) = Complex.normSq (φ x) := by
    have := congrArg Complex.re hN
    simpa using this
  exact_mod_cast this ▸ hpos

/-- `x σ(x)` is a positive rational for `x ≠ 0` in an imaginary quadratic field. -/
theorem mul_conjAut_pos (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) {x : K}
    (hx : x ≠ 0) : ∃ q : ℚ, 0 < q ∧ x * conjAut hK2 x = algebraMap ℚ K q :=
  ⟨Algebra.norm ℚ x, norm_pos hK2 hTC hx, (norm_eq_mul_conjAut hK2 x).symm⟩

end ZInQ.Contrib.CloudB3RC53.RankCounts.Genus
