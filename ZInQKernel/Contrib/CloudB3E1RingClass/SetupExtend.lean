import ZInQKernel.Contrib.CloudB3E1RingClass.Complete

/-!
# Extending prescribed split pairs by class-group generators

Manuscript `diophantine_zq.tex`, tex 3528–3534: "to the active and `2N` pairs adjoin split pairs
whose classes generate `Cl(K)`, over further distinct rational primes".

`exists_extended_setup` starts from prescribed split pairs `(𝔭⁰_j, 𝔭̄⁰_j)` over pairwise distinct
rational primes `p⁰_j` and a finite set `T` of primes to avoid. It returns a `RingClassSetup` whose
first `S₀` pairs are the prescribed ones, with further pairs outside `T` such that:
* all rational primes are pairwise distinct;
* `𝔭_j ≠ 𝔭̄_j` for every pair;
* the classes `[𝔭_j]` generate `Cl(K)`;
* `placeR r` lies over `r`.

These are the setup facts `hinj`, `hne`, `hgen` and `placeR_over` of `GenuineMovingComplete`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- A prime containing `p`, where `p𝒪_K = PQ`, is `P` or `Q`. Kind: PROVED. -/
theorem eq_or_eq_of_mem_split {w P Q : HeightOneSpectrum (𝓞 K)} {p : ℤ}
    (hmul : P.asIdeal * Q.asIdeal = Ideal.span {(p : 𝓞 K)}) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    w = P ∨ w = Q := by
  have hle : P.asIdeal * Q.asIdeal ≤ w.asIdeal := by
    rw [hmul, Ideal.span_le, Set.singleton_subset_iff]; exact hw
  rcases w.isPrime.mul_le.mp hle with h | h
  · exact Or.inl (HeightOneSpectrum.ext (P.isMaximal.eq_of_le w.isPrime.ne_top h).symm)
  · exact Or.inr (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le w.isPrime.ne_top h).symm)

/-- **Extending prescribed split pairs by generators of `Cl(K)`** (tex 3528–3534). Kind: PROVED. -/
theorem exists_extended_setup (hK : Module.finrank ℚ K = 2) {S₀ : ℕ}
    (P₀ Q₀ : Fin S₀ → HeightOneSpectrum (𝓞 K)) (p₀ : Fin S₀ → ℕ) (hp₀ : ∀ j, (p₀ j).Prime)
    (hinj₀ : Function.Injective p₀) (hne₀ : ∀ j, P₀ j ≠ Q₀ j)
    (hmul₀ : ∀ j, (P₀ j).asIdeal * (Q₀ j).asIdeal = Ideal.span {(((p₀ j : ℤ)) : 𝓞 K)})
    (T : Finset (HeightOneSpectrum (𝓞 K))) (Ssupp : Set (HeightOneSpectrum (𝓞 K)))
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ∃ (S₁ : ℕ) (C : RingClassSetup K (S₀ + S₁)),
      (∀ j, C.𝔭 (Fin.castAdd S₁ j) = P₀ j ∧ C.𝔭bar (Fin.castAdd S₁ j) = Q₀ j ∧
        C.p (Fin.castAdd S₁ j) = p₀ j) ∧
      (∀ k, C.𝔭 (Fin.natAdd S₀ k) ∉ T ∧ C.𝔭bar (Fin.natAdd S₀ k) ∉ T) ∧
      Function.Injective C.p ∧ (∀ j, C.𝔭 j ≠ C.𝔭bar j) ∧
      Subgroup.closure (Set.range fun j =>
        ClassGroup.mk0 ⟨(C.𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot⟩) = ⊤ ∧
      ∀ r, r.Prime → ((r : ℤ) : 𝓞 K) ∈ (C.placeR r).asIdeal := by
  classical
  let T' := T ∪ Finset.univ.image P₀ ∪ Finset.univ.image Q₀
  obtain ⟨S₁, P₁, Q₁, p₁, hp₁, hinj₁, hne₁, hT₁, hmul₁, hcl₁⟩ :=
    exists_split_generators_distinct hK T'
  have hp : ∀ j, (Fin.append p₀ p₁ j).Prime := fun j => by
    refine Fin.addCases (fun j => ?_) (fun k => ?_) j
    · rw [Fin.append_left]; exact hp₀ j
    · rw [Fin.append_right]; exact hp₁ k
  have hmul : ∀ j, (Fin.append P₀ P₁ j).asIdeal * (Fin.append Q₀ Q₁ j).asIdeal =
      Ideal.span {(((Fin.append p₀ p₁ j : ℕ) : ℤ) : 𝓞 K)} := fun j => by
    induction j using Fin.addCases with
    | left j => rw [Fin.append_left, Fin.append_left, Fin.append_left]; exact hmul₀ j
    | right k => rw [Fin.append_right, Fin.append_right, Fin.append_right]; exact hmul₁ k
  let C := RingClassSetup.mk' (Fin.append P₀ P₁) (Fin.append Q₀ Q₁) (Fin.append p₀ p₁) hp hmul
    Ssupp w₀
  -- the new rational primes avoid the prescribed ones
  have hdisj : ∀ j k, p₁ k ≠ p₀ j := by
    intro j k h
    have hmem : (((p₀ j : ℤ)) : 𝓞 K) ∈ (P₁ k).asIdeal := by
      have hm : (((p₁ k : ℤ)) : 𝓞 K) ∈ (P₁ k).asIdeal * (Q₁ k).asIdeal := by
        rw [hmul₁ k]; exact Ideal.mem_span_singleton_self _
      have := Ideal.mul_le_left (I := (P₁ k).asIdeal) (J := (Q₁ k).asIdeal) hm
      rwa [h] at this
    rcases eq_or_eq_of_mem_split (hmul₀ j) hmem with h' | h'
    · exact (hT₁ k).1 (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h'.symm⟩)))
    · exact (hT₁ k).1 (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h'.symm⟩))
  refine ⟨S₁, C, fun j => ⟨Fin.append_left _ _ j, Fin.append_left _ _ j, Fin.append_left _ _ j⟩,
    fun k => ?_, ?_, ?_, ?_, fun r hr => placeR_over' hr⟩
  · change Fin.append P₀ P₁ (Fin.natAdd S₀ k) ∉ T ∧ Fin.append Q₀ Q₁ (Fin.natAdd S₀ k) ∉ T
    rw [Fin.append_right, Fin.append_right]
    exact ⟨fun h => (hT₁ k).1 (Finset.mem_union_left _ (Finset.mem_union_left _ h)),
      fun h => (hT₁ k).2 (Finset.mem_union_left _ (Finset.mem_union_left _ h))⟩
  · intro a b hab
    change Fin.append p₀ p₁ a = Fin.append p₀ p₁ b at hab
    revert hab
    refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;>
      refine Fin.addCases (fun i' => ?_) (fun i' => ?_) b <;> intro hab
    all_goals simp only [Fin.append_left, Fin.append_right] at hab
    · rw [hinj₀ hab]
    · exact absurd hab.symm (hdisj i i')
    · exact absurd hab (hdisj i' i)
    · rw [hinj₁ hab]
  · intro j
    change Fin.append P₀ P₁ j ≠ Fin.append Q₀ Q₁ j
    refine Fin.addCases (fun j => ?_) (fun k => ?_) j
    · rw [Fin.append_left, Fin.append_left]; exact hne₀ j
    · rw [Fin.append_right, Fin.append_right]; exact hne₁ k
  · rw [eq_top_iff, ← hcl₁]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨Fin.natAdd S₀ k, ?_⟩
    change ClassGroup.mk0 ⟨(Fin.append P₀ P₁ (Fin.natAdd S₀ k)).asIdeal, _⟩ = _
    simp only [Fin.append_right]

end ZInQ.Contrib.CloudB3E1RingClass
