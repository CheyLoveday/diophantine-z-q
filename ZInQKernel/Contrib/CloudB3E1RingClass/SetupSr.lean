import ZInQKernel.Contrib.CloudB3E1RingClass.FromPairs

/-!
# The setup and the genuine moving data, recording the moving supports

Manuscript `diophantine_zq.tex`, tex 2720, 3528–3595.

`exists_extended_setup_Sr` and `exists_genuineMovingComplete_Sr` are `exists_extended_setup` and
`exists_genuineMovingComplete` with one more conclusion. Each setup they produce has moving supports
`S_r = S_supp ∪ {v : max(r, 1) ∈ v}`, so these supports are finite when `S_supp` is (as the leaf's
`GenuineFamilyMovingCharacter` requires). The proofs are those of the originals.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open scoped nonZeroDivisors

section Extend

variable {K : Type} [Field K] [NumberField K]

/-- **`exists_extended_setup`, recording the moving supports** `S_r = S_supp ∪ {v : r ∈ v}`
(tex 3528–3534). Kind: PROVED. -/
theorem exists_extended_setup_Sr (hK : Module.finrank ℚ K = 2) {S₀ : ℕ}
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
      (∀ r, r.Prime → ((r : ℤ) : 𝓞 K) ∈ (C.placeR r).asIdeal) ∧
      ∀ r, C.Sr r = Ssupp ∪ {v | ((max r 1 : ℕ) : 𝓞 K) ∈ v.asIdeal} := by
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
    fun k => ?_, ?_, ?_, ?_, fun r hr => placeR_over' hr, fun r => rfl⟩
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

end Extend

section Complete

variable {s : Qbar} {D : ℚ}

/-- **`exists_genuineMovingComplete`, recording the moving supports and the radical** (tex 2720,
3528–3595, 3662–3693). Kind: PROVED. -/
theorem exists_genuineMovingComplete_Sr (E : WeierstrassCurve ℚ) (n : ℕ)
    (hsD : s ^ 2 = algebraMap ℚ Qbar D) (hD : D < 0)
    (hi : ∀ x : quadField s, x ^ 2 ≠ -1) (hω : ∀ x : quadField s, x ^ 2 + x + 1 ≠ 0)
    {S₀ : ℕ} (P₀ Q₀ : Fin S₀ → HeightOneSpectrum (𝓞 (quadField s))) (p₀ : Fin S₀ → ℕ)
    (hp₀ : ∀ j, (p₀ j).Prime) (hinj₀ : Function.Injective p₀) (hne₀ : ∀ j, P₀ j ≠ Q₀ j)
    (hmul₀ : ∀ j, (P₀ j).asIdeal * (Q₀ j).asIdeal =
      Ideal.span {(((p₀ j : ℤ)) : 𝓞 (quadField s))})
    (act₀ over2N₀ : Fin S₀ → Prop) (hdis : ∀ j, act₀ j → ¬ over2N₀ j)
    (hodd : ∀ j, act₀ j → p₀ j ≠ 2) (Sexc₀ : Finset ℕ)
    (T : Finset (HeightOneSpectrum (𝓞 (quadField s))))
    (Ssupp : Set (HeightOneSpectrum (𝓞 (quadField s)))) (w₀ : HeightOneSpectrum (𝓞 (quadField s))) :
    ∃ (S₁ : ℕ) (C : RingClassSetup (quadField s) (S₀ + S₁)) (I : GenuineMovingComplete E n s C),
      (∀ j, C.𝔭 (Fin.castAdd S₁ j) = P₀ j ∧ C.𝔭bar (Fin.castAdd S₁ j) = Q₀ j ∧
        C.p (Fin.castAdd S₁ j) = p₀ j) ∧
      (∀ k, C.𝔭 (Fin.natAdd S₀ k) ∉ T ∧ C.𝔭bar (Fin.natAdd S₀ k) ∉ T) ∧
      (∀ j, (I.act (Fin.castAdd S₁ j) ↔ act₀ j) ∧ (I.over2N (Fin.castAdd S₁ j) ↔ over2N₀ j)) ∧
      (∀ k, ¬ I.act (Fin.natAdd S₀ k) ∧ ¬ I.over2N (Fin.natAdd S₀ k)) ∧
      Sexc₀ ⊆ I.Sexc ∧ I.D = D ∧
      ∀ r, C.Sr r = Ssupp ∪ {v | ((max r 1 : ℕ) : 𝓞 (quadField s)) ∈ v.asIdeal} := by
  classical
  have hK := finrank_quadField_of_neg hsD hD
  obtain ⟨S₁, C, hpre, hT, hinj, hne, hgen, hover, hSr⟩ :=
    exists_extended_setup_Sr hK P₀ Q₀ p₀ hp₀ hinj₀ hne₀ hmul₀ T Ssupp w₀
  let act : Fin (S₀ + S₁) → Prop := Fin.append act₀ (fun _ => False)
  let over2N : Fin (S₀ + S₁) → Prop := Fin.append over2N₀ (fun _ => False)
  let Sexc : Finset ℕ :=
    Sexc₀ ∪ Finset.univ.image C.p ∪ (discr (quadField s)).natAbs.primeFactors
  have hact_l : ∀ j, act (Fin.castAdd S₁ j) = act₀ j := fun j => Fin.append_left _ _ j
  have hact_r : ∀ k, act (Fin.natAdd S₀ k) = False := fun k => Fin.append_right _ _ k
  have hover_l : ∀ j, over2N (Fin.castAdd S₁ j) = over2N₀ j := fun j => Fin.append_left _ _ j
  have hover_r : ∀ k, over2N (Fin.natAdd S₀ k) = False := fun k => Fin.append_right _ _ k
  let I : GenuineMovingComplete E n s C :=
    { hK := hK
      hunits := units_quadField hsD hD hi hω
      D := D
      sqrtD_sq := hsD
      act := act
      decAct := Classical.decPred _
      over2N := over2N
      act_not_over2N := fun j => by
        refine Fin.addCases (fun j => ?_) (fun k => ?_) j
        · rw [hact_l, hover_l]; exact hdis j
        · rw [hact_r]; exact False.elim
      hinj := hinj
      hne := hne
      hgen := hgen
      h2 := fun j => by
        refine Fin.addCases (fun j => ?_) (fun k => ?_) j
        · rw [hact_l]
          intro hj
          have h := (not_mem_of_ne C (Fin.castAdd S₁ j) 2 Nat.prime_two
            (by rw [(hpre j).2.2]; exact (hodd j hj).symm)).1
          simpa using h
        · rw [hact_r]; exact False.elim
      Sexc := Sexc
      p_mem := fun j => Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
      hSdisc := fun q hq hd => Finset.mem_union_right _
        (Nat.mem_primeFactors.mpr ⟨hq, Int.natCast_dvd.mp hd, Int.natAbs_ne_zero.mpr
          (discr_ne_zero (quadField s))⟩)
      placeR_over := fun r hr => hover r hr.1 }
  refine ⟨S₁, C, I, hpre, hT, fun j => ⟨?_, ?_⟩, fun k => ⟨?_, ?_⟩,
    fun q hq => Finset.mem_union_left _ (Finset.mem_union_left _ hq), rfl, hSr⟩
  · change act _ ↔ _; rw [hact_l]
  · change over2N _ ↔ _; rw [hover_l]
  · change ¬ act _; rw [hact_r]; exact id
  · change ¬ over2N _; rw [hover_r]; exact id

end Complete

end ZInQ.Contrib.CloudB3E1RingClass
