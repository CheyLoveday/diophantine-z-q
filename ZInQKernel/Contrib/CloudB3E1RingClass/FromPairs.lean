import ZInQKernel.Contrib.CloudB3E1RingClass.SetupExtend

/-!
# The genuine moving data from prescribed split pairs over an imaginary quadratic field

Manuscript `diophantine_zq.tex`, tex 2720, 3528–3595, 3662–3693.

Over `K = ℚ(s)` with `s² = D < 0`:
* `finrank_quadField_of_neg`: `[K : ℚ] = 2`;
* `isTotallyComplex_quadField_of_neg`: `K` is totally complex;
* `units_quadField`: `𝒪_K^× = {±1}` when `K ≠ ℚ(i), ℚ(√−3)` (tex 2720), i.e. no `x² = −1` and no
  `x² + x + 1 = 0` in `K`, from lane E2's `units_eq_one_or_neg_one`.

**`exists_genuineMovingComplete`** (PROVED). Inputs, all explicit choices of the setup:
* prescribed split pairs `(𝔭⁰_j, 𝔭̄⁰_j)` over pairwise distinct primes `p⁰_j`;
* the labels `act`, `over2N` on them, disjoint, with the active `p⁰_j` odd;
* a finite excluded set `Sexc₀` (tex 3528–3534).

It produces a setup `C` extending the prescribed pairs by generators of `Cl(K)`, and a
`GenuineMovingComplete` on it, with:
* the prescribed pairs and labels in the first `S₀` places;
* no labels on the generators;
* `Sexc ⊇ Sexc₀`.

Consequently `moving_character_complete` applies with no remaining hypothesis beyond these choices
(and the Serre/CM/trace inputs of RC0).

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain Polynomial
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open ZInQ.Contrib.CloudB3E2.RingClassDelta
open scoped nonZeroDivisors

variable {s : Qbar} {D : ℚ}

/-- **`[ℚ(s) : ℚ] = 2`** for `s² = D < 0`. Kind: PROVED. -/
theorem finrank_quadField_of_neg (hsD : s ^ 2 = algebraMap ℚ Qbar D) (hD : D < 0) :
    Module.finrank ℚ (quadField s) = 2 := by
  have hirr : Irreducible (X ^ 2 - C D : ℚ[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => by nlinarith [sq_nonneg b])
  have hmin : minpoly ℚ s = X ^ 2 - C D := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C D two_ne_zero)).symm
    simp [hsD]
  have hint : IsIntegral ℚ s := Algebra.IsIntegral.isIntegral s
  change Module.finrank ℚ (IntermediateField.adjoin ℚ {s}) = 2
  rw [IntermediateField.adjoin.finrank hint, hmin, natDegree_X_pow_sub_C]

/-- **`ℚ(s)` is totally complex** for `s² = D < 0`. Kind: PROVED. -/
theorem isTotallyComplex_quadField_of_neg (hsD : s ^ 2 = algebraMap ℚ Qbar D) (hD : D < 0) :
    IsTotallyComplex (quadField s) := by
  refine ⟨fun w => ?_⟩
  by_contra hw
  rw [InfinitePlace.not_isComplex_iff_isReal, InfinitePlace.isReal_iff] at hw
  let ψ := hw.embedding
  let s' : quadField s := ⟨s, IntermediateField.mem_adjoin_simple_self ℚ s⟩
  have hs' : s' ^ 2 = algebraMap ℚ (quadField s) D := Subtype.ext (by simpa using hsD)
  have h := congrArg ψ hs'
  rw [map_pow, eq_ratCast] at h
  have h' : ψ s' ^ 2 = (D : ℝ) := by
    rw [h, map_ratCast]
  have : (D : ℝ) < 0 := by exact_mod_cast hD
  nlinarith [sq_nonneg (ψ s')]

/-- **`𝒪_K^× = {±1}`** for `K = ℚ(s)`, `s² = D < 0`, `K ≠ ℚ(i), ℚ(√−3)` (tex 2720).
Kind: PROVED. -/
theorem units_quadField (hsD : s ^ 2 = algebraMap ℚ Qbar D) (hD : D < 0)
    (hi : ∀ x : quadField s, x ^ 2 ≠ -1) (hω : ∀ x : quadField s, x ^ 2 + x + 1 ≠ 0) :
    ∀ ε : (𝓞 (quadField s))ˣ, ε = 1 ∨ ε = -1 := by
  have := isTotallyComplex_quadField_of_neg hsD hD
  exact units_eq_one_or_neg_one (finrank_quadField_of_neg hsD hD) hi hω

/-- **The genuine moving data from prescribed split pairs** (tex 2720, 3528–3595, 3662–3693): see
the module docstring. Kind: PROVED. -/
theorem exists_genuineMovingComplete (E : WeierstrassCurve ℚ) (n : ℕ)
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
      Sexc₀ ⊆ I.Sexc ∧ I.D = D := by
  classical
  have hK := finrank_quadField_of_neg hsD hD
  obtain ⟨S₁, C, hpre, hT, hinj, hne, hgen, hover⟩ :=
    exists_extended_setup hK P₀ Q₀ p₀ hp₀ hinj₀ hne₀ hmul₀ T Ssupp w₀
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
    fun q hq => Finset.mem_union_left _ (Finset.mem_union_left _ hq), rfl⟩
  · change act _ ↔ _; rw [hact_l]
  · change over2N _ ↔ _; rw [hover_l]
  · change ¬ act _; rw [hact_r]; exact id
  · change ¬ over2N _; rw [hover_r]; exact id

end ZInQ.Contrib.CloudB3E1RingClass
