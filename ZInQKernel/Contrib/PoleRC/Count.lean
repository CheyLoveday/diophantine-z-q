import ZInQKernel.Contrib.PoleRC.QClass

/-!
# The dimension-three count from the local images (`diophantine_zq.tex` lines 1061–1074)

The local images of the Kummer map of `E_ℓ` are stated as five textbook GLUE Props (`LocalReal`,
`LocalTwo`, `LocalThree`, `LocalBad`, `LocalGood`), and `dimThreeCount_of_local` proves the
manuscript's `DimThreeCount` from them: the local conditions of a Selmer class become the
equations of `kmat_forces`, which leave exactly the eight classes
`{1, ℓ, β, ℓ/β} × {(1, 1), (3, −ℓ)}`.
-/

namespace ZInQ.Manuscript.PoleRC

open Matrix

variable {ℓ : ℕ}

open Classical in
/-- The indicator, on the prime support of `ℓ`, of the prime factors of `x`. -/
noncomputable def ind (ℓ : ℕ) (x : ℤ) : Supp ℓ → ZMod 2 :=
  fun i => if (i : ℕ) ∈ x.natAbs.primeFactors then 1 else 0

theorem three_not_mem (h12 : ℓ % 12 = 11) : 3 ∉ ℓ.primeFactors := by
  intro h; have := (Nat.mem_primeFactors.mp h).2.1; omega

open Classical in
/-- **`qcls` at a prime of `ℓ` of a squarefree integer supported on `3` and the primes of `ℓ`.**
`(u_i, δλ_i + σ s_i + Σ_{j ≠ i} K_ij u_j)`, the last sum written `(Ku)_i + K_ii u_i`. -/
theorem qcls_formula (h12 : ℓ % 12 = 11) {x : ℤ} (hx : Squarefree x)
    (hsupp : x.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors) (i : Supp ℓ) :
    haveI := Fact.mk (supp_prime i)
    qcls i x = (ind ℓ x i, (if 3 ∈ x.natAbs.primeFactors then lam ℓ i else 0) +
      (if x < 0 then sgn ℓ i else 0) + ((Kmat ℓ *ᵥ ind ℓ x) i + Kmat ℓ i i * ind ℓ x i)) := by
  have := Fact.mk (supp_prime i)
  have hi3 : (i : ℕ) ≠ 3 := supp_ne_three (by omega) i
  rw [qcls_eq_sum (i : ℕ) hx]
  have h1 : ∑ p ∈ x.natAbs.primeFactors, qcls i p =
      ∑ p ∈ insert 3 ℓ.primeFactors, (if p ∈ x.natAbs.primeFactors then qcls i p else 0) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsupp]
  rw [h1, Finset.sum_insert (three_not_mem h12), ← Finset.sum_coe_sort ℓ.primeFactors,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h3 : qcls i ((3 : ℕ) : ℤ) = (0, lam ℓ i) :=
    qcls_prime_ne (i : ℕ) 3 Nat.prime_three (Ne.symm hi3)
  have hself : qcls i ((i : ℕ) : ℤ) = (1, 0) := qcls_self i
  have hne : ∀ j ∈ (Finset.univ : Finset (Supp ℓ)).erase i,
      (if (j : ℕ) ∈ x.natAbs.primeFactors then qcls i ((j : ℕ) : ℤ) else 0) =
        (0, Kmat ℓ i j * ind ℓ x j) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hji' : (j : ℕ) ≠ i := fun h => hji (Subtype.ext h)
    rw [qcls_prime_ne (i : ℕ) j (supp_prime j) hji']
    simp only [Kmat, ind, if_neg (Ne.symm hji)]
    split_ifs <;> simp <;> rfl
  rw [Finset.sum_congr rfl hne, h3, hself, qcls_neg_one]
  -- the row sum
  have hrow : (Kmat ℓ *ᵥ ind ℓ x) i + Kmat ℓ i i * ind ℓ x i =
      ∑ j ∈ (Finset.univ : Finset (Supp ℓ)).erase i, Kmat ℓ i j * ind ℓ x j := by
    rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_comm,
      ← add_assoc, zmod2_add_self, zero_add]
  rw [hrow]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum]
    unfold ind
    split_ifs <;> simp
  · split_ifs <;> simp only [Prod.snd_add, Prod.snd_sum, Prod.snd_zero, sgn, add_zero,
      zero_add] <;> ring

end ZInQ.Manuscript.PoleRC
