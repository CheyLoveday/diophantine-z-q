import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Place

/-! Compare (O.11) on all indices in the common field and at the two
places. The power-of-two rescaling of the source cancels exactly. The
base change calculation is provenance (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenBudget

open ZInQ.Manuscript.RC.Odd
open AddressGenuine AuxInputs Wiring
open ZInQ.Manuscript.RC.Even
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

section Transport

variable {R S : Type} [CommRing R] [CommRing S]

private theorem map_TL_scaled (f : R →+* S) {η a : ℕ → R} {η' a' : ℕ → S} {s : S}
    (hη : ∀ n, f (η n) = η' n) (ha : ∀ n, f (a n) = s * a' n) (J : List ℕ) (n : ℕ) :
    f (TL η J a n) = s * TL η' J a' n := by
  induction J generalizing n with
  | nil => exact ha n
  | cons p J ih =>
    have hd : f (divCoeff (TL η J a) p n) = s * divCoeff (TL η' J a') p n := by
      unfold divCoeff
      split_ifs <;> simp [ih]
    simp only [TL_cons, Odd.Top, map_sub, map_mul, ih, hη, hd]
    ring

private theorem map_unary (f : R →+* S) {η : ℕ → R} {η' : ℕ → S}
    (hη : ∀ n, f (η n) = η' n) (good : ℕ → Prop) (i : Fin 2) (j n : ℕ) :
    f (unaryCoeff good η i j n) = unaryCoeff good η' i j n := by
  classical
  unfold unaryCoeff
  split <;> simp [hη]

theorem map_rawNumerator_scaled (f : R →+* S) {η a : ℕ → R} {η' a' : ℕ → S} {s : S}
    (hη : ∀ n, f (η n) = η' n) (ha : ∀ n, f (a n) = s * a' n)
    (good : ℕ → Prop) (i : Fin 2) (J : List ℕ) (n : ℕ) :
    f (rawNumerator good η a i J n) = s * rawNumerator good η' a' i J n := by
  simp only [rawNumerator, map_sub, map_sum, map_mul, map_TL_scaled f hη ha, map_unary f hη,
    mul_sub, Finset.mul_sum, mul_assoc]

private theorem map_timesTheta (f : R →+* S) (a : ℕ → R) (n : ℕ) :
    f (ThetaCoeff.timesTheta a n) = ThetaCoeff.timesTheta (fun k => f (a k)) n := by
  simp only [ThetaCoeff.timesTheta, map_add, map_mul, map_ofNat, map_sum]

end Transport

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {O K : Type} [CommRing O] [Field K] [CharZero K] [Algebra O K]

/-- The formal divided series before either coefficient embedding, at the
original depth. A statement about coefficients, independent of modularity. -/
def halfDivided {F : Type} [Field F] (good : ℕ → Prop) (η a : ℕ → F)
    (δ : ℤ) (i : Fin 2) (J : List ℕ) (n : ℕ) : F :=
  (2 : F) ^ (-(δ + J.length + 1)) * rawNumerator good η a i J n

omit [CharZero K] in
theorem commonCoeff_complex (C : SourceAtPlace P O K) (hS : SupportSpec W)
    (i : Fin 2) (J : List ℕ) (n : ℕ) :
    C.eC (ThetaCoeff.timesTheta (halfDivided ((evenTypes W.S hS.1).Good) C.η₀ C.c P.δ i J) n) =
      ThetaCoeff.timesTheta
        (halfDivided ((evenTypes W.S hS.1).Good) (fun p => P.phaseData.η p) P.sievedCoeff P.δ i J) n := by
  rw [map_timesTheta]
  congr 1
  funext k
  simp only [halfDivided, map_mul, map_zpow₀, map_ofNat,
    map_rawNumerator_scaled C.eC C.complex_eta (fun n => (C.complex_coeff n).trans (one_mul _).symm),
    one_mul]

theorem commonCoeff_place (C : SourceAtPlace P O K) (hS : SupportSpec W)
    (hinj : Function.Injective (algebraMap O K)) (i : Fin 2) (J : List ℕ)
    (hJ : J.Nodup) (hg : ∀ p ∈ J, (evenTypes W.S hS.1).Good p) (n : ℕ) :
    algebraMap O K (ThetaCoeff.timesTheta
      (dividedCoeff (source_at_place C hS hinj) i J hJ hg) n) =
      C.eK (ThetaCoeff.timesTheta (halfDivided ((evenTypes W.S hS.1).Good) C.η₀ C.c P.δ i J) n) := by
  rw [map_timesTheta, map_timesTheta]
  congr 1
  funext k
  have h : -(P.δ + C.k + (J.length : ℤ) + 1) + C.k = -(P.δ + J.length + 1) := by omega
  rw [dividedCoeff_spec, halfDivided, map_mul C.eK, map_zpow₀ C.eK, map_ofNat C.eK,
    map_rawNumerator_scaled (algebraMap O K) C.integral_eta C.integral_coeff,
    map_rawNumerator_scaled C.eK (fun _ => rfl) (fun _ => (one_mul _).symm), one_mul,
    ← mul_assoc, ← zpow_add₀ (by norm_num : (2 : K) ≠ 0), h]

/-- The undivided unary correction after ordinary theta multiplication
has reduced support only on its square shell. This is the unary-support
input of the determinant calculation. -/
theorem unary_timesTheta_mem {O : Type} [CommRing O] (m : Ideal O) (h2 : (2 : O) ∈ m)
    (good : ℕ → Prop) (η : ℕ → O) (i : Fin 2) (b : O) {d n : ℕ}
    (hn : ∀ k : ℕ, n ≠ d * k ^ 2) :
    ThetaCoeff.timesTheta (fun k => b * unaryCoeff good η i d k) n ∈ m := by
  have hz : unaryCoeff good η i d n = 0 := by
    unfold unaryCoeff
    rw [dite_eq_right]
    rintro ⟨k, _, _, hk⟩
    exact hn k hk
  have h := timesTheta_congr (fun k => b * unaryCoeff good η i d k) n
  rw [hz, mul_zero, sub_zero] at h
  obtain ⟨x, hx⟩ := h
  rw [hx]
  exact m.mul_mem_right x h2

#print axioms unary_timesTheta_mem

#print axioms map_TL_scaled
#print axioms map_unary
#print axioms map_rawNumerator_scaled
#print axioms map_timesTheta
#print axioms commonCoeff_complex
#print axioms commonCoeff_place

end ZInQ.Manuscript.RC.EvenBudget
