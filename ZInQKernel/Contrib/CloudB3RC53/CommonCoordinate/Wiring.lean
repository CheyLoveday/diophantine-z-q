import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Bridge
import ZInQKernel.Contrib.OneProof.RC.Wiring.Central

/-!
# Common coordinate, part 4: a `CommonCoordinateModel` from the support-triangle models

Lane RC0's input for (4.7) (`RC/Wiring/Central.lean`) is, at every address of a final family, a
`CommonCoordinateModel`. `commonCoordinateModel_of_models` builds one: the fields `h47` and `hunit`
— the multi-prime (4.7) and `ε_q ∈ Λ^×` (tex L4166–4193), listed there as "ELLIOT + GLUE (Nekovář
6.4.1–6.4.3)" — are produced from triangular models of the support triangle at each relaxation step
(`Bridge.lean`, `Triangular.lean`; the old-part relations are the norm identity and
`λ_R ∘ i = e_q λ_P`, hypotheses of the models; the headline does not import `Naturality.lean`, so on the
headline's route they are assumed), with `ε_q = q⁻⁴`. The remaining fields (the ring `𝒪[G]`,
the character, the Euler-factor data `hratio`, `hinv`, the sign data and `ũ = η u_rel`) are taken as
given, as RC0 lists them.

**Classification.** PROVED (GLUE to RC0's wiring).
-/

namespace ZInQ.Contrib.CloudB3RC53.CommonCoordinate

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Manuscript.RC.Wiring

/-- **A `CommonCoordinateModel` from the support-triangle models** (tex L4142–4328). Besides
RC0's definitional and Euler-factor fields, the inputs are: for each unused prime `p` an odd residue
cardinality `qn p`, a Frobenius matrix `F p` over `ℚ₂[[t]]` with trace `a p` and determinant
`qn p`, the scalar `z p` with inverse `zi p`, the identifications `chi(l_p) = l_p(F p, …)` and
`chi(e_p) = e_p`, and the coordinates `u T` relaxed at `T ⊆ U` (`u U = u_rel`,
`u ∅ = u_prim,x`) related at each step by a triangular model. Then `ε_p = q_p⁻⁴`. -/
noncomputable def commonCoordinateModel_of_models {ℓ : ℕ} (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) (R : Type) [CommRing R] (chi : R →+* PowerSeries ℚ_[2]) (Q : Finset ℕ)
    (v g l e ei : ℕ → R)
    (hsign : ∀ q ∈ Q, chi (g q) = 1 ∨ chi (g q) = -1)
    (hratio : ∀ q ∈ Q, chi (l q) * chi (ei q) ^ 2 = 1 + 2 * chi (v q))
    (hinv : ∀ q ∈ Q, chi (e q) * chi (ei q) = 1) (urel : PowerSeries ℚ_[2]) (U : Finset ℕ)
    (hU : ∀ q, q ∈ U ↔ (q ∈ Q ∧ chi (g q) = 1))
    (hutilde : D.uTilde Fam x = chi (Central.eta Q v g) * urel)
    (qn : ℕ → ℕ) (hodd : ∀ p ∈ U, Odd (qn p))
    (F : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])) (a z zi : ℕ → PowerSeries ℚ_[2])
    (ha : ∀ p ∈ U, (F p).trace = a p)
    (hd : ∀ p ∈ U, (F p).det = PowerSeries.C (qn p : ℚ_[2]))
    (hl : ∀ p ∈ U, chi (l p) =
      quotientFactor (F p) (PowerSeries.C ((qn p : ℚ_[2])⁻¹)) (z p) (zi p))
    (he : ∀ p ∈ U, chi (e p) = pointFactor (a p) (z p) (zi p))
    (u : Finset ℕ → PowerSeries ℚ_[2]) (hrel : u U = urel) (hprim : u ∅ = D.uPrim Fam x)
    (hmodel : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T → ∃ (n : ℕ) (DP : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2]))
      (X : Matrix (Fin n) (Fin 2 ⊕ Fin 2) (PowerSeries ℚ_[2])) (zP wP : Fin n → PowerSeries ℚ_[2])
      (zR wR : Fin n ⊕ (Fin 2 ⊕ Fin 2) → PowerSeries ℚ_[2]),
      (∀ i, zR (Sum.inl i) = pointFactor (a p) (z p) (zi p) * zP i) ∧
      (∀ i, wR (Sum.inl i) = pointFactor (a p) (z p) (zi p) * wP i) ∧
      IsCoordOn (fromBlocks DP X 0
        (twoPlaceBlock (F p) (PowerSeries.C (qn p : ℚ_[2])) (z p) (zi p))) zR wR (u (insert p T)) ∧
      IsClassFunctionalCoord DP zP wP (u T) ∧ DP.adjugate ≠ 0) :
    CommonCoordinateModel D Fam x where
  R := R
  chi := chi
  Q := Q
  v := v
  g := g
  l := l
  e := e
  ei := ei
  eps := fun p => PowerSeries.C ((qn p : ℚ_[2])⁻¹) ^ 4
  hsign := hsign
  hratio := hratio
  hinv := hinv
  urel := urel
  U := U
  hU := hU
  h47 := by
    have hq : ∀ p ∈ U, PowerSeries.C (qn p : ℚ_[2]) * PowerSeries.C ((qn p : ℚ_[2])⁻¹) = 1 := by
      intro p hp
      have hne : (qn p : ℚ_[2]) ≠ 0 := by
        have := (hodd p hp).pos
        exact_mod_cast this.ne'
      rw [← map_mul, mul_inv_cancel₀ hne, map_one]
    exact commonCoordinate_h47_of_models chi U l e urel (D.uPrim Fam x) F
      (fun p => PowerSeries.C (qn p : ℚ_[2])) (fun p => PowerSeries.C ((qn p : ℚ_[2])⁻¹)) a z zi u
      hl he hrel hprim hq ha hd hmodel
  hunit := fun p hp => lamUnit_inv_odd_pow (qn p) (hodd p hp)
  hutilde := hutilde

end ZInQ.Contrib.CloudB3RC53.CommonCoordinate
