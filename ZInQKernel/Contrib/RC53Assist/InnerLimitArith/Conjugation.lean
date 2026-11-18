import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.Realization
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.TateLevel
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitTransport

/-!
# The conjugation of the realized derivative stages in the coefficient basis

The realized derivative matrices of the inner limit are written in the `ℤ₂`-basis of the Tate
module `T_2E` over `K_S` that underlies the coefficient module `𝕋 = T_2E ⊗ Λ(α)`, the basis in
which the fibre duality states its conjugation matrix. The comparison with the Tate module of `E`
over `ℚ̄` uses an isomorphism `K̄ ≃ ℚ̄` and the equivariant level isomorphisms
`E(K_S)[2^n] ≃ E(ℚ̄)[2^n]`.

* `tateSEquiv`: the Tate module of `E_K` over `K_S` is the Tate module of `E` over `ℚ̄`,
  `ℤ₂`-linearly, levelwise.
* `rhoK g`: the action of `g ∈ G_ℚ` transported to the Tate module over `K_S`, multiplicative in
  `g`; its matrix `rhoKMatrix g` in the coefficient basis is conjugate to the matrix of `ρ(g)` in
  any basis of `T_2E`, with the same determinant and the same congruences.
* `rhoK_conj_pt`: for an actual complex conjugation, the transported action of `e τ e⁻¹` is, at
  every level, the coordinate action `(x, y) ↦ (τx, τy)` on the points over `K_S`; it does not
  depend on the isomorphism `K̄ ≃ ℚ̄` (`rhoK_conj_indep`), and it is the unique endomorphism with
  these levels (`eq_rhoK_conj_of_pt`). Its matrix `conjMatrixK` is `ρ_T(τ)` in the coefficient
  basis: `J² = 1`, `det J = -1`.
* `realizedDerivativeK`: the realized derivative matrices in the coefficient basis, with rational
  Frobenius matrices `rhoKMatrix (Fr_i)` and conjugation `J = conjMatrixK`; `J` is `ρ_T(τ)` in the
  coefficient basis by definition (`realizedDerivativeK_J`); after base change to a residue field
  it is the matrix of `id ⊗ ρ_T(τ)` in the base-changed basis (`conjMatrixK_baseChange`).

* `conjTate_eq_rhoK`, `conjMatrix_eq_conjMatrixK`, `realizedDerivativeK_J_fibre`: the fibre
  duality's `conjTate` is the transported conjugation, its `conjMatrix` at a fibre is the
  specialization of `conjMatrixK`, and the realized conjugation read at a fibre is `conjMatrix`.
* The Frobenius of the stage primes and the square of the rational Frobenius: `galKOfQ g` (for
  `g ∈ G_ℚ` fixing the image of `K`, the `K`-automorphism `e⁻¹ g e`), `gksOfQ g` (its restriction
  to `K_S`, acting on the Tate module as the transported `ρ(g)`), `ratSqFrob D i` (the restriction
  of `e⁻¹ Fr_i² e`, acting trivially on `T_2E / 2^i T_2E`), `twisted_congr_ratSqFrob` (under the
  character constraint it acts trivially on `𝕋 / I_i 𝕋`, and so does every conjugate),
  `htriv_of_match` and `realizedDerivativeK_of_match` (the derivative congruence of a label whose
  stage Frobenius is a conjugate of `ratSqFrob D i`, `FrobeniusMatchesLabel`).

Sources: the conjugation and its duality, manuscript lines 2761–2808; (H12), lines 3088–3100; the
localization identity (5.4), lines 4809–4830; the local planes at a derivative prime, lines
5027–5037.
-/

set_option maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.InnerLimitArith

open Filter Topology Module NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (TorsS KS ActualConj conjPt conjTors coe_conjTors FullTorsion)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar TateMod tateRep)
open ZInQ.Manuscript.RC.TateWiring (tateMatrix tateMatrix_mul tateMatrix_one det_tateMatrix)
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Contrib.RC53Assist.InnerLimit
open scoped WeierstrassCurve PowerSeries.WithPiTopology

/-! ### The Tate module over `K_S` is the Tate module over `ℚ̄` -/

section TateIso

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (E : WeierstrassCurve ℚ) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)

/-- The level maps commute with the transitions. -/
theorem tateTorsMap_transition (n : ℕ) (P : Lev K S (E⁄K) (n + 1)) :
    TauCeti.tateModuleTransition 2 (E⁄Qbar).toAffine.Point n (tateTorsMap S E e (n + 1) P) =
      tateTorsMap S E e n (transLev K S (E⁄K) n P) := by
  apply Subtype.ext
  rw [TauCeti.tateModuleTransition_apply, coe_tateTorsMap, coe_tateTorsMap, coe_transLev]
  exact (map_nsmul (tatePointMap S E e) 2 _).symm

/-- The levelwise map from the Tate module over `K_S` to the Tate module over `ℚ̄`. -/
def tateSMap : TateS K S (E⁄K) →+ TateMod E 2 where
  toFun P := TauCeti.TateModule.mk (fun n => tateTorsMap S E e n ((P : ∀ n, Lev K S (E⁄K) n) n))
    fun n => by
      rw [tateTorsMap_transition]
      exact congrArg _ (P.2 n)
  map_zero' := TauCeti.TateModule.ext fun n => by
    rw [map_zero (TauCeti.TateModule.proj n)]
    exact map_zero (tateTorsMap S E e n)
  map_add' P Q := TauCeti.TateModule.ext fun n => by
    rw [map_add (TauCeti.TateModule.proj n)]
    exact map_add (tateTorsMap S E e n) ((P : ∀ n, Lev K S (E⁄K) n) n)
      ((Q : ∀ n, Lev K S (E⁄K) n) n)

theorem proj_tateSMap (P : TateS K S (E⁄K)) (n : ℕ) :
    TauCeti.TateModule.proj n (tateSMap S E e P) =
      tateTorsMap S E e n ((P : ∀ n, Lev K S (E⁄K) n) n) :=
  rfl

theorem tateSMap_smul (a : ℤ_[2]) (P : TateS K S (E⁄K)) :
    tateSMap S E e (a • P) = a • tateSMap S E e P := by
  apply TauCeti.TateModule.ext
  intro n
  rw [TauCeti.TateModule.proj_smul, proj_tateSMap, proj_tateSMap]
  apply Subtype.ext
  rw [TauCeti.TateModule.coe_zmod_smul]
  change ((tateTorsMap S E e n (resN n a • (P : ∀ n, Lev K S (E⁄K) n) n) : TateLevel E n) :
    (E⁄Qbar).toAffine.Point) = _
  rw [map_nsmul, AddSubgroup.coe_nsmul]
  rfl

/-- The levelwise map is `ℤ₂`-linear. -/
def tateSLin : TateS K S (E⁄K) →ₗ[ℤ_[2]] TateMod E 2 :=
  { tateSMap S E e with map_smul' := tateSMap_smul S E e }

theorem proj_tateSLin (P : TateS K S (E⁄K)) (n : ℕ) :
    TauCeti.TateModule.proj n (tateSLin S E e P) =
      tateTorsMap S E e n ((P : ∀ n, Lev K S (E⁄K) n) n) :=
  rfl

theorem tateSLin_injective : Function.Injective (tateSLin S E e) := by
  intro P Q h
  apply TateS.ext'
  intro n
  have h' := congrArg (TauCeti.TateModule.proj n) h
  rw [proj_tateSLin, proj_tateSLin] at h'
  exact congrArg Subtype.val (tateTorsMap_injective S E e n h')

variable [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]

theorem tateSLin_surjective : Function.Surjective (tateSLin S E e) := by
  intro y
  have hb : ∀ n, Function.Bijective (tateTorsMap S E e n) := fun n =>
    tateTorsMap_bijective S E e n (HasFullTwoTorsion.full n)
  choose P hP using fun n => (hb n).2 (TauCeti.TateModule.proj n y)
  refine ⟨⟨P, fun n => ?_⟩, ?_⟩
  · apply (hb n).1
    rw [← tateTorsMap_transition, hP, hP, TauCeti.TateModule.proj_succ]
  · apply TauCeti.TateModule.ext
    intro n
    exact hP n

/-- **The Tate module of `E_K` over `K_S` is the Tate module of `E` over `ℚ̄`**, `ℤ₂`-linearly and
levelwise, under the full two-power torsion over `K_S`. -/
def tateSEquiv : TateS K S (E⁄K) ≃ₗ[ℤ_[2]] TateMod E 2 :=
  LinearEquiv.ofBijective (tateSLin S E e) ⟨tateSLin_injective S E e, tateSLin_surjective S E e⟩

theorem proj_tateSEquiv (P : TateS K S (E⁄K)) (n : ℕ) :
    TauCeti.TateModule.proj n (tateSEquiv S E e P) =
      tateTorsMap S E e n ((P : ∀ n, Lev K S (E⁄K) n) n) :=
  rfl

end TateIso

/-! ### The transported Galois action and its matrices in the coefficient basis -/

section Transport

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (E : WeierstrassCurve ℚ) [E.IsElliptic] (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
  [HasFullTwoTorsion K S (E⁄K)]

/-- The coefficient basis of the Tate module over `K_S`. -/
abbrev basisK : Basis (Fin 2) ℤ_[2] (TateS K S (E⁄K)) :=
  ZInQ.Manuscript.RC.LambdaCoef.tateBasis (K := K) (S := S) (W := E⁄K)

/-- The action of `g ∈ G_ℚ` transported to the Tate module over `K_S`. -/
def rhoK (g : GalQ) : TateS K S (E⁄K) →ₗ[ℤ_[2]] TateS K S (E⁄K) :=
  (tateSEquiv S E e).symm.toLinearMap ∘ₗ tateRep E 2 g ∘ₗ (tateSEquiv S E e).toLinearMap

theorem tateSEquiv_rhoK (g : GalQ) (x : TateS K S (E⁄K)) :
    tateSEquiv S E e (rhoK S E e g x) = tateRep E 2 g (tateSEquiv S E e x) := by
  simp [rhoK]

theorem rhoK_mul (g h : GalQ) : rhoK S E e (g * h) = rhoK S E e g ∘ₗ rhoK S E e h := by
  apply LinearMap.ext
  intro x
  apply (tateSEquiv S E e).injective
  simp only [LinearMap.comp_apply, tateSEquiv_rhoK, map_mul, Module.End.mul_apply]

theorem rhoK_one : rhoK S E e 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply (tateSEquiv S E e).injective
  simp [tateSEquiv_rhoK]

/-- The matrix of the transported action in the coefficient basis. -/
def rhoKMatrix (g : GalQ) : Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  LinearMap.toMatrix (basisK S E) (basisK S E) (rhoK S E e g)

/-- The transported basis of the Tate module over `ℚ̄`. -/
abbrev basisQ : Basis (Fin 2) ℤ_[2] (TateMod E 2) := (basisK S E).map (tateSEquiv S E e)

theorem rhoKMatrix_eq_toMatrix (g : GalQ) :
    rhoKMatrix S E e g = LinearMap.toMatrix (basisQ S E e) (basisQ S E e) (tateRep E 2 g) := by
  ext a b
  simp only [rhoKMatrix, rhoK, LinearMap.toMatrix_apply, Module.Basis.map_repr,
    Module.Basis.map_apply, LinearEquiv.trans_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]

/-- **The transported matrix is conjugate to the matrix of `ρ(g)` in the basis of `T_2E`**. -/
theorem rhoKMatrix_eq (g : GalQ) :
    rhoKMatrix S E e g =
      (basisQ S E e).toMatrix (ZInQ.Manuscript.RC.PrintsArith.tateBasis E) * tateMatrix E g *
        (ZInQ.Manuscript.RC.PrintsArith.tateBasis E).toMatrix (basisQ S E e) := by
  rw [rhoKMatrix_eq_toMatrix, tateMatrix,
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]

theorem rhoKMatrix_mul (g h : GalQ) :
    rhoKMatrix S E e (g * h) = rhoKMatrix S E e g * rhoKMatrix S E e h := by
  rw [rhoKMatrix, rhoK_mul, LinearMap.toMatrix_comp (basisK S E) (basisK S E) (basisK S E)]
  rfl

theorem rhoKMatrix_one : rhoKMatrix S E e 1 = 1 := by
  rw [rhoKMatrix, rhoK_one, LinearMap.toMatrix_id]

/-- The transported matrices have the determinants of the Tate representation. -/
theorem det_rhoKMatrix (g : GalQ) : (rhoKMatrix S E e g).det = (tateMatrix E g).det := by
  rw [rhoKMatrix, LinearMap.det_toMatrix, det_tateMatrix, rhoK]
  have h := LinearMap.det_conj (tateRep E 2 g) (tateSEquiv S E e).symm
  rw [LinearEquiv.symm_symm] at h
  exact h

/-- Congruences of Tate matrices transfer to the coefficient basis. -/
theorem rhoKMatrix_congr {i : ℕ} {g g' : GalQ}
    (h : (PadicInt.toZModPow i).mapMatrix (tateMatrix E g) =
      (PadicInt.toZModPow i).mapMatrix (tateMatrix E g')) :
    (PadicInt.toZModPow i).mapMatrix (rhoKMatrix S E e g) =
      (PadicInt.toZModPow i).mapMatrix (rhoKMatrix S E e g') := by
  rw [rhoKMatrix_eq, rhoKMatrix_eq, map_mul, map_mul, map_mul, map_mul, h]

end Transport

/-! ### The actual complex conjugation in the coefficient basis -/

section Conj

open ComplexConjugate

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (E : WeierstrassCurve ℚ) [E.IsElliptic] (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
  [HasFullTwoTorsion K S (E⁄K)] (C : ActualConj K S)

/-- **The transported action of `e τ e⁻¹` is the coordinate action of `τ`** at every level. -/
theorem rhoK_conj_pt (x : TateS K S (E⁄K)) (n : ℕ) :
    (rhoK S E e (tateConjQ e C) x).pt n =
      conjPt C (E⁄K) (tate_baseChange_map_kappa E C) (x.pt n) := by
  have h1 := congrArg (TauCeti.TateModule.proj n) (tateSEquiv_rhoK S E e (tateConjQ e C) x)
  rw [proj_tateSEquiv] at h1
  change _ = tateProj E n (tateRep E 2 (tateConjQ e C) (tateSEquiv S E e x)) at h1
  rw [tateProj_tateRep] at h1
  change _ = tateLevelAct E n (tateConjQ e C) (TauCeti.TateModule.proj n (tateSEquiv S E e x))
    at h1
  rw [proj_tateSEquiv, ← tateTorsMap_conjTors] at h1
  have h2 := tateTorsMap_injective S E e n h1
  have h3 := congrArg Subtype.val h2
  rw [coe_conjTors] at h3
  exact h3

/-- **Uniqueness**: an endomorphism of the Tate module over `K_S` acting at every level by the
coordinate action of `τ` is the transported action of `e τ e⁻¹`. -/
theorem eq_rhoK_conj_of_pt (f : TateS K S (E⁄K) →ₗ[ℤ_[2]] TateS K S (E⁄K))
    (hf : ∀ x n, (f x).pt n = conjPt C (E⁄K) (tate_baseChange_map_kappa E C) (x.pt n)) :
    f = rhoK S E e (tateConjQ e C) := by
  apply LinearMap.ext
  intro x
  apply TateS.ext'
  intro n
  rw [hf, rhoK_conj_pt]

/-- The transported conjugation does not depend on the isomorphism `K̄ ≃ ℚ̄`. -/
theorem rhoK_conj_indep (e' : AlgebraicClosure K ≃ₐ[ℚ] Qbar) :
    rhoK S E e (tateConjQ e C) = rhoK S E e' (tateConjQ e' C) :=
  (eq_rhoK_conj_of_pt E e' C _ fun x n => rhoK_conj_pt E e C x n)

/-- **`ρ_T(τ)` in the coefficient basis**: the matrix of the coordinate action of the actual
complex conjugation on the Tate module over `K_S`. -/
def conjMatrixK : Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  rhoKMatrix S E (tateAlgEquiv K) (tateConjQ (tateAlgEquiv K) C)

/-- The conjugation matrix is the transported matrix for every isomorphism `K̄ ≃ ℚ̄`. -/
theorem conjMatrixK_eq : conjMatrixK E C = rhoKMatrix S E e (tateConjQ e C) := by
  rw [conjMatrixK, rhoKMatrix, rhoKMatrix, rhoK_conj_indep E (tateAlgEquiv K) C e]

/-- **`J² = 1`.** -/
theorem conjMatrixK_sq : conjMatrixK E C * conjMatrixK E C = 1 := by
  rw [conjMatrixK, ← rhoKMatrix_mul, tateConjQ_mul_self, rhoKMatrix_one]

/-- Complex conjugation inverts the `2`-power roots of unity of `ℚ̄`. -/
theorem tateConjQ_roots (M : ℕ) (ζ : Qbar) (hζ : ζ ^ (2 ^ M) = 1) :
    tateConjQ e C ζ = ζ ^ (2 ^ M - 1) := by
  have hinj : Function.Injective (fun y : Qbar => C.ι (e.symm y)) :=
    C.ι.injective.comp e.symm.injective
  apply hinj
  change C.ι (e.symm (tateConjQ e C ζ)) = C.ι (e.symm (ζ ^ (2 ^ M - 1)))
  rw [tateConjQ_complex]
  have hz : (C.ι (e.symm ζ)) ^ (2 ^ M) = 1 := by
    rw [← map_pow, ← map_pow, hζ, map_one, map_one]
  have hnorm := Complex.norm_eq_one_of_pow_eq_one hz (pow_ne_zero _ two_ne_zero)
  rw [← Complex.inv_eq_conj hnorm, map_pow, map_pow]
  have hz0 : C.ι (e.symm ζ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_ne_zero _ two_ne_zero)] at hz
    exact zero_ne_one hz
  rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hz0, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hz]

/-- **`det J = -1`.** -/
theorem det_conjMatrixK : (conjMatrixK E C).det = -1 := by
  rw [conjMatrixK, det_rhoKMatrix, det_tateMatrix_conj E (tateConjQ_roots (tateAlgEquiv K) C)]

/-- **After base change to any coefficient field, the conjugation matrix is the matrix of
`id ⊗ ρ_T(τ)` in the base-changed coefficient basis.** -/
theorem conjMatrixK_baseChange (A : Type) [CommRing A] [Algebra ℤ_[2] A] :
    LinearMap.toMatrix (Algebra.TensorProduct.basis A (basisK S E))
        (Algebra.TensorProduct.basis A (basisK S E))
        (LinearMap.baseChange A (rhoK S E e (tateConjQ e C))) =
      (conjMatrixK E C).map (algebraMap ℤ_[2] A) := by
  rw [LinearMap.toMatrix_baseChange, conjMatrixK_eq E e C]
  rfl

end Conj

/-! ### The conjugation matrix of the fibre duality -/

section FibreConj

open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)] (C : ActualConj K S)
  (hW : (E⁄K).map (C.κ : K →+* K) = E⁄K) (P : Ideal Lambda) [P.IsPrime]

/-- **The conjugation matrix of the fibre duality is `ρ_T(τ)` in the coefficient basis**: the
fibre duality's `conjTate` is the transported action of the actual complex conjugation, so its
matrix `conjMatrix` at a fibre is the specialization of `conjMatrixK`. -/
theorem conjTate_eq_rhoK (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) :
    ZInQ.Manuscript.RC.FibreDuality.conjTate C (E⁄K) hW = rhoK S E e (tateConjQ e C) :=
  eq_rhoK_conj_of_pt E e C _ fun x n =>
    ZInQ.Manuscript.RC.FibreDuality.conjTate_pt C (E⁄K) hW x n

theorem conjMatrix_eq_conjMatrixK :
    ZInQ.Manuscript.RC.FibreDuality.conjMatrix C (E⁄K) hW P =
      (conjMatrixK E C).map (algebraMap ℤ_[2] (ResAt P)) := by
  rw [ZInQ.Manuscript.RC.FibreDuality.conjMatrix, conjTate_eq_rhoK E C hW (tateAlgEquiv K)]
  rfl

end FibreConj

/-! ### The realized derivative matrices in the coefficient basis -/

section RealizedK

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (E : WeierstrassCurve ℚ) [E.IsElliptic] (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
  [HasFullTwoTorsion K S (E⁄K)] (C : ActualConj K S) {α : GKS K S →* Lambdaˣ}
  (L : MovingLabel K S) {h : ℕ → GalQ} {F : ℕ → IntermediateField ℚ Qbar}
  {excl : ℕ → Finset ℕ} (D : DerivativePrimes E (tateConjQ e C) h F excl)
  (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i, h i x = x)
  (htriv : ∀ i (x : TLam K S (E⁄K) α), L.frob i • x - x ∈ tlamNbhd K S (E⁄K) α i)
  (U : Ultrafilter ℕ)

/-- **The realized derivative matrices in the coefficient basis**: the same actual primes and the
same Frobenius of the stage primes on `𝕋` as `realizedDerivative`, with the rational Frobenius
matrices and the conjugation written in the coefficient basis of `T_2E` over `K_S`. -/
def realizedDerivativeK : DerivativeMatrices (R := Lambda) stageIdeal U :=
  { realizedDerivative L D (tateConjQ_mul_self e C) (tateConjQ_roots e C) hh htriv U with
    rationalFrob := fun i => (rhoKMatrix S E e (D.frob i)).map (algebraMap ℤ_[2] Lambda)
    J := (conjMatrixK E C).map (algebraMap ℤ_[2] Lambda)
    rational_congr := Eventually.of_forall fun i a b => by
      have hc := congrFun (congrFun (rhoKMatrix_congr S E e (D.tate_conj hh i)) a) b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hc
      have hz : PadicInt.toZModPow i (rhoKMatrix S E e (D.frob i) a b -
          rhoKMatrix S E e (tateConjQ e C) a b) = 0 := by
        rw [map_sub, hc, sub_self]
      have hm := algebraMap_mem_stageIdeal hz
      rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, conjMatrixK_eq E e C, ← map_sub]
      exact hm
    J_square := by
      rw [← Matrix.map_mul, conjMatrixK_sq, Matrix.map_one _ (map_zero _) (map_one _)] }

/-- **The conjugation of the realized stages is `ρ_T(τ)` in the coefficient basis**, by
definition. -/
theorem realizedDerivativeK_J :
    (realizedDerivativeK E e C L D hh htriv U).J = (conjMatrixK E C).map (algebraMap ℤ_[2] Lambda) :=
  rfl

/-- The rational Frobenius matrices of the realized stages are the transported Frobenius actions. -/
theorem realizedDerivativeK_rationalFrob (i : ℕ) :
    (realizedDerivativeK E e C L D hh htriv U).rationalFrob i =
      (rhoKMatrix S E e (D.frob i)).map (algebraMap ℤ_[2] Lambda) :=
  rfl

/-- The residue characteristics are the actual primes, unchanged. -/
theorem realizedDerivativeK_ell (i : ℕ) :
    (realizedDerivativeK E e C L D hh htriv U).ell i = ((D.ell i : ℕ) : Lambda) :=
  rfl

/-- **`det J = -1`** for the realized conjugation in the coefficient basis. -/
theorem realizedDerivativeK_J_det : (realizedDerivativeK E e C L D hh htriv U).J.det = -1 := by
  rw [realizedDerivativeK_J, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_conjMatrixK,
    map_neg, map_one]

/-- The rational Frobenius determinants are the selected primes. -/
theorem realizedDerivativeK_rationalFrob_det (i : ℕ) :
    ((realizedDerivativeK E e C L D hh htriv U).rationalFrob i).det -
      (realizedDerivativeK E e C L D hh htriv U).ell i ∈ stageIdeal i := by
  rw [realizedDerivativeK_rationalFrob, realizedDerivativeK_ell, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, det_rhoKMatrix, det_tateMatrix,
    ZInQ.Manuscript.RC.GlueSweep.Tate.det_tateRep_eq_of_isFrobAt E (D.odd i) (D.isFrob i),
    map_natCast, sub_self]
  exact Submodule.zero_mem _

/-- The inner limits of the realized stages in the coefficient basis: `ℓ → -1`, `q → 1`,
`Φ → 1`, and the limiting conjugation `J = ρ_T(τ)` with `det J = -1`. -/
theorem realizedDerivativeK_limits (hU : (U : Filter ℕ) ≤ cofinite) :
    ulim U (realizedDerivativeK E e C L D hh htriv U).ell = -1 ∧
      ulim U (fun i => (realizedDerivativeK E e C L D hh htriv U).ell i ^ 2) = 1 ∧
      ulimMat U (realizedDerivativeK E e C L D hh htriv U).phi = 1 ∧
      ulimMat U (realizedDerivativeK E e C L D hh htriv U).rationalFrob =
        (conjMatrixK E C).map (algebraMap ℤ_[2] Lambda) ∧
      (realizedDerivativeK E e C L D hh htriv U).J.det = -1 :=
  ⟨ell_limit stageIdeal_tendsToZero hU _, residueSize_limit stageIdeal_tendsToZero hU _,
    phi_limit stageIdeal_tendsToZero hU _, rationalFrob_limit stageIdeal_tendsToZero hU _,
    limitJ_det stageIdeal_tendsToZero hU _
      (Eventually.of_forall (realizedDerivativeK_rationalFrob_det E e C L D hh htriv U))⟩

/-- The limiting local action of the realized stages in the coefficient basis is `(J, -J)` with
`J = ρ_T(τ)`. -/
theorem realizedDerivativeK_localAction (hU : (U : Filter ℕ) ≤ cofinite) :
    (Matrix.toLin' (ulimMat U (realizedDerivativeK E e C L D hh htriv U).rationalFrob)).prodMap
      (Matrix.toLin' (ulimMat U (fun i => (realizedDerivativeK E e C L D hh htriv U).ellInv i •
        (realizedDerivativeK E e C L D hh htriv U).rationalFrob i))) =
      localLimitAction ((conjMatrixK E C).map (algebraMap ℤ_[2] Lambda)) :=
  localLimitAction_from_stages stageIdeal_tendsToZero hU _

/-- **The realized conjugation, read at a fibre, is the fibre duality's `conjMatrix`.** -/
theorem realizedDerivativeK_J_fibre (hW : (E⁄K).map (C.κ : K →+* K) = E⁄K)
    (P : Ideal Lambda) [P.IsPrime] :
    (realizedDerivativeK E e C L D hh htriv U).J.map
        (algebraMap Lambda (ZInQ.Manuscript.RC.Wiring.ResAt P)) =
      ZInQ.Manuscript.RC.FibreDuality.conjMatrix C (E⁄K) hW P := by
  rw [conjMatrix_eq_conjMatrixK E C hW P, realizedDerivativeK_J, Matrix.map_map]
  congr 1

end RealizedK

/-! ### Elements of `G_ℚ` fixing `K`, as elements of `G_{K,S}` -/

section Descend

open ZInQ.Manuscript.RC.SelmerComplex (resAbsCont)
open ZInQ.Manuscript.RC.CoefModules (inclS galS)

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)

/-- **`e⁻¹ g e` as a `K`-automorphism of `K̄`**, for `g ∈ G_ℚ` fixing the image of `K`. -/
def galKOfQ (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  { (e.trans (g.trans e.symm)).toRingEquiv with
    commutes' := fun x => by
      change e.symm (g (e (algebraMap K (AlgebraicClosure K) x))) = _
      rw [hg, AlgEquiv.symm_apply_apply] }

theorem galKOfQ_apply (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) (x : AlgebraicClosure K) :
    galKOfQ e g hg x = e.symm (g (e x)) :=
  rfl

/-- The map `Gal(K̄/K) → G_ℚ` sends `e⁻¹ g e` back to `g`. -/
theorem tateGalToQ_galKOfQ (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) :
    tateGalToQ e (galKOfQ e g hg) = g := by
  ext y
  rw [tateGalToQ_apply, galKOfQ_apply, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- **The restriction of `e⁻¹ g e` to `K_S`**, an element of `G_{K,S}`. -/
def gksOfQ (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) : GKS K S :=
  resAbsCont K S (galKOfQ e g hg)

theorem gksOfQ_lift (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) (x : KS K S) :
    galKOfQ e g hg (inclS K S x) = inclS K S (galS K S (gksOfQ S e g hg) x) :=
  (tate_isLift_iff (gksOfQ S e g hg) (galKOfQ e g hg)).mpr rfl x

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]

/-- **On the Tate module over `K_S`, the restriction of `e⁻¹ g e` acts as `ρ(g)`.** -/
theorem tateSEquiv_gksOfQ_smul (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) (P : TateS K S (E⁄K)) :
    tateSEquiv S E e (gksOfQ S e g hg • P) = tateRep E 2 g (tateSEquiv S E e P) := by
  apply TauCeti.TateModule.ext
  intro n
  rw [proj_tateSEquiv]
  change tateTorsMap S E e n (gksOfQ S e g hg • (P : ∀ n, Lev K S (E⁄K) n) n) =
    tateProj E n (tateRep E 2 g (tateSEquiv S E e P))
  rw [tateTorsMap_smul S E e n (gksOfQ S e g hg) (galKOfQ e g hg) (gksOfQ_lift S e g hg),
    tateGalToQ_galKOfQ, tateProj_tateRep]
  rfl

theorem gksOfQ_smul_eq_rhoK (g : GalQ)
    (hg : ∀ x : K, g (e (algebraMap K (AlgebraicClosure K) x)) =
      e (algebraMap K (AlgebraicClosure K) x)) (P : TateS K S (E⁄K)) :
    gksOfQ S e g hg • P = rhoK S E e g P := by
  apply (tateSEquiv S E e).injective
  rw [tateSEquiv_gksOfQ_smul, tateSEquiv_rhoK]

end Descend

/-! ### The square of the rational Frobenius -/

section RatSq

open ZInQ.Manuscript.RC.SelmerComplex (resAbsCont)
open ZInQ.Manuscript.RC.CoefModules (inclS galS)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (E : WeierstrassCurve ℚ) [E.IsElliptic] (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
  [HasFullTwoTorsion K S (E⁄K)] (C : ActualConj K S)
  {h : ℕ → GalQ} {F : ℕ → IntermediateField ℚ Qbar} {excl : ℕ → Finset ℕ}
  (D : DerivativePrimes E (tateConjQ e C) h F excl)
  (hK : ∀ i (x : K), (D.frob i * D.frob i) (e (algebraMap K (AlgebraicClosure K) x)) =
    e (algebraMap K (AlgebraicClosure K) x))

/-- **The square of the selected rational Frobenius, in `G_{K,S}`**: the restriction of
`e⁻¹ Fr_i² e` to `K_S`. -/
def ratSqFrob (i : ℕ) : GKS K S :=
  gksOfQ S e (D.frob i * D.frob i) (hK i)

omit [E.IsElliptic] in
/-- A matrix congruent to the identity modulo `2^i` is the identity plus `2^i` times a matrix. -/
theorem exists_sub_one_eq_two_pow_smul {i : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ_[2]}
    (hM : (PadicInt.toZModPow i).mapMatrix M = 1) :
    ∃ N : Matrix (Fin 2) (Fin 2) ℤ_[2], M - 1 = (2 : ℤ_[2]) ^ i • N := by
  have hmem : ∀ a b, (M - 1) a b ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ i} := by
    intro a b
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, Matrix.sub_apply, map_sub]
    have h1 := congrFun (congrFun hM a) b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    rw [h1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  choose N hN using fun a b => Ideal.mem_span_singleton'.mp (hmem a b)
  refine ⟨Matrix.of fun a b => N a b, ?_⟩
  ext a b
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hN a b, Nat.cast_ofNat, mul_comm]

omit [HasFullTwoTorsion K S (E⁄K)] in
/-- The Tate matrix of `Fr_i²` is the identity modulo `2^i`. -/
theorem tateMatrix_frob_sq_mod (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x) (i : ℕ) :
    (PadicInt.toZModPow i).mapMatrix (tateMatrix E (D.frob i * D.frob i)) = 1 := by
  rw [tateMatrix_mul, map_mul, D.tate_conj hh i, ← map_mul, ← tateMatrix_mul,
    tateConjQ_mul_self, tateMatrix_one, map_one]

/-- **The square of the rational Frobenius acts trivially on `T_2E / 2^i T_2E`.** -/
theorem ratSqFrob_smul_sub (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x) (i : ℕ) (P : TateS K S (E⁄K)) :
    ∃ Q : TateS K S (E⁄K), (2 : ℤ_[2]) ^ i • Q = ratSqFrob E e C D hK i • P - P := by
  obtain ⟨N, hN⟩ := exists_sub_one_eq_two_pow_smul (tateMatrix_frob_sq_mod E e C D hh i)
  let b := ZInQ.Manuscript.RC.PrintsArith.tateBasis E
  have hf : LinearMap.toMatrix b b
      (tateRep E 2 (D.frob i * D.frob i) - LinearMap.id : TateMod E 2 →ₗ[ℤ_[2]] TateMod E 2) =
      (2 : ℤ_[2]) ^ i • N := by
    rw [map_sub, LinearMap.toMatrix_id, ← hN]
    rfl
  have hy : ∀ y : TateMod E 2,
      ((tateRep E 2 (D.frob i * D.frob i) - LinearMap.id : TateMod E 2 →ₗ[ℤ_[2]] TateMod E 2) y) =
      (2 : ℤ_[2]) ^ i • Matrix.toLin b b N y := by
    intro y
    rw [← Matrix.toLin_toMatrix b b
      (tateRep E 2 (D.frob i * D.frob i) - LinearMap.id : TateMod E 2 →ₗ[ℤ_[2]] TateMod E 2), hf,
      map_smul, LinearMap.smul_apply]
  refine ⟨(tateSEquiv S E e).symm (Matrix.toLin b b N (tateSEquiv S E e P)), ?_⟩
  apply (tateSEquiv S E e).injective
  rw [map_smul, LinearEquiv.apply_symm_apply, ← hy, map_sub, ratSqFrob, tateSEquiv_gksOfQ_smul]
  rfl

variable {α : GKS K S →* Lambdaˣ}

/-- **The twisted derivative congruence for the square of the rational Frobenius**: under the
character constraint `α(ratSqFrob D i) ≡ 1` modulo the stage ideal, it acts trivially on
`𝕋 / I_i 𝕋`. -/
theorem twisted_congr_ratSqFrob (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x) (i : ℕ)
    (hα : ((α (ratSqFrob E e C D hK i) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i)
    (x : TLam K S (E⁄K) α) :
    ratSqFrob E e C D hK i • x - x ∈ tlamNbhd K S (E⁄K) α i := by
  induction x using TLam.induction with
  | zero => rw [smul_zero, sub_zero]; exact Submodule.zero_mem _
  | tmul l P => exact smul_tmul_sub_mem _ i l P hα (ratSqFrob_smul_sub E e C D hK hh i P)
  | add x y hx hy =>
    rw [smul_add, add_sub_add_comm]
    exact Submodule.add_mem _ hx hy

omit [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)] in
/-- Acting trivially on `𝕋 / I_i 𝕋` is invariant under conjugation in `G_{K,S}`. -/
theorem twisted_congr_of_conj {i : ℕ} {σ : GKS K S}
    (hσ : ∀ x : TLam K S (E⁄K) α, σ • x - x ∈ tlamNbhd K S (E⁄K) α i) (g : GKS K S)
    (x : TLam K S (E⁄K) α) : (g * σ * g⁻¹) • x - x ∈ tlamNbhd K S (E⁄K) α i := by
  have e1 : (g * σ * g⁻¹) • x - x = g • (σ • (g⁻¹ • x) - g⁻¹ • x) := by
    rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
  rw [e1]
  exact act_mem_tlamNbhd g i (hσ (g⁻¹ • x))

/-- **The match of the label's Frobenius with the rational Frobenius**: at every stage, the
Frobenius of the stage prime in `G_{K,S}` is a conjugate of the restriction of `e⁻¹ Fr_i² e`. -/
def FrobeniusMatchesLabel (L : MovingLabel K S) : Prop :=
  ∀ i, ∃ g : GKS K S, L.frob i = g * ratSqFrob E e C D hK i * g⁻¹

/-- **The derivative congruence of a label from the rational Frobenius**: if the Frobenius of the
stage primes matches the square of the rational Frobenius and the character constraint holds,
the Frobenius of the stage primes acts trivially on `𝕋 / I_i 𝕋` at every stage. -/
theorem htriv_of_match (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x)
    (hα : ∀ i, ((α (ratSqFrob E e C D hK i) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i)
    (L : MovingLabel K S) (hL : FrobeniusMatchesLabel E e C D hK L) :
    ∀ i (x : TLam K S (E⁄K) α), L.frob i • x - x ∈ tlamNbhd K S (E⁄K) α i := by
  intro i x
  obtain ⟨g, hg⟩ := hL i
  rw [hg]
  exact twisted_congr_of_conj E (twisted_congr_ratSqFrob E e C D hK hh i (hα i)) g x

/-- **The realized derivative matrices in the coefficient basis without the derivative-congruence
input**: built from the actual primes, the match of the label's Frobenius with the rational
Frobenius, and the character constraint. -/
def realizedDerivativeK_of_match (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x)
    (hα : ∀ i, ((α (ratSqFrob E e C D hK i) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i)
    (L : MovingLabel K S) (hL : FrobeniusMatchesLabel E e C D hK L) (U : Ultrafilter ℕ) :
    DerivativeMatrices (R := Lambda) stageIdeal U :=
  realizedDerivativeK E e C (α := α) L D hh (htriv_of_match E e C D hK hh hα L hL) U

/-- Its conjugation is `ρ_T(τ)` in the coefficient basis. -/
theorem realizedDerivativeK_of_match_J (hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i,
      h i x = x)
    (hα : ∀ i, ((α (ratSqFrob E e C D hK i) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i)
    (L : MovingLabel K S) (hL : FrobeniusMatchesLabel E e C D hK L) (U : Ultrafilter ℕ) :
    (realizedDerivativeK_of_match E e C D hK hh hα L hL U).J =
      (conjMatrixK E C).map (algebraMap ℤ_[2] Lambda) :=
  rfl

end RatSq

end ZInQ.Contrib.RC53Assist.InnerLimitArith
