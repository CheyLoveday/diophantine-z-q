import ZInQKernel.Contrib.OneProof.RC.Central.Correction
import ZInQKernel.Contrib.OneProof.RC.Central.Coordinate

/-!
# Common coordinate, part 2: the support triangle gives (4.7)

Lemma `ex:arith-common-coordinate` (`diophantine_zq.tex`, tex L4142–4328), proof, tex L4166–4193:

> The actual norm identity is `z_R = e_q i(z_P)` [...] Consequently `λ_R ∘ i = e_q λ_P`. [...]
> The two quotient determinants satisfy `δ_q = det(z Fr_q − q) det(z⁻¹ Fr_q − q) = q⁴ l_q`. In the
> original integral determinant bases, the support triangle therefore gives
> `l_q u_rel = e_q² ε_q u_prim`, `ε_q ∈ Λ^×` (4.7).

The support triangle `C_P → C_R → (singular quotient at q)` is realized by the upper triangular
model of `SelmerDuality/SupportChange.lean` ("the old complex is an actual subcomplex of an upper
triangular model", tex L3492–3494): in two-term form the relaxed differential is
`D_R = [[D_P, X], [0, D_W]]` with `D_W` the two-place singular block
`diag(z Fr_q − q, z⁻¹ Fr_q − q)`.

* `adjugate_fromBlocks_inl_inl`: the upper-left block of `adj [[A, B], [0, C]]` is `det C · adj A`.
* `triangular_coord` (PROVED): if the relaxed cycle and functional restrict to `e z_P` and `e w_P`
  on the old part (the norm identity and `λ_R ∘ i = e λ_P`, `Naturality.lean`), then
  `det D_W · u_rel = e² u_prim` (each of the class and the functional contributes one `e`).
* `single_prime_47_of_model` (PROVED, tex L4181–4193): with `D_W` the two-place singular block,
  `δ_q = det D_W = q⁴ l_q` (RC15's `quotientDet_eq`) and RC15's `single_prime_47` give (4.7)
  `l_q u_rel = e_q² ε_q u_prim` with `ε_q = q⁻⁴` a unit.
* `prod_relax_of_models` (PROVED): relaxing the unused primes one at a time through such models
  gives `(∏ l_q) u_rel = (∏ e_q² ε_q) u_prim`, the input of RC15's `corrected_eq`
  (`ũ_x = (∏ ε_q) u_{prim,x}`, the universal correction `η`, `Correction.lean`).

The further unit from the comparison of the retained determinant bases (tex L4189–4193, "only
determinants of unit disks") is `MinimalComplexes/CoordinateUnit.lean`'s base-change factor.

**Classification.** PROVED (from the triangular model; the identification of the model with the
actual Galois cochains is the open identification of `SelmerDuality`).
-/

namespace ZInQ.Contrib.CloudB3RC53.CommonCoordinate

open Matrix ZInQ.Manuscript.RC.Central

variable {K : Type*} [CommRing K]

/-- The class-functional coordinate on any finite index type (`z ⊗ w = u · adj D`); on `Fin n` it
is RC15's `IsClassFunctionalCoord`. -/
def IsCoordOn {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι K) (z w : ι → K) (u : K) :
    Prop :=
  vecMulVec z w = u • D.adjugate

theorem isCoordOn_fin_iff {n : ℕ} (D : Matrix (Fin n) (Fin n) K) (z w : Fin n → K) (u : K) :
    IsCoordOn D z w u ↔ IsClassFunctionalCoord D z w u :=
  Iff.rfl

/-- **The upper-left block of the adjugate of a block upper triangular matrix.** -/
theorem adjugate_fromBlocks_inl_inl {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) κ K) (C : Matrix κ κ K) (i j : Fin n) :
    (fromBlocks A B 0 C).adjugate (Sum.inl i) (Sum.inl j) = C.det * A.adjugate i j := by
  rw [adjugate_apply, adjugate_apply]
  have : (fromBlocks A B 0 C).updateRow (Sum.inl j) (Pi.single (Sum.inl i) 1) =
      fromBlocks (A.updateRow j (Pi.single i 1)) (B.updateRow j 0) 0 C := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [updateRow_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Sum.inl.injEq, reduceCtorEq, ite_false, Matrix.zero_apply] <;>
      split_ifs <;> simp [Pi.single_apply]
  rw [this, det_fromBlocks_zero₂₁, mul_comm]

/-- **The support triangle on coordinates** (tex L4166–4188). For the relaxed two-term model
`D_R = [[D_P, X], [0, D_W]]`, if the relaxed cycle and functional restrict on the old part to
`e z_P` and `e w_P`, `u_rel` and `u_prim` are the two coordinates and `adj D_P ≠ 0`, then
`det D_W · u_rel = e² u_prim`. -/
theorem triangular_coord [IsDomain K] {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (DP : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) κ K) (DW : Matrix κ κ K)
    (zP wP : Fin n → K) (zR wR : Fin n ⊕ κ → K) (e uprim urel : K)
    (hz : ∀ i, zR (Sum.inl i) = e * zP i) (hw : ∀ i, wR (Sum.inl i) = e * wP i)
    (hR : IsCoordOn (fromBlocks DP X 0 DW) zR wR urel)
    (hP : IsClassFunctionalCoord DP zP wP uprim) (hadj : DP.adjugate ≠ 0) :
    DW.det * urel = e ^ 2 * uprim := by
  obtain ⟨i, j, hij⟩ := exists_entry_ne_zero hadj
  have a := congrFun (congrFun hR (Sum.inl i)) (Sum.inl j)
  have b := congrFun (congrFun hP i) j
  simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, adjugate_fromBlocks_inl_inl,
    hz, hw] at a b
  have key : (DW.det * urel - e ^ 2 * uprim) * DP.adjugate i j = 0 := by
    linear_combination -a + e ^ 2 * b
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hij)

/-- The two-place singular block `diag(z Fr_q − q, z⁻¹ Fr_q − q)` at an unused prime `q`
(tex L4181–4184, (4.4) at augmentation at the two conjugate places). -/
def twoPlaceBlock (F : Matrix (Fin 2) (Fin 2) K) (q z zi : K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (z • F - q • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0
    (zi • F - q • (1 : Matrix (Fin 2) (Fin 2) K))

theorem det_twoPlaceBlock (F : Matrix (Fin 2) (Fin 2) K) (q z zi : K) :
    (twoPlaceBlock F q z zi).det = quotientDet F q z zi := by
  rw [twoPlaceBlock, det_fromBlocks_zero₂₁]
  rfl

/-- **(4.7) at one unused prime from the triangular model** (tex L4166–4193). With the relaxed
model `[[D_P, X], [0, D_W]]`, `D_W` the two-place singular block for a Frobenius matrix `F` with
trace `a_q` and determinant `q` (`q q⁻¹ = 1`), relaxed cycle and functional restricting to
`e_q z_P`, `e_q w_P` (`e_q = a_q − z − z⁻¹`) and `adj D_P ≠ 0`:
`l_q u_rel = e_q² ε_q u_prim` with `ε_q = q⁻⁴`, a unit. -/
theorem single_prime_47_of_model [IsDomain K] {n : ℕ} (DP : Matrix (Fin n) (Fin n) K)
    (X : Matrix (Fin n) (Fin 2 ⊕ Fin 2) K) (F : Matrix (Fin 2) (Fin 2) K) (q qi a z zi : K)
    (hq : q * qi = 1) (ha : F.trace = a) (hd : F.det = q)
    (zP wP : Fin n → K) (zR wR : Fin n ⊕ (Fin 2 ⊕ Fin 2) → K) (uprim urel : K)
    (hz : ∀ i, zR (Sum.inl i) = pointFactor a z zi * zP i)
    (hw : ∀ i, wR (Sum.inl i) = pointFactor a z zi * wP i)
    (hR : IsCoordOn (fromBlocks DP X 0 (twoPlaceBlock F q z zi)) zR wR urel)
    (hP : IsClassFunctionalCoord DP zP wP uprim) (hadj : DP.adjugate ≠ 0) :
    quotientFactor F qi z zi * urel = pointFactor a z zi ^ 2 * qi ^ 4 * uprim ∧
      IsUnit (qi ^ 4) := by
  have htri := triangular_coord DP X _ zP wP zR wR _ uprim urel hz hw hR hP hadj
  rw [det_twoPlaceBlock] at htri
  have h47 := single_prime_47 (urel := urel) (uprim := uprim) (e := pointFactor a z zi)
    (δ := quotientDet F q z zi) (l := quotientFactor F qi z zi) (ε' := 1) hq
    (quotientDet_eq z zi hq ha hd) (by rw [htri]; ring)
  refine ⟨by rw [h47]; ring, ?_⟩
  exact (show IsUnit qi from ⟨⟨qi, q, by rw [mul_comm]; exact hq, hq⟩, rfl⟩).pow 4

/-- **Relaxing the unused primes one at a time** (tex L4185–4188, L4222, L4289–4291): if, for
every intermediate stage `T ⊆ U` and every `p ∈ U \ T`, the coordinate `u (insert p T)` relaxed at
`p` and `u T` are related by a triangular model at `p` as in `single_prime_47_of_model`, then
`(∏_{p ∈ U} l_p) u_rel = (∏_{p ∈ U} e_p² ε_p) u_prim` with `ε_p = q_p⁻⁴`. This is the multi-prime
input of RC15's `corrected_eq` (`ũ_x = η_x u_{rel,x} = (∏ ε_p) u_{prim,x}`). -/
theorem prod_relax_of_models [IsDomain K] {ι : Type*} [DecidableEq ι] (U : Finset ι)
    (F : ι → Matrix (Fin 2) (Fin 2) K) (q qi a z zi : ι → K) (u : Finset ι → K)
    (hq : ∀ p ∈ U, q p * qi p = 1) (ha : ∀ p ∈ U, (F p).trace = a p) (hd : ∀ p ∈ U, (F p).det = q p)
    (hmodel : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T → ∃ (n : ℕ) (DP : Matrix (Fin n) (Fin n) K)
      (X : Matrix (Fin n) (Fin 2 ⊕ Fin 2) K) (zP wP : Fin n → K) (zR wR : Fin n ⊕ (Fin 2 ⊕ Fin 2) → K),
      (∀ i, zR (Sum.inl i) = pointFactor (a p) (z p) (zi p) * zP i) ∧
      (∀ i, wR (Sum.inl i) = pointFactor (a p) (z p) (zi p) * wP i) ∧
      IsCoordOn (fromBlocks DP X 0 (twoPlaceBlock (F p) (q p) (z p) (zi p))) zR wR (u (insert p T)) ∧
      IsClassFunctionalCoord DP zP wP (u T) ∧ DP.adjugate ≠ 0) :
    (∏ p ∈ U, quotientFactor (F p) (qi p) (z p) (zi p)) * u U =
      (∏ p ∈ U, pointFactor (a p) (z p) (zi p) ^ 2 * qi p ^ 4) * u ∅ := by
  refine prod_relax U (fun p => quotientFactor (F p) (qi p) (z p) (zi p))
    (fun p => pointFactor (a p) (z p) (zi p)) (fun p => qi p ^ 4) u ?_
  intro T hT p hp hpT
  obtain ⟨n, DP, X, zP, wP, zR, wR, hz, hw, hR, hP, hadj⟩ := hmodel T hT p hp hpT
  exact (single_prime_47_of_model DP X (F p) (q p) (qi p) (a p) (z p) (zi p) (hq p hp) (ha p hp)
    (hd p hp) zP wP zR wR (u T) (u (insert p T)) hz hw hR hP hadj).1

end ZInQ.Contrib.CloudB3RC53.CommonCoordinate
