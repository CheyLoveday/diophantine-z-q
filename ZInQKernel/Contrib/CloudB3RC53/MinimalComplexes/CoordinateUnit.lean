import ZInQKernel.Contrib.OneProof.RC.Central.Coordinate

/-!
# RC53 MinimalComplexes: cancelling unit disks changes the coordinate only by a unit

Lemma `ex:arith-base-zero`, tex L4360–4366:

> In the second case the generic and central dimensions agree in every degree. Hence no disk with
> `r > 0` occurs. All cancellable disks have unit differential, so integral determinant base change
> identifies the coordinate of `[z] ⊗ [λ_z]` with the coordinate of its central tensor, in the
> retained determinant basis.

The central lane's base-zero file (`RC/Central/BaseZero.lean`, module docstring, its lines 18–24)
records that passing from the actual complex to the two-term model "multiplies the coordinate by a
unit, absorbed into `ε₀`". This file proves that statement on the two-term model, in the central
lane's own form `IsClassFunctionalCoord D z w u` (`vecMulVec z w = u • adj D`, Definition
`ex:arith-coordinate`, tex L3882–3892), which it imports.

Nodes (PROVED):
* `CoordinateBaseChangeUnit`: a change of bases `D ↦ P D Q` (`P, Q` invertible) transports cycle
  and functional to `Q⁻¹ z`, `w P⁻¹` and multiplies the coordinate by `(det P det Q)⁻¹`, and
  conversely.
* `CoordinateUnitDiskCancel`: for the Smith form `D₀ = diag(δ, 1, …, 1)` (one entry `δ` and `m` unit
  disks) and cycles `z, w`, the coordinate of `D₀` equals the coordinate of the `1 × 1` model `(δ)`
  on the first components: cancelling unit disks changes the coordinate by the unit `1`.
* `CoordinateCancelUnit`: combining both, if `P D Q = D₀`, the coordinate of `D` is
  `det P · det Q` times the coordinate of the `1 × 1` model on the transformed cycle and functional.
* `RegularZeroUnitTransfer` and `CoordinateCancelRegularZero`: over a ring `A` with a map to a field
  `F` and a residue map `ρ`, multiplying the generic coordinate by the image of a unit of `A`
  preserves "regular with value `0` at the centre" (`∃ u₀ : A, ι u₀ = u ∧ ρ u₀ = 0`, the conclusion
  shape of `baseZero_core`), so the central lane's conclusion for the cancelled model gives the same
  conclusion for the actual one.
-/

namespace ZInQ.Contrib.CloudB3RC53.MinimalComplexes

open Matrix ZInQ.Manuscript.RC.Central

/-- `M⁻¹ = det(M)⁻¹ • adj M`, with `det M` a unit. -/
theorem inv_eq_smul_adjugate {K : Type*} [CommRing K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    M⁻¹ = Ring.inverse M.det • M.adjugate := Matrix.inv_def M

/-- **Change of bases multiplies the coordinate by `(det P det Q)⁻¹`** (tex L4363–4366: "integral
determinant base change identifies the coordinate [...] in the retained determinant basis").
Over a commutative ring `K`, for invertible `P, Q`, the coordinate `u` of `(D, z, w)` and the
coordinate of `(P D Q, Q⁻¹ z, w P⁻¹)` are related by the factor `(det P det Q)⁻¹`, in both
directions. Classification: PROVED. -/
def CoordinateBaseChangeUnit : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (D P Q : Matrix (Fin n) (Fin n) K) (z w : Fin n → K) (u : K),
    IsUnit P.det → IsUnit Q.det →
      (IsClassFunctionalCoord D z w u ↔
        IsClassFunctionalCoord (P * D * Q) (Q⁻¹ *ᵥ z) (w ᵥ* P⁻¹)
          (Ring.inverse (P.det * Q.det) * u))

theorem coordinateBaseChangeUnit_proof : CoordinateBaseChangeUnit := by
  intro K _ n D P Q z w u hP hQ
  have hadj : (P * D * Q).adjugate = Q.adjugate * D.adjugate * P.adjugate := by
    rw [adjugate_mul_distrib, adjugate_mul_distrib, Matrix.mul_assoc]
  have hvv : vecMulVec (Q⁻¹ *ᵥ z) (w ᵥ* P⁻¹) = Q⁻¹ * vecMulVec z w * P⁻¹ := by
    rw [← mul_vecMulVec, ← vecMulVec_mul, Matrix.mul_assoc]
  have hinv : Ring.inverse (P.det * Q.det) = Ring.inverse P.det * Ring.inverse Q.det := by
    rw [Ring.mul_inverse_rev, mul_comm]
  unfold IsClassFunctionalCoord
  constructor
  · intro h
    rw [hvv, h, hadj, inv_eq_smul_adjugate Q, inv_eq_smul_adjugate P]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hinv]
    congr 1
    ring
  · intro h
    have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
    have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
    have hzw : vecMulVec z w = Q * vecMulVec (Q⁻¹ *ᵥ z) (w ᵥ* P⁻¹) * P := by
      rw [hvv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_assoc, hPP,
        Matrix.mul_one]
    rw [hzw, h, hadj, Matrix.mul_smul, Matrix.smul_mul]
    have e : Q * (Q.adjugate * D.adjugate * P.adjugate) * P =
        (Q * Q.adjugate) * D.adjugate * (P.adjugate * P) := by
      simp only [Matrix.mul_assoc]
    rw [e, mul_adjugate, adjugate_mul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, hinv]
    congr 1
    calc Ring.inverse P.det * Ring.inverse Q.det * u * (P.det * Q.det)
        = (Ring.inverse P.det * P.det) * (Ring.inverse Q.det * Q.det) * u := by ring
      _ = u := by rw [Ring.inverse_mul_cancel _ hP, Ring.inverse_mul_cancel _ hQ]; ring

/-- **Cancelling unit disks does not change the coordinate** (tex L4362–4366: "All cancellable
disks have unit differential"). For `D₀ = diag(δ, 1, …, 1) ∈ K^{(m+1)×(m+1)}` (the two-term model in
Smith form: one entry `δ` and `m` unit disks) and cycles `z` (`D₀ z = 0`) and `w` (`w D₀ = 0`), the
coordinate of `(D₀, z, w)` is the coordinate of the `1 × 1` model `(δ)` with cycle `z 0` and
functional `w 0`. Classification: PROVED. -/
def CoordinateUnitDiskCancel : Prop :=
  ∀ (K : Type) [CommRing K] (m : ℕ) (δ : K) (z w : Fin (m + 1) → K) (u : K),
    let D₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
      Matrix.diagonal (Fin.cons δ (fun _ => 1) : Fin (m + 1) → K)
    D₀ *ᵥ z = 0 → w ᵥ* D₀ = 0 →
      (IsClassFunctionalCoord D₀ z w u ↔
        IsClassFunctionalCoord (Matrix.of fun _ _ => δ : Matrix (Fin 1) (Fin 1) K)
          (fun _ => z 0) (fun _ => w 0) u)

theorem coordinateUnitDiskCancel_proof : CoordinateUnitDiskCancel := by
  intro K _ m δ z w u D₀ hz hw
  set v : Fin (m + 1) → K := Fin.cons δ (fun _ => 1) with hv
  have hv0 : v 0 = δ := rfl
  have hvs : ∀ k : Fin m, v k.succ = 1 := fun k => rfl
  -- the cycle conditions
  have hzi : ∀ i, v i * z i = 0 := fun i => by
    have := congrFun hz i
    simpa [D₀, mulVec_diagonal] using this
  have hwi : ∀ i, w i * v i = 0 := fun i => by
    have := congrFun hw i
    simpa [D₀, vecMul_diagonal] using this
  have hz0 : ∀ i, i ≠ 0 → z i = 0 := fun i hi => by
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hi
    have := hzi k.succ; rwa [hvs, one_mul] at this
  have hw0 : ∀ i, i ≠ 0 → w i = 0 := fun i hi => by
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hi
    have := hwi k.succ; rwa [hvs, mul_one] at this
  -- the adjugate of `D₀`
  have hadj : D₀.adjugate = Matrix.diagonal fun i => ∏ j ∈ Finset.univ.erase i, v j :=
    adjugate_diagonal v
  have hadj00 : D₀.adjugate 0 0 = 1 := by
    rw [hadj, diagonal_apply_eq]
    apply Finset.prod_eq_one
    intro j hj
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr (Finset.ne_of_mem_erase hj)
    exact hvs k
  have hadjii : ∀ i, i ≠ 0 → ∃ c, D₀.adjugate i i = δ * c := fun i hi => by
    rw [hadj, diagonal_apply_eq]
    have h0 : (0 : Fin (m + 1)) ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨fun h => hi h.symm, Finset.mem_univ _⟩
    exact ⟨_, (Finset.mul_prod_erase _ _ h0).symm⟩
  unfold IsClassFunctionalCoord
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h 0) 0
    simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, hadj00, mul_one] at this
    simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, adjugate_fin_one]
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0, Matrix.one_apply_eq, mul_one]
    exact this
  · intro h
    have hu : z 0 * w 0 = u := by
      have := congrFun (congrFun h 0) 0
      simpa [vecMulVec_apply, adjugate_fin_one] using this
    ext i j
    simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = 0
      · subst hi; rw [hadj00, mul_one, hu]
      · obtain ⟨c, hc⟩ := hadjii i hi
        rw [hz0 i hi, zero_mul, hc, ← hu]
        have : δ * z 0 = 0 := by have := hzi 0; rwa [hv0] at this
        calc (0 : K) = (δ * z 0) * w 0 * c := by rw [this]; ring
          _ = z 0 * w 0 * (δ * c) := by ring
    · have hoff : D₀.adjugate i j = 0 := by rw [hadj, diagonal_apply_ne _ hij]
      rw [hoff, mul_zero]
      by_cases hi : i = 0
      · subst hi; rw [hw0 j (fun h => hij h.symm), mul_zero]
      · rw [hz0 i hi, zero_mul]

/-- **The coordinate of `D` is `det P det Q` times the coordinate of the cancelled `1 × 1` model**
(tex L4360–4366; the unit absorbed into `ε₀` by the central lane). If `P D Q = D₀ = diag(δ, 1, …, 1)`
with `P, Q` invertible and `z, w` are a cycle and a closed functional of `D`, then `u` is the
coordinate of `(D, z, w)` iff `(det P det Q)⁻¹ u` is the coordinate of the `1 × 1` model `(δ)` with
cycle `(Q⁻¹ z) 0` and functional `(w P⁻¹) 0`. Classification: PROVED. -/
def CoordinateCancelUnit : Prop :=
  ∀ (K : Type) [CommRing K] (m : ℕ) (D P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (δ : K)
    (z w : Fin (m + 1) → K) (u : K),
    IsUnit P.det → IsUnit Q.det →
    P * D * Q = Matrix.diagonal (Fin.cons δ (fun _ => 1) : Fin (m + 1) → K) →
    D *ᵥ z = 0 → w ᵥ* D = 0 →
      (IsClassFunctionalCoord D z w u ↔
        IsClassFunctionalCoord (Matrix.of fun _ _ => δ : Matrix (Fin 1) (Fin 1) K)
          (fun _ => (Q⁻¹ *ᵥ z) 0) (fun _ => (w ᵥ* P⁻¹) 0) (Ring.inverse (P.det * Q.det) * u))

theorem coordinateCancelUnit_proof : CoordinateCancelUnit := by
  intro K _ m D P Q δ z w u hP hQ hD hz hw
  have hz' : (P * D * Q) *ᵥ (Q⁻¹ *ᵥ z) = 0 := by
    rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQ, Matrix.mul_one,
      ← mulVec_mulVec, hz, mulVec_zero]
  have hw' : (w ᵥ* P⁻¹) ᵥ* (P * D * Q) = 0 := by
    rw [vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hP,
      Matrix.one_mul, ← vecMul_vecMul, hw, zero_vecMul]
  rw [coordinateBaseChangeUnit_proof K (m + 1) D P Q z w u hP hQ, hD]
  rw [hD] at hz' hw'
  exact coordinateUnitDiskCancel_proof K m δ _ _ _ hz' hw'

/-- **Regularity with value `0` at the centre is unchanged by a unit factor** (the conclusion shape
of the central lane's `baseZero_core`, `∃ u₀ : A, algebraMap A F u₀ = uprim ∧ ρ u₀ = 0`). For a ring
map `ι : A → F`, a residue map `ρ : A → k`, a unit `c` of `A` and `u ∈ F`:
`u` is regular with value `0` iff `ι(c) u` is. Classification: PROVED. -/
def RegularZeroUnitTransfer : Prop :=
  ∀ (A F k : Type) [CommRing A] [CommRing F] [CommRing k] (ι : A →+* F) (ρ : A →+* k) (c : Aˣ)
    (u : F),
    (∃ u₀ : A, ι u₀ = u ∧ ρ u₀ = 0) ↔ (∃ u₀ : A, ι u₀ = ι c * u ∧ ρ u₀ = 0)

theorem regularZeroUnitTransfer_proof : RegularZeroUnitTransfer := by
  intro A F k _ _ _ ι ρ c u
  constructor
  · rintro ⟨u₀, h1, h2⟩
    exact ⟨c * u₀, by rw [map_mul, h1], by rw [map_mul, h2, mul_zero]⟩
  · rintro ⟨u₀, h1, h2⟩
    refine ⟨↑c⁻¹ * u₀, ?_, by rw [map_mul, h2, mul_zero]⟩
    rw [map_mul, h1, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-- **The central lane's conclusion transfers through unit-disk cancellation** (tex L4360–4366;
`RC/Central/BaseZero.lean` L18–24). Let `A → F` be a ring map to a field and `ρ : A → k` a residue
map; let `D, P, Q` be integral matrices with `P, Q` invertible over `A` and `P D Q = diag(δ, 1, …, 1)`,
and `z, w` an integral cycle and closed functional of `D`. If `uprim` is the generic coordinate of
`(D, z, w)` and `u₁` the generic coordinate of the cancelled `1 × 1` model `(δ)` on the transformed
cycle and functional, then `uprim = ι(det P det Q) u₁`, and `uprim` is regular with value `0` at
the centre iff `u₁` is. Classification: PROVED. -/
def CoordinateCancelRegularZero : Prop :=
  ∀ (A F k : Type) [CommRing A] [Field F] [CommRing k] (ι : A →+* F) (ρ : A →+* k) (m : ℕ)
    (D P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (δ : A) (z w : Fin (m + 1) → A) (uprim u₁ : F),
    IsUnit P.det → IsUnit Q.det →
    P * D * Q = Matrix.diagonal (Fin.cons δ (fun _ => 1) : Fin (m + 1) → A) →
    D *ᵥ z = 0 → w ᵥ* D = 0 →
    IsClassFunctionalCoord (D.map ι) (fun i => ι (z i)) (fun i => ι (w i)) uprim →
    IsClassFunctionalCoord (Matrix.of fun _ _ => ι δ : Matrix (Fin 1) (Fin 1) F)
      (fun _ => ι ((Q⁻¹ *ᵥ z) 0)) (fun _ => ι ((w ᵥ* P⁻¹) 0)) u₁ →
      uprim = ι (P.det * Q.det) * u₁ ∧
      ((∃ u₀ : A, ι u₀ = u₁ ∧ ρ u₀ = 0) → (∃ u₀ : A, ι u₀ = uprim ∧ ρ u₀ = 0))

theorem coordinateCancelRegularZero_proof : CoordinateCancelRegularZero := by
  intro A F k _ _ _ ι ρ m D P Q δ z w uprim u₁ hP hQ hD hz hw hu hu₁
  set Pm := P.map ι
  set Qm := Q.map ι
  have hdetP : Pm.det = ι P.det := by rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hdetQ : Qm.det = ι Q.det := by rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hPm : IsUnit Pm.det := by rw [hdetP]; exact hP.map ι
  have hQm : IsUnit Qm.det := by rw [hdetQ]; exact hQ.map ι
  -- base change of the identities along `ι`
  have hmapv : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) A) (v : Fin b → A),
      (M.map ι *ᵥ fun i => ι (v i)) = fun i => ι ((M *ᵥ v) i) := fun M v => by
    ext i; simp [mulVec, dotProduct, map_sum]
  have hmapv' : ∀ {a b : ℕ} (v : Fin a → A) (M : Matrix (Fin a) (Fin b) A),
      ((fun i => ι (v i)) ᵥ* M.map ι) = fun i => ι ((v ᵥ* M) i) := fun v M => by
    ext i; simp [vecMul, dotProduct, map_sum]
  have hinvmap : ∀ M : Matrix (Fin (m + 1)) (Fin (m + 1)) A, IsUnit M.det →
      (M.map ι)⁻¹ = M⁻¹.map ι := fun M hM =>
    Matrix.inv_eq_right_inv (by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv M hM, Matrix.map_one _ ι.map_zero ι.map_one])
  have hDm : Pm * D.map ι * Qm =
      Matrix.diagonal (Fin.cons (ι δ) (fun _ => 1) : Fin (m + 1) → F) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hD]
    ext i j
    by_cases hij : i = j
    · subst hij
      refine Fin.cases ?_ (fun l => ?_) i <;> simp
    · simp [diagonal_apply_ne _ hij]
  have hzm : D.map ι *ᵥ (fun i => ι (z i)) = 0 := by rw [hmapv, hz]; ext; simp
  have hwm : (fun i => ι (w i)) ᵥ* D.map ι = 0 := by rw [hmapv', hw]; ext; simp
  have key := (coordinateCancelUnit_proof F m (D.map ι) Pm Qm (ι δ) _ _ uprim hPm hQm hDm hzm hwm).1 hu
  rw [hinvmap Q hQ, hinvmap P hP, hmapv, hmapv'] at key
  -- uniqueness of the `1 × 1` coordinate: `adj (δ) = 1`
  have h1 : Ring.inverse (Pm.det * Qm.det) * uprim = u₁ := by
    have a := congrFun (congrFun key 0) 0
    have b := congrFun (congrFun hu₁ 0) 0
    simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, adjugate_fin_one,
      Matrix.one_apply_eq, mul_one] at a b
    rw [← a, b]
  have hc : IsUnit (P.det * Q.det) := hP.mul hQ
  have huprim : uprim = ι (P.det * Q.det) * u₁ := by
    rw [← h1, hdetP, hdetQ, ← map_mul, ← mul_assoc, Ring.mul_inverse_cancel _ (hc.map ι), one_mul]
  refine ⟨huprim, fun h => ?_⟩
  rw [huprim]
  exact (regularZeroUnitTransfer_proof A F k ι ρ hc.unit u₁).1 h

/-- Non-vacuity: for the `1 × 1` model `D = (0)` (the case `m = 0`, `δ = 0` of
`CoordinateCancelUnit` with `P = Q = 1`), every cycle `a` and functional `b` have the coordinate
`a b`, so the coordinate predicate is satisfiable with a nonzero value. PROVED. -/
theorem coordinateCancel_example (K : Type) [CommRing K] (a b : K) :
    IsClassFunctionalCoord (0 : Matrix (Fin 1) (Fin 1) K) (fun _ => a) (fun _ => b) (a * b) := by
  unfold IsClassFunctionalCoord
  ext i j
  fin_cases i; fin_cases j
  simp [vecMulVec_apply, adjugate_fin_one]

end ZInQ.Contrib.CloudB3RC53.MinimalComplexes
