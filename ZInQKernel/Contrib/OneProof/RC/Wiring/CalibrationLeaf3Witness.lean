import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeaf3
import ZInQKernel.Contrib.OneProof.RC.Height.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Curve

/-!
**Theorem 5.3, Lane RC0 round 4: the calibration leaf `CalibrationModelH` at a trivial family**

As batch 3's witness of `CalibrationModelC` at the trivial family, for the round-4 leaf: every
field of `CalibrationModelH` is constructed at the address `0` of the family without primes
(`k = −1`, so the conditions at `p ∣ k`, the good models and the Edixhoven print are empty; `K = ℚ(i)`;
the moving prime `r = 1`, `a_r = 3`, `χ = 1`, `c_E = 0`, `B = 1`; the Kummer model `D_K = (0)` with
`z = λ = u_K = 1`), with the quotient block now given by its local blocks: the two-place block of
the Frobenius `[[3, −1], [1, 0]]` at `r = 1`, `z = z' = 1` (determinant `N² = 1`), no active places
(`ω(1) = 0`), and the changes of basis `P_W = 1`, `Q_W = blocks⁻¹`, so `D_W = 1`. Cassels–Milne at
the genuine Néron–Tate heights (`hmilne`, a PRINT field) is the one hypothesis. PROVED; nothing here
is used by the deduction.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate ZInQ.Contrib.CloudB3RC53.Calibration
  ZInQ.Manuscript.RC.Height

/-- The family without primes or address bits. -/
def famTriv : Family := ⟨0, ∅, fun _ => 0⟩

theorem omega_famTriv : omega (famTriv.h 0) = 0 := by
  simp [omega]

instance isEmpty_famTriv : IsEmpty (Fin (4 * omega (famTriv.h 0))) := by
  rw [omega_famTriv, mul_zero]
  infer_instance

/-- Interface data with `k = −1`, `u_prim = 1`, `j_rc = 0` (the other fields are irrelevant). -/
def exDataCal : RCData 1 where
  S := ∅
  prepared _ := True
  Lstar _ := 1
  jgen _ := 0
  jrc _ _ := 0
  hstar := -7
  stages := pure 0
  Mθ _ := 0
  aθ _ _ := 0
  admissible _ _ := False
  δo := 0
  kfin := -1
  uPrim _ _ := 1
  uTilde _ _ := 1

/-- The Frobenius at the moving prime of the example: trace `3`, determinant `1`. -/
def frobMov : Matrix (Fin 2) (Fin 2) ℚ_[2] := !![3, -1; 1, 0]

theorem frobMov_map_central : (frobMov.map PowerSeries.C).map central = frobMov := by
  ext i j
  simp [central]

/-- `2^{s(E) + s(E^{(−1)})}`, the order of `Ш(ℬ)[2^∞]` in the example. -/
def shaBCal : ℕ :=
  2 ^ (shaLength (Etw 1 (famTriv.h 0)) + shaLength (Etw 1 (famTriv.h 0 * exDataCal.kfin)))

instance : (Ecurve 1).IsElliptic := ZInQ.Manuscript.RC.Nonvanishing.curve_nat_isElliptic one_pos

/-- The quotient index set at `famTriv`. -/
abbrev κTriv : Type := (Fin 2 ⊕ Fin 2) ⊕ Fin (4 * omega (famTriv.h 0))

/-- The (empty) active block. -/
def bactTriv : Matrix (Fin (4 * omega (famTriv.h 0))) (Fin (4 * omega (famTriv.h 0)))
    (PowerSeries ℚ_[2]) := 0

/-- The local blocks: the two-place block at `r = 1`, `z = z' = 1`, and the active block. -/
def blocksTriv : Matrix κTriv κTriv (PowerSeries ℚ_[2]) :=
  (fromBlocks (twoPlaceBlock (frobMov.map PowerSeries.C) ((1 : ℕ) : PowerSeries ℚ_[2]) 1 1) 0 0
    bactTriv).submatrix (Equiv.refl _) (Equiv.refl _)

theorem blocksTriv_det : blocksTriv.det = 1 := by
  rw [blocksTriv, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_twoPlaceBlock, quotientDet,
    det_smul_sub_smul_one, Matrix.det_isEmpty (A := bactTriv), mul_one]
  have hdet : (frobMov.map PowerSeries.C).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, frobMov, Matrix.det_fin_two_of]
    norm_num
  have htr : (frobMov.map PowerSeries.C).trace = 3 := by
    rw [Matrix.trace_fin_two]
    simp [frobMov, map_ofNat]
  rw [hdet, htr]
  norm_num

/-- The class and functional `(1, 0, …, 0)` of the primitive model. -/
def zTriv : Fin 1 ⊕ κTriv → PowerSeries ℚ_[2] := Sum.elim (fun _ => 1) (fun _ => 0)

theorem hP_triv : IsCoordOn (fromBlocks (0 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2])) 0 0
    (1 : Matrix κTriv κTriv (PowerSeries ℚ_[2]))) zTriv zTriv 1 := by
  rw [← diagonal_zero, ← diagonal_one, fromBlocks_diagonal]
  unfold IsCoordOn
  rw [adjugate_diagonal]
  ext x y
  rcases x with x | x <;> rcases y with y | y
  · fin_cases x; fin_cases y
    simp only [vecMulVec_apply, zTriv, Sum.elim_inl, Matrix.smul_apply, diagonal_apply_eq,
      smul_eq_mul]
    rw [Finset.prod_eq_one]
    intro j hj
    rcases j with j | j
    · fin_cases j; exact absurd rfl (Finset.ne_of_mem_erase hj)
    · rfl
  · simp [vecMulVec_apply, diagonal_apply_ne, zTriv]
  · simp [vecMulVec_apply, diagonal_apply_ne, zTriv]
  · simp only [vecMulVec_apply, zTriv, Sum.elim_inr, mul_zero, Matrix.smul_apply, smul_eq_mul]
    by_cases hxy : x = y
    · subst hxy
      rw [diagonal_apply_eq, Finset.prod_eq_zero (i := Sum.inl 0)]
      · simp
      · simp
      · rfl
    · rw [diagonal_apply_ne _ (fun h => hxy (Sum.inr_injective h)), mul_zero]

/-- **`CalibrationModelH` at the trivial family** (PROVED), conditional on Cassels–Milne at the
genuine Néron–Tate heights with `|Ш(𝒜)| = |tors| = 1`, `|Ш(ℬ)| = shaBCal`, trivial component
numbers and the period ratio `2`. -/
def calibrationModelH_of_milne
    (hm : ∀ (gA : ((qtwist (Ecurve 1) (famTriv.h 0 : ℚ)).baseChange GaussField).toAffine.Point)
      (gB : ((qtwist (Ecurve 1) (famTriv.h 0 : ℚ)).baseChange ℚ).toAffine.Point ×
        ((qtwist (Ecurve 1) ((famTriv.h 0 : ℚ) * (exDataCal.kfin : ℚ))).baseChange ℚ).toAffine.Point),
      IsFreeGenerator gA → IsFreeGenerator gB →
      MilneIsogenyInvariance 1 shaBCal 1 1 1 1 1 1 gA.canonicalHeight
        (heightB (Ecurve 1) (famTriv.h 0 : ℚ) (exDataCal.kfin : ℚ) gB) 1 ((2 : ℚ) * 1)) :
    CalibrationModelH exDataCal 0 0 famTriv 0 where
  shaA := 1
  shaB := shaBCal
  tA := 1
  tB := 1
  shaA_ne := one_ne_zero
  shaB_ne := by unfold shaBCal; positivity
  tA_ne := one_ne_zero
  tB_ne := one_ne_zero
  Scomp := ∅
  cA _ := 1
  cB _ := 1
  hTS := by simp [exDataCal]
  hcpos _ _ := one_pos
  hcancel _ _ _ := rfl
  hA1 _ hp := by simp [exDataCal] at hp
  hodd _ hp := by simp [exDataCal] at hp
  hram _ hp := by simp [exDataCal] at hp
  goodModel _ hp := absurd hp (by simp [exDataCal])
  hEdix p hp _ hpk _ _ := by
    exfalso
    have h1 : p ∣ 1 := by simpa [exDataCal] using Int.natCast_dvd.mp hpk
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  K := GaussField
  quad := by simpa [exDataCal] using GaussField.quadData
  aPull := 2
  bPull := 2
  hab := by norm_num
  gam := 1
  kap := 1
  hgam := by norm_num
  hkap := by norm_num
  OmA := 1
  hOmA := one_ne_zero
  rhoOm := 2
  hcv := by norm_num
  hmilne gA gB hA hB := by simpa using hm gA gB hA hB
  hsB := by simp [shaBCal]
  hgB := by simp
  rmov := 1
  amov := 3
  chimov := 1
  Bexp := 1
  cE := 0
  hchi := Or.inl rfl
  hrmov := by norm_num
  hnd := by norm_num
  hcB := le_refl _
  nK := 1
  κ := κTriv
  DK := 0
  X := 0
  DW := 1
  zK _ := 1
  wK _ := 1
  zP := zTriv
  wP := zTriv
  uK := 1
  hz _ := rfl
  hw _ := rfl
  hP := hP_triv
  hKc := by
    unfold IsClassFunctionalCoord
    ext i j; fin_cases i; fin_cases j
    simp [adjugate_fin_one, vecMulVec_apply]
  hadj := by rw [adjugate_fin_one]; exact one_ne_zero
  hK := by simp [exDataCal, central, v2, diskContribution]
  Fr := frobMov.map PowerSeries.C
  hFtr := by
    rw [frobMov_map_central]
    simp [frobMov, Matrix.trace_fin_two_of]
  hFdet := by
    rw [frobMov_map_central]
    simp [frobMov, Matrix.det_fin_two_of]
  PW := 1
  QW := blocksTriv⁻¹
  eW := Equiv.refl _
  zmov := 1
  zmov' := 1
  Bact := bactTriv
  hDW := by
    show (1 : Matrix κTriv κTriv (PowerSeries ℚ_[2])) = 1 * blocksTriv * blocksTriv⁻¹
    rw [Matrix.one_mul, mul_nonsing_inv _ (by rw [blocksTriv_det]; exact isUnit_one)]
  hPW := by simp [central, v2]
  hQW := by
    rw [det_nonsing_inv, blocksTriv_det, Ring.inverse_one]
    simp [central, v2]
  hzmov := by simp [central]
  hzmov' := by simp [central]
  hact := Subsingleton.elim _ _

/-- **Non-vacuity of `CalibrationModelH`, conditional on Cassels–Milne** (PROVED). -/
theorem nonempty_calibrationModelH_of_milne
    (hm : ∀ (gA : ((qtwist (Ecurve 1) (famTriv.h 0 : ℚ)).baseChange GaussField).toAffine.Point)
      (gB : ((qtwist (Ecurve 1) (famTriv.h 0 : ℚ)).baseChange ℚ).toAffine.Point ×
        ((qtwist (Ecurve 1) ((famTriv.h 0 : ℚ) * (exDataCal.kfin : ℚ))).baseChange ℚ).toAffine.Point),
      IsFreeGenerator gA → IsFreeGenerator gB →
      MilneIsogenyInvariance 1 shaBCal 1 1 1 1 1 1 gA.canonicalHeight
        (heightB (Ecurve 1) (famTriv.h 0 : ℚ) (exDataCal.kfin : ℚ) gB) 1 ((2 : ℚ) * 1)) :
    Nonempty (CalibrationModelH exDataCal 0 0 famTriv 0) :=
  ⟨calibrationModelH_of_milne hm⟩

end ZInQ.Manuscript.RC.Wiring
