import ZInQKernel.Contrib.OneProof.RC.Even.Membership
import ZInQKernel.Contrib.OneProof.RC.Determinant.SmithLength

/-!
# Lane RC22 (glue sweep), even share: the Smith step of (E.4a)

Lane RC11's `E4a_nonneg` (`Membership.lean`, (E.4a), tex 7572–7589) is the arithmetic of
`v_𝔭(u_x) = v(α) − Σ_i v(d_i) = ℓ_R(H¹/Rz) − ℓ_R H² ≥ 0` over the DVR `R = A_𝔭`, with the step
`Σ_i v(d_i) = ℓ_R H²` taken as the hypothesis `hsmith` (GLUE: the Smith decomposition of a finite
free model with universal coefficients; tex 7567–7581: "Let `d_1, …, d_r` be the nonzero
Smith entries of a finite free model … its degree-two cohomology is torsion").

The step is PROVED in the tree by lane RC7 (`Determinant.length_quotient_range_eq_ord_det`, via
Mathlib's Smith normal form): over a principal ideal domain, the cokernel of a square matrix `X`
with `det X ≠ 0` has length `ord(det X)`, and `det X` is associated to the product of the Smith
entries. Over a DVR, `ord(d) = ℓ_R(R/dR) = v(d)` (lane RC11's own `length_quotient_dvr`). So:

* `length_coker_eq_addVal_det` — `ℓ_R(Rⁿ / X Rⁿ) = v(det X)` for a square `X` over a DVR with
  `det X ≠ 0` (the sum of the valuations of its Smith entries);
* `E4a_of_smith` — (E.4a) with `hsmith` discharged, for `H² = Rⁿ / X Rⁿ` the cokernel of the
  degree-two differential `X` of the finite free model.

Not done here: the identification of `H²(C_x⁺ ⊗ R)` with the cokernel of a square nonsingular
differential (the model's shape: cohomology only in degrees one and two, `H²` torsion), which is
part of lane RC11's ELLIOT input. All results here are `PROVED`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Even

/-- **The Smith count over a DVR** (PROVED; tex 7567–7581, the step `Σ_i v_𝔭(d_i) = ℓ_R H²` of
(E.4a)): for a square matrix `X` over a discrete valuation ring `R` with `det X ≠ 0`,
`ℓ_R(Rⁿ / X Rⁿ) = v(det X)`. Discharger of the GLUE `hsmith` of lane RC11's `E4a_nonneg`; from lane
RC7's `Determinant.length_quotient_range_eq_ord_det` (Smith normal form over a PID) and lane RC11's
`length_quotient_dvr`. -/
theorem length_coker_eq_addVal_det {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n R)
    (hX : X.det ≠ 0) :
    Module.length R ((n → R) ⧸ LinearMap.range X.mulVecLin) =
      (IsDiscreteValuationRing.addVal R X.det : ℕ∞) := by
  rw [ZInQ.Manuscript.RC.Determinant.length_quotient_range_eq_ord_det X hX]
  exact ZInQ.Manuscript.RC.Even.length_quotient_dvr hX

/-- **(E.4a) with the Smith step discharged** (tex 7572–7589; PROVED from the remaining inputs of
lane RC11's `E4a_nonneg`: the inverse-determinant identity `hu` (with `Σ_i v(d_i) = v(det X)`),
`hquot` and Kato's bound (K2) `hK2`, all ELLIOT). Here `H²` of the finite free model over the DVR
`R = A_𝔭` is the cokernel of its square degree-two differential `X`, `det X ≠ 0`, of length
`lH2`; the GLUE `Σ_i v(d_i) = ℓ_R H²` of `E4a_nonneg` (hypothesis `hsmith`) is
`length_coker_eq_addVal_det`. Consumer: lane RC11's `E4a_nonneg`. -/
theorem E4a_of_smith {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n R) (hX : X.det ≠ 0)
    {vu vα lquot : ℤ} {lH2 : ℕ}
    (hH2 : Module.length R ((n → R) ⧸ LinearMap.range X.mulVecLin) = lH2)
    (hu : vu = vα - ((IsDiscreteValuationRing.addVal R X.det).toNat : ℤ))
    (hquot : lquot = vα) (hK2 : (lH2 : ℤ) ≤ lquot) :
    vu = lquot - lH2 ∧ 0 ≤ vu := by
  have hfin : IsDiscreteValuationRing.addVal R X.det ≠ ⊤ := fun h =>
    hX ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)
  have hlen : (((IsDiscreteValuationRing.addVal R X.det).toNat : ℕ) : ℕ∞) = lH2 := by
    rw [← hH2, length_coker_eq_addVal_det X hX]
    exact ENat.natCast_toNat hfin
  have hlen' : (IsDiscreteValuationRing.addVal R X.det).toNat = lH2 := by exact_mod_cast hlen
  have hsmith : ((IsDiscreteValuationRing.addVal R X.det).toNat : ℤ) = (lH2 : ℤ) := by
    rw [hlen']
  exact ZInQ.Manuscript.RC.Even.E4a_nonneg hu hsmith hquot hK2

end ZInQ.Manuscript.RC.GlueSweep.Even
