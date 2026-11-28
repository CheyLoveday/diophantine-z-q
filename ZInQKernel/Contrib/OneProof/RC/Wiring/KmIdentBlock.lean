import ZInQKernel.Contrib.OneProof.RC.Wiring.KmIdentCentral

/-!
# Theorem 5.3, Lane RC35: the Kummer block with the constructed Knudsen–Mumford identification

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141), its Kummer
coordinate (tex 3877–3890, 3895–3986, 4005–4018, 4050–4064).

The literature block `KummerCoordinateBlockLit` (`Wiring/CalibrationLeafLit.lean`) carries, as free
data, a finite set `S`, a topological `ℚ₂[[t]][G_{K,S}]`-module `M`, local conditions `Δ`, a
Knudsen–Mumford identification `I` of their Selmer complex over `ℚ₂[[t]]`, the coordinate transfer
`link : z_K ⊗ w_K = I.coord · adj D_K`, the central disk values `x_j` with `hx_j`, and the
disk-length identifications `hval_j` with the constructed integral disks. The text has no such
module: its Kummer complex is the ordinary compact Kummer complex `C_K` of `E^{(h)}/K`, central and
integral (tex 4007, 4057–4064, 3982–3984; see `KmIdentCentral`), and `ℚ₂[[t]]` does not occur in
it. So those fields are a DEPARTURE of form.

`KummerCoordinateBlockR` replaces them by the genuine central objects:

* Lit's `S`, `hSfin`, `M`, `Δ`, `hinj` (definition): replaced by the address's genuine Kummer
  data `G` (support `G.S`, the compact Kummer complex `compactCentralComplex G` of the central
  twist).
* Lit's `I` (PROVED): CONSTRUCTED, `KummerCoordinateBlockR.I` (the normalized core and the
  constructed integral disks of `C_K`; the genuine target in `KmIdentGenuine`, `genuineI`).
* Lit's `x_j`, `hx_j`, `hval_j` (PROVED): the disks ARE the constructed integral disk
  determinants (`KummerCoordinateBlockR.x₁`, `hx₁`, …; `hval_j` is `rfl`).
* Lit's `hu₀` (PROVED): `u₀ = 1` for the normalized core (`KummerCoordinateBlockR.hu₀`).
* Lit's `link` (GLUE): `link`, the central value of the leaf's Kummer coordinate is a `2`-adic
  unit times the constructed coordinate (the text's central Kummer comparison, tex 3953–3986,
  3489–3498, 4065–4080).
* Lit's `I.a`, `I.b` (data): the class and functional coefficients `aK`, `bK`, units of
  `ℚ₂[[t]]` (pinned by a central cycle and functional in `KmIdentPinned`).
* Lit's `aP` … `hbP` (ELLIOT): unchanged in form (lane RC34's point coefficients, stated against
  `aK`, `bK`).
* Lit's `arith` (ELLIOT): unchanged (see `RC53Assist/DiskOrders/Literature.lean`).
* Lit's literature inputs `hfinite`, `h2`, `hK`, `finite2`, `rank_one`: unchanged.

PROVED:
* `KummerCoordinateBlockR.tie`, `disk_valuations`: the order tie and the disk valuations of the
  constructed disks, from the eight book statements and `arith`.
* `KummerCoordinateBlockR.leafHK`: the field `hK` of the calibration leaf in its exact form.
* `KummerCoordinateBlockR.ofLit`: every literature block gives an R-block (the link from Lit's
  `link`, `hu₀` and `hval_j`), so the R-block asks for no more than Lit.
* `KummerCoordinateBlockR.toLitOfRealization`: the literature block from an R-block and a
  `ℚ₂[[t]]` Galois realization of the constructed identification (its `S`, `M`, `Δ`, `hinj`, the
  identification `J` with `J.a = aK`, `J.b = bK`, `v₂ J.u₀(0) = 0`, the central disks of `J`
  equal to the constructed disk determinants, and Lit's exact `link` for `J`): these are exactly
  the Lit fields with no counterpart in the text.
* `KummerCoordinateBlockR.ofCentralClassFunctional`: the block with the class and functional
  coefficients pinned by a central cycle and closed functional of the retained integral model.
* `KummerCoordinateBlockR.nonempty_of_inputs`: non-vacuity: for every genuine address datum `G`
  with the literature inputs and `arith`, and all `j`, `vL`, `m ≠ 0`, some leaf model
  `(D_K, z_K, w_K)` carries an R-block.

The human-review boundary is that of the literature form (H1–H3 of `CalibrationLeafLit`), with
the Knudsen–Mumford identification now constructed rather than an input: the identification of the
based torsion coordinate `kmCoord` with the coordinate of Definition `ex:arith-coordinate` is the
determinant functor of Knudsen–Mumford (PRINT, Math. Scand. 39 (1976) 19–55, quoted in
`KmIdentCentral`), and the transfer to the leaf's two-term model is the GLUE `link`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring.KmIdent

open Matrix CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.Calibration (central_mul v2_mul v2_intCast)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData DiskTie DiskArith
  valuation_unit_padicInt)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (compactCentralComplex centralCurve)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape centralDiskMatrix
  centralDiskMatrix_det_ne_zero)
open ZInQ.Manuscript.RC.SelmerComplex (GKS GaloisLocalConditions GenuineKummerModelIdentification)
open ZInQ.Manuscript.RC.Wiring (CalibrationBookProps KummerCoordinateBlockLit
  diskTie_of_literature)

attribute [local instance] Nat.fact_prime_two

/-! ### Units and valuations -/

section Units

/-- A `2`-adic unit has valuation zero in `ℚ₂`. Kind: PROVED. -/
theorem v2_coe_unit (μ : ℤ_[2]ˣ) : v2 ((μ : ℤ_[2]) : ℚ_[2]) = 0 := by
  rw [ZInQ.Contrib.RC53Assist.Calibration.v2_coe_padicInt _ μ.ne_zero, valuation_unit_padicInt μ]
  rfl

/-- An element of `ℚ₂` of valuation zero is a `2`-adic unit. Kind: PROVED. -/
theorem exists_unit_of_v2_eq_zero {x : ℚ_[2]} (hx : v2 x = 0) :
    ∃ μ : ℤ_[2]ˣ, ((μ : ℤ_[2]) : ℚ_[2]) = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [v2] at hx
  have hval : x.valuation = 0 := by
    have h := hx
    rw [v2, Padic.addValuation.apply hx0] at h
    exact_mod_cast h
  have hn : ‖x‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation hx0, hval]
    simp
  exact ⟨PadicInt.mkUnits hn, PadicInt.mkUnits_eq hn⟩

/-- Two nonzero `2`-adic integers of the same valuation differ by a unit (read in `ℚ₂`).
Kind: PROVED. -/
theorem exists_unit_of_valuation_eq {x y : ℤ_[2]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x.valuation = y.valuation) :
    ∃ η : ℤ_[2]ˣ, (x : ℚ_[2]) = (y : ℚ_[2]) * ((η : ℤ_[2]) : ℚ_[2]) := by
  have hy' : (y : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.2 hy
  have hq : v2 ((x : ℚ_[2]) * (y : ℚ_[2])⁻¹) = 0 := by
    rw [v2_mul, ZInQ.Contrib.RC53Assist.Calibration.v2_coe_padicInt _ hx,
      v2_inv_coe_padicInt _ hy, h, ← WithTop.coe_add]
    simp
  obtain ⟨η, hη⟩ := exists_unit_of_v2_eq_zero hq
  refine ⟨η, ?_⟩
  rw [hη]
  field_simp

/-- The inverse of a unit in `ℚ₂`. Kind: PROVED. -/
theorem coe_unit_inv (μ : ℤ_[2]ˣ) :
    (((μ⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) = ((μ : ℤ_[2]) : ℚ_[2])⁻¹ := by
  have h : (((μ⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) * ((μ : ℤ_[2]) : ℚ_[2]) = 1 := by
    rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
  exact eq_inv_of_mul_eq_one_left h

/-- The central value of the inverse of a unit of `ℚ₂[[t]]`. Kind: PROVED. -/
theorem central_units_inv (δ : (PowerSeries ℚ_[2])ˣ) :
    central ((δ⁻¹ : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) =
      (central (δ : PowerSeries ℚ_[2]))⁻¹ := by
  have h := congrArg central δ.inv_mul
  rw [central_mul] at h
  have h1 : central (1 : PowerSeries ℚ_[2]) = 1 := by simp [central]
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h

/-- A power series with nonzero central value is a unit. Kind: PROVED. -/
theorem isUnit_of_central_ne_zero {f : PowerSeries ℚ_[2]} (h : central f ≠ 0) : IsUnit f := by
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  rwa [← central_eq_constantCoeff]

/-- **The central valuation of `C(m) · a_P`** (the moving factor of the boundary (4.5)).
Kind: PROVED. -/
theorem v2_central_C_mul {m : ℤ} (hm : m ≠ 0) {aP : PowerSeries ℚ_[2]} {j vL : ℤ}
    (haP : v2 (central aP) = ((j + vL : ℤ) : WithTop ℤ)) :
    v2 (central (PowerSeries.C (m : ℚ_[2]) * aP)) =
      ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  have hC : central (PowerSeries.C (m : ℚ_[2])) = (m : ℚ_[2]) := by simp [central]
  rw [central_mul, v2_mul, hC, v2_intCast hm, haP, ← WithTop.coe_add]
  congr 1
  ring

/-- A power series of finite central valuation has nonzero central value. Kind: PROVED. -/
theorem central_ne_zero_of_v2 {f : PowerSeries ℚ_[2]} {k : ℤ}
    (h : v2 (central f) = (k : WithTop ℤ)) : central f ≠ 0 := by
  intro h0
  rw [h0] at h
  simp [v2] at h

end Units

/-! ### The block -/

section Block

/-- **The Kummer block with the constructed Knudsen–Mumford identification** (tex 3877–3909,
4005–4018, 4050–4064), for the two-term Kummer model `(D_K, z_K, w_K)` of the calibration leaf,
`j = j_rc(h, k)`, `vL = v₂L`, `m = a_r − 2χ_h(r)`, `tA = |𝒜(ℚ)_tors[2^∞]|`, `shaA = |Ш(𝒜)[2^∞]|`.

* `G` (data; tex 2723–2741, 3413–3463): the address's genuine Kummer data (support, curve,
  twist, full `2`-power torsion).
* `hfinite` … `rank_one` (tex 4005–4018): the literature inputs of `KummerCoordinateBlockLit`.
* `aK`, `bK` (data; tex 3895–3909): the free-line coefficients of the central class and
  functional.
* `link` (GLUE; tex 3953–3986, 3489–3498, 4065–4080): the leaf's Kummer coordinate has central
  value `ε · u_K(0)` for a `2`-adic unit `ε`, `u_K` the constructed coordinate.
* `aP` … `hbP` (ELLIOT; tex 3898–3906, 4061–4062): the point coefficients (`aK = m a_P`,
  `bK = m b_P`, `v₂ a_P(0) = v₂ b_P(0) = j + v₂L`).
* `arith` (ELLIOT; tex 4005–4018): the genuine orders are those of `𝒜(ℚ)_tors[2^∞]`,
  `Ш(𝒜)[2^∞]`.

Kind: definition (inputs). -/
structure KummerCoordinateBlockR (K : Type) [Field K] [NumberField K] (E₀ : WeierstrassCurve ℚ)
    (hZ : ℤ) {n : ℕ} (DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2]))
    (zK wK : Fin n → PowerSeries ℚ_[2]) (j vL m : ℤ) (tA shaA : ℕ) : Type 1 where
  /-- the genuine data of the address -/
  G : GenuineKummerData K E₀ hZ
  /-- finite generation of the integral compact central cohomology -/
  hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n)
  /-- the support contains the places above `2` -/
  h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S
  /-- `K` has no real places -/
  hK : IsTotallyComplex K
  /-- the `2`-primary torsion of the central twist over `K` is finite -/
  finite2 : ∀ [DecidableEq K],
    Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)
  /-- the integral central first cohomology has rank one -/
  rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1
  /-- the free-line coefficient of the central class -/
  aK : (PowerSeries ℚ_[2])ˣ
  /-- the free-line coefficient of the central functional -/
  bK : (PowerSeries ℚ_[2])ˣ
  /-- **the central Kummer comparison** (GLUE): the leaf's two-term Kummer model computes, at
  `t = 0` and up to a `2`-adic unit, the constructed ordinary Kummer coordinate -/
  link : ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2], Central.IsClassFunctionalCoord DK zK wK uK ∧
    central uK = ((ε : ℤ_[2]) : ℚ_[2]) * central (centralKMCoord G hfinite aK bK)
  /-- the free coefficient of the point in the class -/
  aP : PowerSeries ℚ_[2]
  /-- the free coefficient of the point in the functional -/
  bP : PowerSeries ℚ_[2]
  /-- the class coefficient is `m · a_P` -/
  ha : (aK : PowerSeries ℚ_[2]) = PowerSeries.C (m : ℚ_[2]) * aP
  /-- the functional coefficient is `m · b_P` -/
  hb : (bK : PowerSeries ℚ_[2]) = PowerSeries.C (m : ℚ_[2]) * bP
  /-- `v₂ a_P(0) = j_rc + v₂L` -/
  haP : v2 (central aP) = ((j + vL : ℤ) : WithTop ℤ)
  /-- `v₂ b_P(0) = j_rc + v₂L` -/
  hbP : v2 (central bP) = ((j + vL : ℤ) : WithTop ℤ)
  /-- the genuine orders are those of the actual torsion and `Ш` -/
  arith : DiskArith G tA shaA

namespace KummerCoordinateBlockR

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {n : ℕ}
  {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
  {j vL m : ℤ} {tA shaA : ℕ}

/-- **The constructed Knudsen–Mumford identification of the block** (replacing Lit's free
`I`). Kind: definition. -/
def I (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) :
    KummerModelIdentification (centralKMModelSel R.G R.hfinite) :=
  centralKMIdentModel R.G R.hfinite R.aK R.bK

/-- The central value of the degree-one disk: the constructed integral determinant. -/
def x₁ (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) : ℤ_[2] :=
  (centralDiskMatrix R.G R.hfinite 1).det

/-- The central value of the degree-two disk: the constructed integral determinant. -/
def x₂ (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) : ℤ_[2] :=
  (centralDiskMatrix R.G R.hfinite 2).det

/-- The central value of the degree-three disk: the constructed integral determinant. -/
def x₃ (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) : ℤ_[2] :=
  (centralDiskMatrix R.G R.hfinite 3).det

/-- The degree-one disk value is nonzero. Kind: PROVED. -/
theorem x₁_ne_zero (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) : R.x₁ ≠ 0 :=
  centralDiskMatrix_det_ne_zero _ _ 1

/-- The degree-two disk value is nonzero. Kind: PROVED. -/
theorem x₂_ne_zero (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) : R.x₂ ≠ 0 :=
  centralDiskMatrix_det_ne_zero _ _ 2

/-- The degree-three disk value is nonzero. Kind: PROVED. -/
theorem x₃_ne_zero (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) : R.x₃ ≠ 0 :=
  centralDiskMatrix_det_ne_zero _ _ 3

/-- `hx₁` of Lit, PROVED: the degree-one disk is integral at the centre with value `x₁`. -/
theorem hx₁ (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) :
    central (R.I.δ₁ : PowerSeries ℚ_[2]) = (R.x₁ : ℚ_[2]) :=
  central_centralKMDisk _ _ 1

/-- `hx₂` of Lit, PROVED. -/
theorem hx₂ (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) :
    central (R.I.δ₂ : PowerSeries ℚ_[2]) = (R.x₂ : ℚ_[2]) :=
  central_centralKMDisk _ _ 2

/-- `hx₃` of Lit, PROVED. -/
theorem hx₃ (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) :
    central (R.I.δ₃ : PowerSeries ℚ_[2]) = (R.x₃ : ℚ_[2]) :=
  central_centralKMDisk _ _ 3

/-- `hu₀` of Lit, PROVED: the core coordinate of the normalized core is `1`. -/
theorem hu₀ (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) :
    v2 (central R.I.u₀) = 0 := by
  change v2 (central (1 : PowerSeries ℚ_[2])) = 0
  simp [central, v2]

/-- **The order tie of the constructed disks, from the eight book statements** (tex 3429–3431,
4005–4018). Kind: PROVED. -/
theorem tie (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA)
    (B : CalibrationBookProps) : DiskTie R.G R.x₁ R.x₂ R.x₃ := by
  classical
  have := R.finite2
  exact diskTie_of_literature R.G R.hfinite B R.hK R.h2 R.rank_one

/-- **The constructed disk valuations are the genuine lengths**: `v₂ x₁ = v₂ x₃ = v₂ tA`,
`v₂ x₂ = v₂ shaA` (tex 4005–4018, 4057–4058). Kind: PROVED. -/
theorem disk_valuations (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA)
    (B : CalibrationBookProps) :
    R.x₁.valuation = padicValNat 2 tA ∧ R.x₂.valuation = padicValNat 2 shaA ∧
      R.x₃.valuation = padicValNat 2 tA :=
  (R.tie B).valuations R.arith (centralDiskMatrix_det_ne_zero _ _ 1)
    (centralDiskMatrix_det_ne_zero _ _ 2) (centralDiskMatrix_det_ne_zero _ _ 3)

/-- `v₂ a(0) = j + v₂L + v₂ m`. Kind: PROVED. -/
theorem v2_aK (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) (hm : m ≠ 0) :
    v2 (central (R.aK : PowerSeries ℚ_[2])) =
      ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  rw [R.ha]
  exact v2_central_C_mul hm R.haP

/-- `v₂ b(0) = j + v₂L + v₂ m`. Kind: PROVED. -/
theorem v2_bK (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA) (hm : m ≠ 0) :
    v2 (central (R.bK : PowerSeries ℚ_[2])) =
      ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  rw [R.hb]
  exact v2_central_C_mul hm R.hbP

/-- **The field `hK` of the calibration leaf, in its exact form** (tex 4057–4064), from the
R-block: the eight book statements `B`, `m ≠ 0`, `z_K ⊗ w_K = u_K adj D_K` and `adj D_K ≠ 0`.
Kind: PROVED. -/
theorem leafHK (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA)
    (B : CalibrationBookProps) (hm : m ≠ 0) {uK : PowerSeries ℚ_[2]}
    (hKc : Central.IsClassFunctionalCoord DK zK wK uK) (hadj : DK.adjugate ≠ 0) :
    v2 (central uK) =
      (((j + vL + ((padicValInt 2 m : ℕ) : ℤ)) + (j + vL + ((padicValInt 2 m : ℕ) : ℤ)) +
        (Central.diskContribution 1 ((padicValNat 2 tA : ℕ) : ℤ) +
          Central.diskContribution 2 ((padicValNat 2 shaA : ℕ) : ℤ) +
          Central.diskContribution 3 ((padicValNat 2 tA : ℕ) : ℤ)) : ℤ) : WithTop ℤ) := by
  obtain ⟨ε, uK', hKc', hc⟩ := R.link
  rw [Central.isClassFunctionalCoord_unique hadj hKc hKc', hc, v2_mul, v2_coe_unit, zero_add]
  obtain ⟨d1, d2, d3⟩ := R.disk_valuations B
  have h₁ : v2 (central (R.I.δ₁ : PowerSeries ℚ_[2])) = (((padicValNat 2 tA : ℕ) : ℤ) :
      WithTop ℤ) := by
    rw [R.hx₁, ZInQ.Contrib.RC53Assist.Calibration.v2_coe_padicInt _ R.x₁_ne_zero]
    exact congrArg (fun k : ℕ => ((k : ℤ) : WithTop ℤ)) d1
  have h₂ : v2 (central (R.I.δ₂ : PowerSeries ℚ_[2])) = (((padicValNat 2 shaA : ℕ) : ℤ) :
      WithTop ℤ) := by
    rw [R.hx₂, ZInQ.Contrib.RC53Assist.Calibration.v2_coe_padicInt _ R.x₂_ne_zero]
    exact congrArg (fun k : ℕ => ((k : ℤ) : WithTop ℤ)) d2
  have h₃ : v2 (central (R.I.δ₃ : PowerSeries ℚ_[2])) = (((padicValNat 2 tA : ℕ) : ℤ) :
      WithTop ℤ) := by
    rw [R.hx₃, ZInQ.Contrib.RC53Assist.Calibration.v2_coe_padicInt _ R.x₃_ne_zero]
    exact congrArg (fun k : ℕ => ((k : ℤ) : WithTop ℤ)) d3
  exact hK_of_identification R.I j vL ((padicValInt 2 m : ℕ) : ℤ) ((padicValNat 2 tA : ℕ) : ℤ)
    ((padicValNat 2 shaA : ℕ) : ℤ) R.hu₀ (R.v2_aK hm) (R.v2_bK hm) h₁ h₂ h₃

/-! #### The link from the central fibre of the leaf's two-term model -/

/-- **The link from a central comparison without dimension jump** (Version 19's determinant
specialization in the two-term case, `central_eq_of_noJump`; V19-only, not in the 11/5
manuscript): if the leaf's two-term model has `adj D_K(0) ≠ 0` (its central fibre has the generic
dimensions) and its central fibre computes `ε` times the central value of the constructed
coordinate, then `link` holds. Kind: PROVED. -/
theorem link_of_noJump (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (aK bK : (PowerSeries ℚ_[2])ˣ) {uK : PowerSeries ℚ_[2]}
    (hKc : Central.IsClassFunctionalCoord DK zK wK uK)
    (hjump : (DK.map central).adjugate ≠ 0) (ε : ℤ_[2]ˣ)
    (hcomp : Central.IsClassFunctionalCoord (DK.map central) (fun i => central (zK i))
      (fun i => central (wK i))
      (((ε : ℤ_[2]) : ℚ_[2]) * central (centralKMCoord G hfinite aK bK))) :
    ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2], Central.IsClassFunctionalCoord DK zK wK uK ∧
      central uK = ((ε : ℤ_[2]) : ℚ_[2]) * central (centralKMCoord G hfinite aK bK) :=
  ⟨ε, uK, hKc, central_eq_of_noJump hKc hjump hcomp⟩

/-! #### The literature block gives an R-block -/

/-- The class coefficient of a literature block is a unit (its central value has the finite
valuation `j + v₂L + v₂ m`). Kind: PROVED. -/
theorem lit_isUnit_a (L : KummerCoordinateBlockLit K E₀ hZ DK zK wK j vL m tA shaA)
    (hm : m ≠ 0) : IsUnit L.I.a := by
  apply isUnit_of_central_ne_zero
  rw [L.ha]
  exact central_ne_zero_of_v2 (v2_central_C_mul hm L.haP)

/-- The functional coefficient of a literature block is a unit. Kind: PROVED. -/
theorem lit_isUnit_b (L : KummerCoordinateBlockLit K E₀ hZ DK zK wK j vL m tA shaA)
    (hm : m ≠ 0) : IsUnit L.I.b := by
  apply isUnit_of_central_ne_zero
  rw [L.hb]
  exact central_ne_zero_of_v2 (v2_central_C_mul hm L.hbP)

/-- **The central link of a literature block**: the leaf's Kummer coordinate (Lit's exact
`link`) has central value a `2`-adic unit times the constructed coordinate with the same class
and functional coefficients; the unit is `u₀(0)` times the ratios of Lit's disks to the
constructed integral disks (units by `hu₀` and `hval_j`). Kind: PROVED. -/
theorem lit_link (L : KummerCoordinateBlockLit K E₀ hZ DK zK wK j vL m tA shaA) (hm : m ≠ 0) :
    ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2], Central.IsClassFunctionalCoord DK zK wK uK ∧
      central uK = ((ε : ℤ_[2]) : ℚ_[2]) *
        central (centralKMCoord L.G L.hfinite (lit_isUnit_a L hm).unit
          (lit_isUnit_b L hm).unit) := by
  obtain ⟨μ, hμ⟩ := exists_unit_of_v2_eq_zero L.hu₀
  obtain ⟨η₁, h₁⟩ := exists_unit_of_valuation_eq
    (ZInQ.Contrib.RC53Assist.Calibration.CentralDiskOrders.x_ne_zero L.hx₁)
    (centralDiskMatrix_det_ne_zero L.G L.hfinite 1) L.hval₁
  obtain ⟨η₂, h₂⟩ := exists_unit_of_valuation_eq
    (ZInQ.Contrib.RC53Assist.Calibration.CentralDiskOrders.x_ne_zero L.hx₂)
    (centralDiskMatrix_det_ne_zero L.G L.hfinite 2) L.hval₂
  obtain ⟨η₃, h₃⟩ := exists_unit_of_valuation_eq
    (ZInQ.Contrib.RC53Assist.Calibration.CentralDiskOrders.x_ne_zero L.hx₃)
    (centralDiskMatrix_det_ne_zero L.G L.hfinite 3) L.hval₃
  refine ⟨μ * η₁ * η₂⁻¹ * η₃, L.I.coord, L.link, ?_⟩
  have hd₂ : ((centralDiskMatrix L.G L.hfinite 2).det : ℚ_[2]) ≠ 0 :=
    PadicInt.coe_ne_zero.2 (centralDiskMatrix_det_ne_zero L.G L.hfinite 2)
  have hη₂ : ((η₂ : ℤ_[2]) : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.2 η₂.ne_zero
  rw [central_centralKMCoord, L.I.coord_eq]
  simp only [central_mul, central_units_inv, L.hx₁, L.hx₂, L.hx₃, IsUnit.unit_spec]
  rw [← hμ, h₁, h₂, h₃]
  simp only [Units.val_mul, PadicInt.coe_mul, coe_unit_inv]
  field_simp

/-- **Every literature block gives an R-block** with the same genuine data, literature inputs,
class and functional coefficients, point coefficients and arithmetic orders; its link is
`lit_link`. So the R-block asks for no more than the literature block. Kind: definition
(PROVED fields). -/
def ofLit (L : KummerCoordinateBlockLit K E₀ hZ DK zK wK j vL m tA shaA) (hm : m ≠ 0) :
    KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA where
  G := L.G
  hfinite := L.hfinite
  h2 := L.h2
  hK := L.hK
  finite2 := L.finite2
  rank_one := L.rank_one
  aK := (lit_isUnit_a L hm).unit
  bK := (lit_isUnit_b L hm).unit
  link := lit_link L hm
  aP := L.aP
  bP := L.bP
  ha := by rw [IsUnit.unit_spec]; exact L.ha
  hb := by rw [IsUnit.unit_spec]; exact L.hb
  haP := L.haP
  hbP := L.hbP
  arith := L.arith

/-! #### The literature block from an R-block and a `ℚ₂[[t]]` Galois realization -/

/-- **The literature block from an R-block and a `ℚ₂[[t]]` Galois realization of the
constructed identification**: a finite set `S`, a topological `ℚ₂[[t]][G_{K,S}]`-module `M`,
injective local conditions `Δ`, an identification `J` of their Selmer complex with the same class
and functional coefficients (`J.a = aK`, `J.b = bK`), a unit core coordinate at the centre, the
central disks of `J` equal to the constructed integral disk determinants, and Lit's exact `link`
for `J`. These are exactly the fields of `KummerCoordinateBlockLit` that have no counterpart in the
text (a DEPARTURE of form, see the module documentation); every other field, including the
disk-length identifications `hval_j` (here `rfl`), comes from the R-block. Kind: definition. -/
def toLitOfRealization (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hSfin : S.Finite) (M : Type) [AddCommGroup M]
    [Module (PowerSeries ℚ_[2]) M] [DistribMulAction (GKS K S) M]
    [SMulCommClass (GKS K S) (PowerSeries ℚ_[2]) M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul (PowerSeries ℚ_[2]) M] [ContinuousSMul (GKS K S) M]
    (Δ : GaloisLocalConditions K S (PowerSeries ℚ_[2]) M)
    (hinj : ∀ v (k : ℤ), Function.Injective ((Δ.i v).f k k rfl))
    (J : GenuineKummerModelIdentification K S (PowerSeries ℚ_[2]) M Δ)
    (hJlink : Central.IsClassFunctionalCoord DK zK wK J.coord)
    (hJa : J.a = R.aK) (hJb : J.b = R.bK) (hJu : v2 (central J.u₀) = 0)
    (hJ₁ : central (J.δ₁ : PowerSeries ℚ_[2]) = (R.x₁ : ℚ_[2]))
    (hJ₂ : central (J.δ₂ : PowerSeries ℚ_[2]) = (R.x₂ : ℚ_[2]))
    (hJ₃ : central (J.δ₃ : PowerSeries ℚ_[2]) = (R.x₃ : ℚ_[2])) :
    KummerCoordinateBlockLit K E₀ hZ DK zK wK j vL m tA shaA where
  S := S
  hSfin := hSfin
  M := M
  Δ := Δ
  hinj := hinj
  I := J
  link := hJlink
  aP := R.aP
  bP := R.bP
  ha := hJa.trans R.ha
  hb := hJb.trans R.hb
  haP := R.haP
  hbP := R.hbP
  hu₀ := hJu
  G := R.G
  x₁ := R.x₁
  x₂ := R.x₂
  x₃ := R.x₃
  hx₁ := hJ₁
  hx₂ := hJ₂
  hx₃ := hJ₃
  arith := R.arith
  hfinite := R.hfinite
  h2 := R.h2
  hK := R.hK
  finite2 := R.finite2
  rank_one := R.rank_one
  hval₁ := rfl
  hval₂ := rfl
  hval₃ := rfl

/-! #### The block pinned by a central class and functional -/

/-- **The R-block with the class and functional coefficients pinned by a central cycle `z₀` and a
closed functional `λ₀` of the retained integral model** (lane RC34 supplies `Z`: the Kummer class
of `L m P` and its paired functional; tex 3895–3909): `aK = C(a₀)`, `bK = C(b₀)` with `a₀`, `b₀`
the free-line coefficients of `z₀`, `λ₀` in the retained integral basis, and the link stated for
the pinned identification `centralKMIdentModelOf`. Kind: definition. -/
def ofCentralClassFunctional (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G))
    (Z : CentralClassFunctional G hfinite H)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    (hK : IsTotallyComplex K)
    (finite2 : ∀ [DecidableEq K],
      Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (link : ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2], Central.IsClassFunctionalCoord DK zK wK uK ∧
      central uK = ((ε : ℤ_[2]) : ℚ_[2]) * central (centralKMIdentModelOf G hfinite H Z).coord)
    (aP bP : PowerSeries ℚ_[2])
    (ha : PowerSeries.C ((retainedA0 G hfinite H Z.z0 : ℤ_[2]) : ℚ_[2]) =
      PowerSeries.C (m : ℚ_[2]) * aP)
    (hb : PowerSeries.C ((retainedB0 G hfinite H Z.lam0 : ℤ_[2]) : ℚ_[2]) =
      PowerSeries.C (m : ℚ_[2]) * bP)
    (haP : v2 (central aP) = ((j + vL : ℤ) : WithTop ℤ))
    (hbP : v2 (central bP) = ((j + vL : ℤ) : WithTop ℤ))
    (arith : DiskArith G tA shaA) : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA where
  G := G
  hfinite := hfinite
  h2 := h2
  hK := hK
  finite2 := finite2
  rank_one := rank_one
  aK := Z.aUnit
  bK := Z.bUnit
  link := link
  aP := aP
  bP := bP
  ha := ha
  hb := hb
  haP := haP
  hbP := hbP
  arith := arith

/-- The identification of the pinned block is the pinned identification. Kind: PROVED. -/
theorem ofCentralClassFunctional_I (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G))
    (Z : CentralClassFunctional G hfinite H) (h2) (hK) (finite2) (rank_one) (link) (aP bP) (ha)
    (hb) (haP) (hbP) (arith) :
    (ofCentralClassFunctional (DK := DK) (zK := zK) (wK := wK) (j := j) (vL := vL) (m := m)
      (tA := tA) (shaA := shaA) G hfinite H Z h2 hK finite2 rank_one link aP bP ha hb haP hbP
        arith).I = centralKMIdentModelOf G hfinite H Z := rfl

/-! #### Non-vacuity -/

/-- `v₂ (2^k) = k` in `ℚ₂`. Kind: PROVED. -/
theorem v2_two_zpow (k : ℤ) : v2 ((2 : ℚ_[2]) ^ k) = (k : WithTop ℤ) := by
  have h2 : (2 : ℚ_[2]) ^ k ≠ 0 := zpow_ne_zero _ two_ne_zero
  rw [v2, Padic.addValuation.apply h2, Padic.valuation_zpow]
  have : (2 : ℚ_[2]).valuation = 1 := by
    have := Padic.valuation_p (p := 2)
    exact_mod_cast this
  rw [this, mul_one]

/-- **Non-vacuity of the R-block**: for every genuine address datum `G` with the literature
inputs and the arithmetic orders, and all `j`, `vL`, `m ≠ 0`, the leaf model `D_K = (0)`,
`z_K = (u_K)`, `w_K = (1)` (with `u_K` the constructed coordinate) carries an R-block, with the
point coefficients `a_P = b_P = 2^{j + vL}` and `ε = 1`. Kind: PROVED. -/
theorem nonempty_of_inputs (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    (hK : IsTotallyComplex K)
    (finite2 : ∀ [DecidableEq K],
      Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (arith : DiskArith G tA shaA) (j vL m : ℤ) (hm : m ≠ 0) :
    ∃ zK : Fin 1 → PowerSeries ℚ_[2], Nonempty (KummerCoordinateBlockR K E₀ hZ
      (0 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2])) zK 1 j vL m tA shaA) := by
  set aP : PowerSeries ℚ_[2] := PowerSeries.C ((2 : ℚ_[2]) ^ (j + vL)) with haPdef
  have haP : v2 (central aP) = ((j + vL : ℤ) : WithTop ℤ) := by
    rw [haPdef]
    simp only [central, PowerSeries.coeff_zero_C]
    exact v2_two_zpow _
  have hu : IsUnit (PowerSeries.C (m : ℚ_[2]) * aP) :=
    isUnit_of_central_ne_zero (central_ne_zero_of_v2 (v2_central_C_mul hm haP))
  refine ⟨fun _ => centralKMCoord G hfinite hu.unit hu.unit, ⟨{
    G := G
    hfinite := hfinite
    h2 := h2
    hK := hK
    finite2 := finite2
    rank_one := rank_one
    aK := hu.unit
    bK := hu.unit
    link := ⟨1, centralKMCoord G hfinite hu.unit hu.unit, ?_, by simp⟩
    aP := aP
    bP := aP
    ha := hu.unit_spec
    hb := hu.unit_spec
    haP := haP
    hbP := haP
    arith := arith }⟩⟩
  unfold Central.IsClassFunctionalCoord
  ext i k
  fin_cases i; fin_cases k
  simp [vecMulVec_apply, adjugate_fin_one]

end KummerCoordinateBlockR

end Block

end ZInQ.Manuscript.RC.Wiring.KmIdent
