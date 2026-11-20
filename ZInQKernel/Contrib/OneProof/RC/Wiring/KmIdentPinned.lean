import ZInQKernel.Contrib.OneProof.RC.Wiring.KmIdentGenuine
import ZInQKernel.Contrib.OneProof.RC.Wiring.KmIdentLeaf

/-!
# Theorem 5.3, Lane RC35: the Kummer block with no free class, functional or core coefficient

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141), Lemma
`ex:arith-central-specialization` (tex 3895–3910).

`KummerCoordinateBlockZ` is the Kummer block whose identification is the genuine pinned
identification `centralKMIdentOf G hfinite H Z` of `KmIdentGenuine`: its class and functional
coefficients are the free-line coefficients `a₀`, `b₀` of a central cycle `z₀` and a closed
functional `λ₀` of the retained integral model of `C_K` (the data `Z : CentralClassFunctional`),
its core coefficient is `u₀ = 1`, and the only point inputs are the two valuations
`v₂ a₀ = v₂ b₀ = j + v₂L + v₂m` (tex 3905–3907, 4061–4062). There are no free `a`, `b`, `u₀`,
`a_P`, `b_P`: `a_P = C(a₀/m)` and `b_P = C(b₀/m)` are derived.

The fields `Z`, `hva0`, `hvb0` have exactly the types of the point half of the calibration
supplied by lane RC34 (its central class and functional from the genuine Kummer class of `L m P`
and the duality homotopy equivalence, with the two valuation theorems), so the combined leaf takes
that point half directly.

* `KummerCoordinateBlockZ.toR`: the R-block (`a_K = C(a₀)`, `b_K = C(b₀)`, `a_P = C(a₀/m)`,
  `b_P = C(b₀/m)`).
* `KummerCoordinateBlockZ.leafHK`: the leaf's `hK`.
* `CentralClassFunctional.scaled`, `KummerCoordinateBlockZ.nonempty_of_inputs`: non-vacuity.
* `CalibrationModelZ`, `CalibrationModelZ.toR`, `CalibrationModelZ.toModelH`,
  `CalibrationInputsZ`, `CalibrationInputsZ.toR`, `CalibrationInputsZ.toH`,
  `calibrationTarget_of_Z`, `calibrationInputsZ_of_noAddress`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring.KmIdent

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.Calibration
open WeierstrassCurve WeierstrassCurve.Affine Matrix CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData DiskTie DiskArith)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve compactCentralComplex)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape centralDiskMatrix
  retainedCentralComplex retainedCentralCoordinates)
open ZInQ.Manuscript.RC.Wiring (calibrationShape_of_literature)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps

attribute [local instance] Nat.fact_prime_two

/-! ### Valuations -/

section Valuation

/-- `v₂ (x⁻¹) = −v₂ x` for `x ∈ ℚ₂` of finite valuation. Kind: PROVED. -/
theorem v2_inv_of_v2 {x : ℚ_[2]} {k : ℤ} (h : v2 x = (k : WithTop ℤ)) :
    v2 x⁻¹ = ((-k : ℤ) : WithTop ℤ) := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp [v2] at h
  have e := v2_mul x⁻¹ x
  rw [inv_mul_cancel₀ hx, h] at e
  have h1 : v2 (1 : ℚ_[2]) = 0 := by simp [v2]
  rw [h1] at e
  have hne : v2 x⁻¹ ≠ ⊤ := by
    intro htop
    rw [htop, WithTop.top_add] at e
    exact WithTop.top_ne_coe e.symm
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hn] at e ⊢
  have h' : n + k = 0 := by exact_mod_cast e.symm
  congr 1
  omega

/-- **`v₂ (a₀ / m) = j + v₂L`** from `v₂ a₀ = j + v₂L + v₂ m`. Kind: PROVED. -/
theorem v2_div_intCast {x : ℚ_[2]} {j vL m : ℤ} (hm : m ≠ 0)
    (h : v2 x = ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ)) :
    v2 (x / (m : ℚ_[2])) = ((j + vL : ℤ) : WithTop ℤ) := by
  rw [div_eq_mul_inv, v2_mul, h, v2_inv_of_v2 (v2_intCast hm), ← WithTop.coe_add]
  congr 1
  ring

/-- `C(a₀) = C(m) · C(a₀/m)` for `m ≠ 0`. Kind: PROVED. -/
theorem C_eq_C_mul_C_div {x : ℚ_[2]} {m : ℤ} (hm : m ≠ 0) :
    PowerSeries.C x = PowerSeries.C (m : ℚ_[2]) * PowerSeries.C (x / (m : ℚ_[2])) := by
  have hm' : (m : ℚ_[2]) ≠ 0 := by exact_mod_cast hm
  rw [← map_mul, mul_div_cancel₀ _ hm']

end Valuation

/-! ### The block -/

section Block

/-- **The Kummer block with the genuine pinned identification** (tex 3877–3910, 4005–4018,
4050–4064): the address's genuine Kummer data `G` with the literature inputs, the cohomology shape
`H`, a central cycle and closed functional `Z` of the retained integral model of `C_K` (the
class of `L m P` and its paired functional), the central Kummer comparison `link` (GLUE, as in
`KummerCoordinateBlockR`), the two valuations of the free-line coefficients (ELLIOT; lane RC34's
theorems), and the arithmetic orders. Kind: definition (inputs). -/
structure KummerCoordinateBlockZ (K : Type) [Field K] [NumberField K] (E₀ : WeierstrassCurve ℚ)
    (hZ : ℤ) {n : ℕ} (DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2]))
    (zK wK : Fin n → PowerSeries ℚ_[2]) (j vL m : ℤ) (tA shaA : ℕ) : Type 1 where
  /-- the genuine data of the address -/
  G : GenuineKummerData K E₀ hZ
  /-- finite generation of the integral compact central cohomology -/
  hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n)
  /-- the cohomology shape of `C_K` -/
  H : CalibrationCohomologyShape (compactCentralComplex G)
  /-- the central cycle and closed functional -/
  Z : CentralClassFunctional G hfinite H
  /-- the support contains the places above `2` -/
  h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S
  /-- `K` has no real places -/
  hK : IsTotallyComplex K
  /-- the `2`-primary torsion of the central twist over `K` is finite -/
  finite2 : ∀ [DecidableEq K],
    Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)
  /-- the integral central first cohomology has rank one -/
  rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1
  /-- **the central Kummer comparison** (GLUE) -/
  link : ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2], Central.IsClassFunctionalCoord DK zK wK uK ∧
    central uK = ((ε : ℤ_[2]) : ℚ_[2]) * central (centralKMIdentOf G hfinite H Z).coord
  /-- `v₂ a₀ = j_rc + v₂L + v₂m` -/
  hva0 : v2 ((retainedA0 G hfinite H Z.z0 : ℤ_[2]) : ℚ_[2]) =
    ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ)
  /-- `v₂ b₀ = j_rc + v₂L + v₂m` -/
  hvb0 : v2 ((retainedB0 G hfinite H Z.lam0 : ℤ_[2]) : ℚ_[2]) =
    ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ)
  /-- the genuine orders are those of the actual torsion and `Ш` -/
  arith : DiskArith G tA shaA

namespace KummerCoordinateBlockZ

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {n : ℕ}
  {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
  {j vL m : ℤ} {tA shaA : ℕ}

/-- **The identification of the block: the genuine pinned identification.** -/
def I (R : KummerCoordinateBlockZ K E₀ hZ DK zK wK j vL m tA shaA) :
    KummerModelIdentification (centralKMSel R.G R.hfinite) :=
  centralKMIdentOf R.G R.hfinite R.H R.Z

/-- The class coefficient. -/
abbrev a0 (R : KummerCoordinateBlockZ K E₀ hZ DK zK wK j vL m tA shaA) : ℚ_[2] :=
  ((retainedA0 R.G R.hfinite R.H R.Z.z0 : ℤ_[2]) : ℚ_[2])

/-- The functional coefficient. -/
abbrev b0 (R : KummerCoordinateBlockZ K E₀ hZ DK zK wK j vL m tA shaA) : ℚ_[2] :=
  ((retainedB0 R.G R.hfinite R.H R.Z.lam0 : ℤ_[2]) : ℚ_[2])

/-- **The R-block of a Z-block**: `a_K = C(a₀)`, `b_K = C(b₀)`, `a_P = C(a₀/m)`,
`b_P = C(b₀/m)`, the link unchanged. Kind: definition (PROVED fields). -/
def toR (R : KummerCoordinateBlockZ K E₀ hZ DK zK wK j vL m tA shaA) (hm : m ≠ 0) :
    KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA where
  G := R.G
  hfinite := R.hfinite
  h2 := R.h2
  hK := R.hK
  finite2 := R.finite2
  rank_one := R.rank_one
  aK := R.Z.aUnit
  bK := R.Z.bUnit
  link := R.link
  aP := PowerSeries.C (R.a0 / (m : ℚ_[2]))
  bP := PowerSeries.C (R.b0 / (m : ℚ_[2]))
  ha := C_eq_C_mul_C_div hm
  hb := C_eq_C_mul_C_div hm
  haP := by
    simp only [central, PowerSeries.coeff_zero_C]
    exact v2_div_intCast hm R.hva0
  hbP := by
    simp only [central, PowerSeries.coeff_zero_C]
    exact v2_div_intCast hm R.hvb0
  arith := R.arith

/-- The R-block's class coefficient is `C(a₀)`. Kind: PROVED. -/
theorem toR_aK (R : KummerCoordinateBlockZ K E₀ hZ DK zK wK j vL m tA shaA) (hm : m ≠ 0) :
    ((R.toR hm).aK : PowerSeries ℚ_[2]) = PowerSeries.C R.a0 := rfl

/-- **The field `hK` of the calibration leaf from a Z-block.** Kind: PROVED. -/
theorem leafHK (R : KummerCoordinateBlockZ K E₀ hZ DK zK wK j vL m tA shaA)
    (B : CalibrationBookProps) (hm : m ≠ 0) {uK : PowerSeries ℚ_[2]}
    (hKc : Central.IsClassFunctionalCoord DK zK wK uK) (hadj : DK.adjugate ≠ 0) :
    v2 (central uK) =
      (((j + vL + ((padicValInt 2 m : ℕ) : ℤ)) + (j + vL + ((padicValInt 2 m : ℕ) : ℤ)) +
        (Central.diskContribution 1 ((padicValNat 2 tA : ℕ) : ℤ) +
          Central.diskContribution 2 ((padicValNat 2 shaA : ℕ) : ℤ) +
          Central.diskContribution 3 ((padicValNat 2 tA : ℕ) : ℤ)) : ℤ) : WithTop ℤ) :=
  (R.toR hm).leafHK B hm hKc hadj

end KummerCoordinateBlockZ

namespace KummerCoordinateBlockR

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {n : ℕ}
  {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
  {j vL m : ℤ} {tA shaA : ℕ}

/-- **The cohomology shape of `C_K` from the nine book statements** (for an R-block).
Kind: PROVED. -/
theorem shape (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA)
    (B : CalibrationBookProps) : CalibrationCohomologyShape (compactCentralComplex R.G) := by
  classical
  have := R.finite2
  exact calibrationShape_of_literature R.G R.hfinite B R.hK R.h2 R.rank_one

/-- **The genuine identification of an R-block**: its class and functional coefficients, with
the genuine target (the base-changed retained integral model of `C_K`). Kind: definition. -/
def genuineI (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA)
    (B : CalibrationBookProps) : KummerModelIdentification (centralKMSel R.G R.hfinite) :=
  centralKMIdent R.G R.hfinite (R.shape B) R.aK R.bK

/-- The genuine identification has the coordinate of the block. Kind: PROVED. -/
theorem genuineI_coord (R : KummerCoordinateBlockR K E₀ hZ DK zK wK j vL m tA shaA)
    (B : CalibrationBookProps) : (R.genuineI B).coord = R.I.coord := rfl

end KummerCoordinateBlockR

/-! ### Non-vacuity -/

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The class coefficient is linear. Kind: PROVED. -/
theorem retainedA0_smul (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (c : ℤ_[2])
    (z : (retainedCentralComplex G hfinite).X 1) :
    retainedA0 G hfinite H (c • z) = c * retainedA0 G hfinite H z := by
  unfold retainedA0
  rw [map_smul]
  rfl

/-- The functional coefficient is linear. Kind: PROVED. -/
theorem retainedB0_smul (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (c : ℤ_[2])
    (lam : (retainedCentralComplex G hfinite).X 2 →ₗ[ℤ_[2]] ℤ_[2]) :
    retainedB0 G hfinite H (c • lam) = c * retainedB0 G hfinite H lam := rfl

/-- **Scaled standard central class and functional**: `z₀ = c e₁`, `λ₀ = c' e₂*` (a cycle and a
closed functional with coefficients `c`, `c'`). Kind: definition (PROVED fields). -/
def CentralClassFunctional.scaled (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (c c' : ℤ_[2]) (hc : c ≠ 0)
    (hc' : c' ≠ 0) : CentralClassFunctional G hfinite H where
  z0 := c • retainedE1 G hfinite H
  hz0 := by rw [map_smul, retainedE1_cycle, smul_zero]
  lam0 := c' • retainedFree2 G hfinite H
  hlam0 := by rw [LinearMap.smul_comp, retainedFree2_closed, smul_zero]
  ha0 := by
    rw [retainedA0_smul, retainedA0_E1, mul_one]
    exact hc
  hb0 := by
    rw [retainedB0_smul, retainedB0_free2, mul_one]
    exact hc'

/-- The class coefficient of the scaled class is `c`. Kind: PROVED. -/
theorem CentralClassFunctional.scaled_a0 (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (c c' : ℤ_[2]) (hc : c ≠ 0)
    (hc' : c' ≠ 0) :
    retainedA0 G hfinite H (CentralClassFunctional.scaled G hfinite H c c' hc hc').z0 = c := by
  change retainedA0 G hfinite H (c • retainedE1 G hfinite H) = c
  rw [retainedA0_smul, retainedA0_E1, mul_one]

/-- The functional coefficient of the scaled functional is `c'`. Kind: PROVED. -/
theorem CentralClassFunctional.scaled_b0 (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G)) (c c' : ℤ_[2]) (hc : c ≠ 0)
    (hc' : c' ≠ 0) :
    retainedB0 G hfinite H (CentralClassFunctional.scaled G hfinite H c c' hc hc').lam0 = c' := by
  change retainedB0 G hfinite H (c' • retainedFree2 G hfinite H) = c'
  rw [retainedB0_smul, retainedB0_free2, mul_one]

/-- `v₂ (2^k) = k` for `k : ℕ`, in `ℤ₂ ⊆ ℚ₂`. Kind: PROVED. -/
theorem v2_two_pow_padicInt (k : ℕ) :
    v2 (((2 : ℤ_[2]) ^ k : ℤ_[2]) : ℚ_[2]) = ((k : ℤ) : WithTop ℤ) := by
  push_cast
  have := v2_two_zpow (k : ℤ)
  rwa [zpow_natCast] at this

/-- **Non-vacuity of the Z-block**: for every genuine address datum `G` with the literature
inputs, its cohomology shape and the arithmetic orders, and all `j`, `vL`, `m` with
`j + vL + v₂ m = k ≥ 0`, the leaf model `D_K = (0)`, `z_K = (u_K)`, `w_K = (1)` carries a Z-block,
with `z₀ = 2^k e₁` and `λ₀ = 2^k e₂*`. Kind: PROVED. -/
theorem KummerCoordinateBlockZ.nonempty_of_inputs {tA shaA : ℕ} (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    (hK : IsTotallyComplex K)
    (finite2 : ∀ [DecidableEq K],
      Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (arith : DiskArith G tA shaA) (j vL m : ℤ) (k : ℕ)
    (hk : j + vL + ((padicValInt 2 m : ℕ) : ℤ) = k) :
    ∃ zK : Fin 1 → PowerSeries ℚ_[2], Nonempty (KummerCoordinateBlockZ K E₀ hZ
      (0 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2])) zK 1 j vL m tA shaA) := by
  have hc : (2 : ℤ_[2]) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  let Z := CentralClassFunctional.scaled G hfinite H _ _ hc hc
  refine ⟨fun _ => (centralKMIdentOf G hfinite H Z).coord, ⟨{
    G := G
    hfinite := hfinite
    H := H
    Z := Z
    h2 := h2
    hK := hK
    finite2 := finite2
    rank_one := rank_one
    link := ⟨1, (centralKMIdentOf G hfinite H Z).coord, ?_, by simp⟩
    hva0 := ?_
    hvb0 := ?_
    arith := arith }⟩⟩
  · unfold Central.IsClassFunctionalCoord
    ext i l
    fin_cases i; fin_cases l
    simp [vecMulVec_apply, adjugate_fin_one]
  · rw [CentralClassFunctional.scaled_a0, v2_two_pow_padicInt, hk]
  · rw [CentralClassFunctional.scaled_b0, v2_two_pow_padicInt, hk]

end Block

/-! ### The leaf -/

section Leaf

/-- **The inputs of (4.6) at one address, with the genuine pinned Knudsen–Mumford
identification** (tex 3987–4141): every field of `CalibrationModelLit`, with the same names and
types, except that its Kummer block is a `KummerCoordinateBlockZ`. Kind: definition (inputs). -/
structure CalibrationModelZ {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
    (x : Addr Fam.b) : Type 1 where
  /-- `|Ш(𝒜)[2^∞]|` -/
  shaA : ℕ
  /-- `|Ш(ℬ)[2^∞]|` -/
  shaB : ℕ
  /-- `|𝒜(ℚ)_tors[2^∞]|` -/
  tA : ℕ
  /-- `|ℬ(ℚ)_tors[2^∞]|` -/
  tB : ℕ
  /-- finiteness of `Ш(𝒜)` -/
  shaA_ne : shaA ≠ 0
  /-- finiteness of `Ш(ℬ)` -/
  shaB_ne : shaB ≠ 0
  /-- `𝒜` has torsion -/
  tA_ne : tA ≠ 0
  /-- `ℬ` has torsion -/
  tB_ne : tB ≠ 0
  /-- the finite set of primes carrying the component numbers -/
  Scomp : Finset ℕ
  /-- the component numbers of `𝒜` -/
  cA : ℕ → ℕ
  /-- the component numbers of `ℬ` -/
  cB : ℕ → ℕ
  /-- the companion primes are among them -/
  hTS : D.kfin.natAbs.primeFactors ⊆ Scomp
  /-- component numbers are positive -/
  hcpos : ∀ p ∈ Scomp, 0 < cA p
  /-- cancellation away from the companion primes -/
  hcancel : ∀ p ∈ Scomp, p ∉ D.kfin.natAbs.primeFactors → cA p = cB p
  /-- the Weil restriction has connected special fiber at a companion prime -/
  hA1 : ∀ p ∈ D.kfin.natAbs.primeFactors, cA p = 1
  /-- the companion primes are odd -/
  hodd : ∀ p ∈ D.kfin.natAbs.primeFactors, p ≠ 2
  /-- the companion primes exactly divide `k` -/
  hram : ∀ p ∈ D.kfin.natAbs.primeFactors, ¬ ((p : ℤ) ^ 2 ∣ D.kfin)
  /-- `E₀ = E^{(h_x)}` has good reduction at each companion prime (a good integral model up to
  isomorphism) -/
  goodModel : ∀ p ∈ D.kfin.natAbs.primeFactors, GoodModelIso (qtwist (Ecurve ℓ) (Fam.h x : ℚ)) p
  /-- **PRINT (Edixhoven, Thm 5.3 and Rem 5.4.1) as GLUE**, model-free form -/
  hEdix : EdixhovenComponentNumberIso ℓ (Fam.h x : ℚ) D.kfin cB
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  [quadK : Algebra.IsQuadraticExtension ℚ K]
  /-- `√k ∈ K` and the nontrivial automorphism `√k ↦ −√k` -/
  quad : QuadData K (D.kfin : ℚ)
  /-- `φ^*ω_ℬ = a ω_𝒜` -/
  aPull : ℤ
  /-- `ψ^*ω_𝒜 = b ω_ℬ` -/
  bPull : ℤ
  /-- `ab = 4` -/
  hab : aPull * bPull = 4
  /-- `|coker φ_ℝ|` -/
  gam : ℕ
  /-- `|ker φ_ℝ|` -/
  kap : ℕ
  /-- both at most four -/
  hgam : 1 ≤ gam ∧ gam ≤ 4
  /-- both at most four -/
  hkap : 1 ≤ kap ∧ kap ≤ 4
  /-- the Néron period of `𝒜` -/
  OmA : ℝ
  /-- nonzero period -/
  hOmA : OmA ≠ 0
  /-- the rational period ratio `Ω_ℬ/Ω_𝒜` -/
  rhoOm : ℚ
  /-- the real change of variables -/
  hcv : (|aPull| : ℝ) * OmA = ((kap : ℝ) / gam) * ((rhoOm : ℝ) * OmA)
  /-- Cassels' isogeny invariance in Milne's form, with the canonical regulators of any free
  generators of the two rank-one lattices -/
  hmilne : ∀ (gA : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange K).toAffine.Point)
    (gB : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange ℚ).toAffine.Point ×
      ((qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).baseChange ℚ).toAffine.Point),
    IsFreeGenerator gA → IsFreeGenerator gB →
    Central.MilneIsogenyInvariance shaA shaB tA tA tB tB
      (∏ p ∈ Scomp, cA p) (∏ p ∈ Scomp, cB p) gA.canonicalHeight
      (ZInQ.Manuscript.RC.Height.heightB (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) gB) OmA
      ((rhoOm : ℝ) * OmA)
  /-- `s_ℬ = s(h_x) + s(h_x k)` -/
  hsB : ((padicValNat 2 shaB : ℕ) : ℤ) =
    (shaLength (Etw ℓ (Fam.h x)) : ℤ) + (shaLength (Etw ℓ (Fam.h x * D.kfin)) : ℤ)
  /-- the rational torsion of `ℬ` is bounded by `G₀` -/
  hgB : ((padicValNat 2 tB : ℕ) : ℤ) ≤ G₀
  /-- the moving prime `r_i` -/
  rmov : ℕ
  /-- its trace `a_{r_i}` -/
  amov : ℤ
  /-- the quadratic sign `χ_h(r_i)` -/
  chimov : ℤ
  /-- the moving exponent `B_i` -/
  Bexp : ℕ
  /-- the constant `c_E` of the Tate image -/
  cE : ℕ
  /-- `χ = ±1` -/
  hchi : chimov = 1 ∨ chimov = -1
  /-- `r_i ≡ 1 (mod 2^{B_i})` -/
  hrmov : (2 : ℤ) ^ Bexp ∣ (rmov : ℤ) - 1
  /-- `2^{c_E + 1} ∤ a_{r_i} − 2χ` (the non-divisibility of the moving-prime construction) -/
  hnd : ¬ (2 : ℤ) ^ (cE + 1) ∣ amov - 2 * chimov
  /-- `B_i ≥ c_E + 1` -/
  hcB : cE + 1 ≤ Bexp
  /-- the size of the Kummer two-term model -/
  nK : ℕ
  /-- the index set of the quotient block -/
  κ : Type
  [fκ : Fintype κ]
  [dκ : DecidableEq κ]
  /-- the Kummer differential -/
  DK : Matrix (Fin nK) (Fin nK) (PowerSeries ℚ_[2])
  /-- the off-diagonal block of the relaxation -/
  X : Matrix (Fin nK) κ (PowerSeries ℚ_[2])
  /-- the quotient block at the moving and active places -/
  DW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the Kummer class -/
  zK : Fin nK → PowerSeries ℚ_[2]
  /-- the Kummer functional -/
  wK : Fin nK → PowerSeries ℚ_[2]
  /-- the primitive class -/
  zP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the primitive functional -/
  wP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the Kummer coordinate -/
  uK : PowerSeries ℚ_[2]
  /-- the primitive class restricts to the Kummer class -/
  hz : ∀ i, zP (Sum.inl i) = zK i
  /-- the primitive functional restricts to the Kummer functional -/
  hw : ∀ i, wP (Sum.inl i) = wK i
  /-- `u_prim` is the coordinate of the primitive model -/
  hP : CommonCoordinate.IsCoordOn (fromBlocks DK X 0 DW) zP wP (D.uPrim Fam x)
  /-- `u_K` is the coordinate of the Kummer model -/
  hKc : Central.IsClassFunctionalCoord DK zK wK uK
  /-- The Kummer differential has nonzero adjugate; this is weaker than
  saying that its generic cohomology has dimensions (1,1). -/
  hadj : DK.adjugate ≠ 0
  /-- **the Kummer block with the genuine pinned identification** (`KummerCoordinateBlockZ`:
  no free class, functional or core coefficient); it replaces the field `hK`, which is derived
  (`KummerCoordinateBlockZ.leafHK`) -/
  kummer : KummerCoordinateBlockZ K (Ecurve ℓ) (Fam.h x) DK zK wK (D.jrc (Fam.h x) D.kfin) vL
    (amov - 2 * chimov) tA shaA
  /-- the Frobenius at the moving prime, over `ℚ₂[[t]]` -/
  Fr : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])
  /-- its central value has trace `a_{r_i}` -/
  hFtr : (Fr.map central).trace = (amov : ℚ_[2])
  /-- its central value has determinant `r_i` -/
  hFdet : (Fr.map central).det = (rmov : ℚ_[2])
  /-- the change of basis on the left -/
  PW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the change of basis on the right -/
  QW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the relabelling of the quotient block by the two moving places and the active places -/
  eW : κ ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin (4 * omega (Fam.h x))
  /-- the moving scalar at the first place above `r_i` -/
  zmov : PowerSeries ℚ_[2]
  /-- the moving scalar at the second place above `r_i` -/
  zmov' : PowerSeries ℚ_[2]
  /-- the block at the active places -/
  Bact : Matrix (Fin (4 * omega (Fam.h x))) (Fin (4 * omega (Fam.h x))) (PowerSeries ℚ_[2])
  /-- the quotient block is the direct sum of the local blocks, up to the changes of basis -/
  hDW : DW = PW * (fromBlocks (CommonCoordinate.twoPlaceBlock Fr (rmov : PowerSeries ℚ_[2]) zmov
    zmov') 0 0 Bact).submatrix eW eW * QW
  /-- the left change of basis has a unit determinant at the centre -/
  hPW : v2 (central PW.det) = 0
  /-- the right change of basis has a unit determinant at the centre -/
  hQW : v2 (central QW.det) = 0
  /-- the moving character is trivial at the centre: the first scalar is `χ_h(r_i)` -/
  hzmov : central zmov = chimov
  /-- the second scalar is `χ_h(r_i)` at the centre -/
  hzmov' : central zmov' = chimov
  /-- the active block is the minimal model `2 · 1` of `E[2]` at the centre -/
  hact : Bact.map central =
    (2 : ℚ_[2]) • (1 : Matrix (Fin (4 * omega (Fam.h x))) (Fin (4 * omega (Fam.h x))) ℚ_[2])

attribute [instance] CalibrationModelZ.fieldK CalibrationModelZ.nfK CalibrationModelZ.decK
  CalibrationModelZ.quadK CalibrationModelZ.fκ CalibrationModelZ.dκ

variable {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family} {x : Addr Fam.b}

/-- `m = a_r − 2χ_h(r) ≠ 0`. Kind: PROVED. -/
theorem CalibrationModelZ.m_ne_zero (M : CalibrationModelZ D vL G₀ Fam x) :
    M.amov - 2 * M.chimov ≠ 0 := by
  intro h0
  exact M.hnd (by rw [h0]; exact dvd_zero _)

/-- **The R-model of a Z-model** (the Kummer block through `KummerCoordinateBlockZ.toR`).
Kind: definition. -/
def CalibrationModelZ.toR (M : CalibrationModelZ D vL G₀ Fam x) :
    CalibrationModelR D vL G₀ Fam x :=
  { M with kummer := M.kummer.toR M.m_ne_zero }

/-- **The RC53 group's model from the Z-model and the nine book statements.**
Kind: definition. -/
def CalibrationModelZ.toModelH (M : CalibrationModelZ D vL G₀ Fam x)
    (B : CalibrationBookProps) : CalibrationModelH D vL G₀ Fam x :=
  M.toR.toModelH B

/-- **The calibration leaf with the genuine pinned identification** ((4.6), tex 3987–4141): the
nine book statements and, at every address of a final family with `ord L(E^{(h_x)}) = 1` and
`ord L(E^{(h_x k)}) = 0`, a `CalibrationModelZ`. Kind: definition. -/
def CalibrationInputsZ (D : RCData ℓ) : Prop :=
  CalibrationBookProps ∧ ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family,
    D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelZ D vL G₀ F x)

/-- `CalibrationInputsZ → CalibrationInputsR`. Kind: PROVED. -/
theorem CalibrationInputsZ.toR (h : CalibrationInputsZ D) : CalibrationInputsR D := by
  obtain ⟨B, vL, G₀, hvL, H⟩ := h
  refine ⟨B, vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact ⟨M.toR⟩

/-- `CalibrationInputsZ → CalibrationInputsH`. Kind: PROVED. -/
theorem CalibrationInputsZ.toH (h : CalibrationInputsZ D) : CalibrationInputsH D :=
  h.toR.toH

/-- **`RCSteps.calibration` from the Z-inputs** ((4.6), tex 3987–4141). Kind: PROVED. -/
theorem calibrationTarget_of_Z (Pr : Prints) (hℓ : 0 < ℓ) (h : CalibrationInputsZ D) :
    CalibrationTarget D :=
  calibrationTarget_of_R Pr hℓ h.toR

/-- **Non-vacuity in the degenerate case.** Kind: PROVED. -/
theorem calibrationInputsZ_of_noAddress (B : CalibrationBookProps)
    (hD : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      AnalyticRank (Etw ℓ (F.h x)) 1 → ¬ AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0) :
    CalibrationInputsZ D :=
  ⟨B, 0, 0, le_rfl, fun Co Ce F hF x h1 h0 => absurd h0 (hD Co Ce F hF x h1)⟩

end Leaf

end ZInQ.Manuscript.RC.Wiring.KmIdent
