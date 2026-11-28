import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointKmIdent
import ZInQKernel.Contrib.OneProof.RC.Wiring.KmIdentPinned

/-!
# Theorem 5.3, Lane RC34: the combined calibration block and leaf

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141), Lemma
`ex:arith-central-specialization` (tex 3895–3910). Lane RC35's Kummer block
`KummerCoordinateBlockZ` has no free class, functional or core coefficient: its point inputs are a
central cycle and closed functional `Z` of the retained integral model of `C_K` and the two
valuations `hva0`, `hvb0` of their free-line coefficients. This file supplies them from the point
data of the address, giving the combined block and its leaf form.

* `blockZOfPointData`: the combined block from the integral duality, the point data
  (`RetainedPointData`) and the block's non-point inputs; `Z := centralClassFunctional`,
  `hva0 := centralClassFunctional_v2_a0`, `hvb0 := centralClassFunctional_v2_b0`.
* `KummerPointInputs B …`: the block's non-point inputs, the division towers and the point data
  for the genuine Kummer map, with the duality of the book statements `B`;
  `KummerPointInputs.toBlockZ`.
* `CalibrationModelP B D vL G₀ Fam x`: lane RC35's model with the Kummer block replaced by
  `KummerPointInputs`; `CalibrationModelP.toZ`.
* `CalibrationInputsP`, `CalibrationInputsP.toZ` (to lane RC35's `CalibrationInputsZ`),
  `calibrationTarget_of_P`, `calibrationInputsP_of_noAddress`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CalPoint

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.Calibration
open WeierstrassCurve WeierstrassCurve.Affine Matrix CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData DiskArith)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve compactCentralComplex)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape)
open ZInQ.Contrib.RC53Assist.CalibrationShape (IntegralCentralKummerDuality)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.Wiring (CalibrationBookProps CalibrationTarget)
open ZInQ.Manuscript.RC.Wiring.KmIdent (KummerCoordinateBlockZ centralKMIdentOf retainedA0
  retainedB0 CentralClassFunctional CalibrationModelZ CalibrationInputsZ calibrationTarget_of_Z)

attribute [local instance] Nat.fact_prime_two

/-! ### The combined block -/

section Block

variable {K : Type} [Field K] [NumberField K] [decK : DecidableEq K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ} {n : ℕ} {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])}
  {zK wK : Fin n → PowerSeries ℚ_[2]} {j vL m : ℤ} {tA shaA : ℕ}

/-- **The combined calibration block** (tex 3895–3910, 4005–4021, 4057–4064): lane RC35's
`KummerCoordinateBlockZ` with its point inputs supplied by the point data, `Z` the central class
and functional of `L m P` and `hva0`, `hvb0` the two valuation theorems. Kind: definition
(PROVED fields). -/
def blockZOfPointData (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G))
    (hdual : IntegralCentralKummerDuality G hfinite)
    {κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1}
    (D : RetainedPointData G κ j vL) (hm : m ≠ 0)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    (hK : IsTotallyComplex K)
    (finite2 : Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (link : ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2], Central.IsClassFunctionalCoord DK zK wK uK ∧
      central uK = ((ε : ℤ_[2]) : ℚ_[2]) *
        central (centralKMIdentOf G hfinite H (centralClassFunctional hdual D hm)).coord)
    (arith : DiskArith G tA shaA) : KummerCoordinateBlockZ K E₀ hZ DK zK wK j vL m tA shaA where
  G := G
  hfinite := hfinite
  H := H
  Z := centralClassFunctional hdual D hm
  h2 := h2
  hK := hK
  finite2 := fun [i : DecidableEq K] => (Subsingleton.elim decK i) ▸ finite2
  rank_one := rank_one
  link := link
  hva0 := centralClassFunctional_v2_a0 hdual D hm
  hvb0 := centralClassFunctional_v2_b0 hdual D hm
  arith := arith

/-- The central class and functional of the combined block are those of the point data.
PROVED. -/
theorem blockZOfPointData_Z (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G))
    (hdual : IntegralCentralKummerDuality G hfinite)
    {κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1}
    (D : RetainedPointData G κ j vL) (hm : m ≠ 0) (h2) (hK) (finite2) (rank_one) (link) (arith) :
    (blockZOfPointData (DK := DK) (zK := zK) (wK := wK) (tA := tA) (shaA := shaA) G hfinite H
      hdual D hm h2 hK finite2 rank_one link arith).Z = centralClassFunctional hdual D hm := rfl

end Block

/-! ### The Kummer block's inputs with the point half -/

section PointInputs

/-- **The Kummer block's inputs at an address with the point half** (tex 3895–3910,
4005–4021, 4057–4064): the non-point fields of `KummerCoordinateBlockZ` (the genuine data, the
finiteness, the cohomology shape, `h2`, `hK`, `finite2`, `rank_one`, the central comparison
`link` and the arithmetic orders), the division towers `hdiv` of the central twist and the point
data `pt` for the genuine Kummer map (`CentralPointData`). The central class and functional are
those of `pt` with the integral duality of the book statements `B` (`bookDuality`). Kind:
definition (inputs). -/
structure KummerPointInputs (B : CalibrationBookProps) (K : Type) [Field K] [NumberField K]
    [DecidableEq K] (E₀ : WeierstrassCurve ℚ) (hZ : ℤ) {n : ℕ}
    (DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])) (zK wK : Fin n → PowerSeries ℚ_[2])
    (j vL m : ℤ) (tA shaA : ℕ) : Type 1 where
  /-- the genuine data of the address -/
  G : GenuineKummerData K E₀ hZ
  /-- finite generation of the integral compact central cohomology -/
  hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n)
  /-- the cohomology shape of `C_K` -/
  H : CalibrationCohomologyShape (compactCentralComplex G)
  /-- the support contains the places above `2` -/
  h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S
  /-- `K` has no real places -/
  hK : IsTotallyComplex K
  /-- the `2`-primary torsion of the central twist over `K` is finite -/
  finite2 : Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)
  /-- the integral central first cohomology has rank one -/
  rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1
  /-- global towers of `2`-power division points of the central twist (proved from good
  reduction outside `S` by `globalDivisionTowers_of_goodReduction`) -/
  hdiv : GlobalDivisionTowers G.S (centralCurve G)
  /-- the point data of the address for the genuine Kummer map -/
  pt : CentralPointData G hdiv j vL
  /-- `m ≠ 0` -/
  hm : m ≠ 0
  /-- **the central Kummer comparison** (GLUE, as in `KummerCoordinateBlockZ`) -/
  link : ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2], Central.IsClassFunctionalCoord DK zK wK uK ∧
    central uK = ((ε : ℤ_[2]) : ℚ_[2]) * central (centralKMIdentOf G hfinite H
      (centralClassFunctional (bookDuality G hfinite B hK h2) pt hm)).coord
  /-- the genuine orders are those of the actual torsion and `Ш` -/
  arith : DiskArith G tA shaA

variable {B : CalibrationBookProps} {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {n : ℕ} {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])}
  {zK wK : Fin n → PowerSeries ℚ_[2]} {j vL m : ℤ} {tA shaA : ℕ}

/-- **The combined Kummer block of the inputs**: `blockZOfPointData` with the duality of the
book statements. Kind: definition (PROVED fields). -/
def KummerPointInputs.toBlockZ (P : KummerPointInputs B K E₀ hZ DK zK wK j vL m tA shaA) :
    KummerCoordinateBlockZ K E₀ hZ DK zK wK j vL m tA shaA :=
  blockZOfPointData P.G P.hfinite P.H (bookDuality P.G P.hfinite B P.hK P.h2) P.pt P.hm P.h2 P.hK
    P.finite2 P.rank_one P.link P.arith


/-- **Non-vacuity of `KummerPointInputs`** (relative to the block's other inputs): for genuine
data `G` with the literature inputs, the arithmetic orders, the division towers and a free
generator `g` whose Kummer class generates `H¹(C_K)` modulo torsion, the one-term model
`D_K = (0)`, `z_K = (u_K)`, `w_K = (1)` (with `u_K` the constructed coordinate) carries the
inputs, at the point data `RetainedPointData.ofGenerator g` (`j = vL = 0`, `m = 1`). PROVED. -/
theorem KummerPointInputs.nonempty_of_inputs (B : CalibrationBookProps)
    (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (H : CalibrationCohomologyShape (compactCentralComplex G))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    (hK : IsTotallyComplex K)
    (finite2 : Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (hdiv : GlobalDivisionTowers G.S (centralCurve G)) (g : (centralCurve G).toAffine.Point)
    (hg : IsFreeGenerator g) (hκ : IsFreeLineGenerator ℤ_[2] (centralKummer G hdiv g))
    (arith : DiskArith G tA shaA) :
    ∃ zK : Fin 1 → PowerSeries ℚ_[2], Nonempty (KummerPointInputs B K E₀ hZ
      (0 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2])) zK 1 0 0 1 tA shaA) := by
  let pt : CentralPointData G hdiv 0 0 := RetainedPointData.ofGenerator g hg hκ
  let Z := centralClassFunctional (H := H) (bookDuality G hfinite B hK h2) pt one_ne_zero
  refine ⟨fun _ => (centralKMIdentOf G hfinite H Z).coord, ⟨{
    G := G
    hfinite := hfinite
    H := H
    h2 := h2
    hK := hK
    finite2 := finite2
    rank_one := rank_one
    hdiv := hdiv
    pt := pt
    hm := one_ne_zero
    link := ⟨1, (centralKMIdentOf G hfinite H Z).coord, ?_, by
      simp only [Units.val_one, PadicInt.coe_one, one_mul]; rfl⟩
    arith := arith }⟩⟩
  unfold Central.IsClassFunctionalCoord
  ext i l
  fin_cases i; fin_cases l
  simp [vecMulVec_apply, adjugate_fin_one]

end PointInputs

/-! ### The leaf with the point half derived -/

section Leaf

/-- **The inputs of (4.6) at one address with the point half derived** (tex 3987–4141): every
field of lane RC35's model with the genuine pinned identification (hence of `CalibrationModelLit`),
with the same names and types, except that its Kummer block is a `KummerPointInputs` (the Kummer
block's non-point inputs, the division towers and the point data), from which the Kummer block
`KummerCoordinateBlockZ` is built with the duality of the book statements `B`.
Kind: definition (inputs). -/
structure CalibrationModelP (B : CalibrationBookProps) {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ)
    (Fam : Family)
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
  /-- **the Kummer block's inputs with the point half** (`KummerPointInputs`): the Kummer block
  `KummerCoordinateBlockZ` is built from them (`KummerPointInputs.toBlockZ`) -/
  kummer : KummerPointInputs B K (Ecurve ℓ) (Fam.h x) DK zK wK (D.jrc (Fam.h x) D.kfin) vL
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

attribute [instance] CalibrationModelP.fieldK CalibrationModelP.nfK CalibrationModelP.decK
  CalibrationModelP.quadK CalibrationModelP.fκ CalibrationModelP.dκ

variable {B : CalibrationBookProps} {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family}
  {x : Addr Fam.b}

/-- **The Z-model of a P-model**: the Kummer block is built from its inputs
(`KummerPointInputs.toBlockZ`), every other field is unchanged. Kind: definition. -/
def CalibrationModelP.toZ (M : CalibrationModelP B D vL G₀ Fam x) :
    CalibrationModelZ D vL G₀ Fam x :=
  { M with kummer := M.kummer.toBlockZ }

/-- **The calibration leaf with the point half derived** ((4.6), tex 3987–4141): the eight book
statements and, at every address of a final family with `ord L(E^{(h_x)}) = 1` and
`ord L(E^{(h_x k)}) = 0`, a `CalibrationModelP` (lane RC35's model with the Kummer block's point
inputs replaced by the point data). Kind: definition. -/
def CalibrationInputsP (D : RCData ℓ) : Prop :=
  ∃ B : CalibrationBookProps, ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family,
    D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelP B D vL G₀ F x)

/-- **`CalibrationInputsP → CalibrationInputsZ`** (lane RC35's leaf). Kind: PROVED. -/
theorem CalibrationInputsP.toZ (h : CalibrationInputsP D) : CalibrationInputsZ D := by
  obtain ⟨B, vL, G₀, hvL, H⟩ := h
  refine ⟨B, vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact ⟨M.toZ⟩

/-- **`RCSteps.calibration` from the leaf with the point half derived** ((4.6), tex 3987–4141).
Kind: PROVED. -/
theorem calibrationTarget_of_P (Pr : Prints) (hℓ : 0 < ℓ) (h : CalibrationInputsP D) :
    CalibrationTarget D :=
  calibrationTarget_of_Z Pr hℓ h.toZ

/-- **Non-vacuity in the degenerate case.** Kind: PROVED. -/
theorem calibrationInputsP_of_noAddress (B : CalibrationBookProps)
    (hD : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      AnalyticRank (Etw ℓ (F.h x)) 1 → ¬ AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0) :
    CalibrationInputsP D :=
  ⟨B, 0, 0, le_rfl, fun Co Ce F hF x h1 h0 => absurd h0 (hD Co Ce F hF x h1)⟩

end Leaf

end ZInQ.Manuscript.RC.CalPoint
