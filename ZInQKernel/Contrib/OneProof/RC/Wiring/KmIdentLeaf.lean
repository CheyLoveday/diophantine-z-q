import ZInQKernel.Contrib.OneProof.RC.Wiring.KmIdentBlock

/-!
# Theorem 5.3, Lane RC35: the calibration leaf with the constructed Knudsen–Mumford identification

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141).

* `CalibrationModelR`: every field of the literature model `CalibrationModelLit`, with the same
  names and types, except that its Kummer block is a `KummerCoordinateBlockR` (the free
  `ℚ₂[[t]]` Selmer data, the free identification, the central disk values and the disk-length
  identifications replaced by the constructed identification of the ordinary Kummer complex; the
  coordinate transfer is the central GLUE `link`).
* `CalibrationModelR.toModelH`: the RC53 group's `CalibrationModelH` (its `hK` from
  `KummerCoordinateBlockR.leafHK`) given the nine book statements.
* `CalibrationModelR.ofLit`: every literature model gives an R-model.
* `CalibrationInputsR`, `CalibrationInputsR.toH`, `CalibrationInputsR.ofLit`,
  `calibrationTarget_of_R`, `calibrationInputsR_of_noAddress` (non-vacuity in the degenerate case;
  the Kummer block itself is non-vacuous by `KummerCoordinateBlockR.nonempty_of_inputs`).

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
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps

attribute [local instance] Nat.fact_prime_two

section Leaf

/-- **The inputs of (4.6) at one address, with the constructed Knudsen–Mumford identification**
(tex 3987–4141): every field of `CalibrationModelLit`, with the same names and types, except that
its Kummer block is a `KummerCoordinateBlockR`. Kind: definition (inputs). -/
structure CalibrationModelR {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
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
  /-- **the Kummer block with the constructed Knudsen–Mumford identification**
  (`KummerCoordinateBlockR`); it replaces the field `hK`, which is derived
  (`KummerCoordinateBlockR.leafHK`) -/
  kummer : KummerCoordinateBlockR K (Ecurve ℓ) (Fam.h x) DK zK wK (D.jrc (Fam.h x) D.kfin) vL
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

attribute [instance] CalibrationModelR.fieldK CalibrationModelR.nfK CalibrationModelR.decK
  CalibrationModelR.quadK CalibrationModelR.fκ CalibrationModelR.dκ

variable {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family} {x : Addr Fam.b}

/-- `m = a_r − 2χ_h(r) ≠ 0`. Kind: PROVED. -/
theorem CalibrationModelR.m_ne_zero (M : CalibrationModelR D vL G₀ Fam x) :
    M.amov - 2 * M.chimov ≠ 0 := by
  intro h0
  exact M.hnd (by rw [h0]; exact dvd_zero _)

/-- **The RC53 group's model from the R-model and the nine book statements**: `hK` from
`KummerCoordinateBlockR.leafHK`. Kind: definition. -/
def CalibrationModelR.toModelH (M : CalibrationModelR D vL G₀ Fam x)
    (B : CalibrationBookProps) : CalibrationModelH D vL G₀ Fam x :=
  { M with hK := M.kummer.leafHK B M.m_ne_zero M.hKc M.hadj }

/-- `m ≠ 0` for a literature model. Kind: PROVED. -/
theorem litModel_m_ne_zero (M : CalibrationModelLit D vL G₀ Fam x) :
    M.amov - 2 * M.chimov ≠ 0 := by
  intro h0
  exact M.hnd (by rw [h0]; exact dvd_zero _)

/-- **Every literature model gives an R-model** (the Kummer block through
`KummerCoordinateBlockR.ofLit`). Kind: definition. -/
def CalibrationModelR.ofLit (M : CalibrationModelLit D vL G₀ Fam x) :
    CalibrationModelR D vL G₀ Fam x :=
  { M with kummer := KummerCoordinateBlockR.ofLit M.kummer (litModel_m_ne_zero M) }

/-- **The calibration leaf with the constructed Knudsen–Mumford identification** ((4.6),
tex 3987–4141): the nine book statements and, as in `CalibrationInputsLit`, constants `vL ≥ 0`,
`G₀` before the families and at every address of a final family with `ord L(E^{(h_x)}) = 1` and
`ord L(E^{(h_x k)}) = 0` a `CalibrationModelR`. Kind: definition. -/
def CalibrationInputsR (D : RCData ℓ) : Prop :=
  CalibrationBookProps ∧ ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family,
    D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelR D vL G₀ F x)

/-- **The current leaf from the R-inputs**: `CalibrationInputsR → CalibrationInputsH`.
Kind: PROVED. -/
theorem CalibrationInputsR.toH (h : CalibrationInputsR D) : CalibrationInputsH D := by
  obtain ⟨B, vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact ⟨M.toModelH B⟩

/-- **The R-inputs from the literature inputs**: `CalibrationInputsLit → CalibrationInputsR`, so
the R-leaf asks for no more than the literature leaf. Kind: PROVED. -/
theorem CalibrationInputsR.ofLit (h : CalibrationInputsLit D) : CalibrationInputsR D := by
  obtain ⟨B, vL, G₀, hvL, H⟩ := h
  refine ⟨B, vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact ⟨CalibrationModelR.ofLit M⟩

/-- **`RCSteps.calibration` from the R-inputs** ((4.6), tex 3987–4141). Kind: PROVED. -/
theorem calibrationTarget_of_R (Pr : Prints) (hℓ : 0 < ℓ) (h : CalibrationInputsR D) :
    CalibrationTarget D :=
  calibrationTarget_of_H Pr hℓ h.toH

/-- **Non-vacuity in the degenerate case**: given the nine statements, the R-leaf holds when no
address of a final family has the two analytic ranks. Kind: PROVED. -/
theorem calibrationInputsR_of_noAddress (B : CalibrationBookProps)
    (hD : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      AnalyticRank (Etw ℓ (F.h x)) 1 → ¬ AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0) :
    CalibrationInputsR D :=
  ⟨B, 0, 0, le_rfl, fun Co Ce F hF x h1 h0 => absurd h0 (hD Co Ce F hF x h1)⟩

end Leaf

end ZInQ.Manuscript.RC.Wiring.KmIdent
