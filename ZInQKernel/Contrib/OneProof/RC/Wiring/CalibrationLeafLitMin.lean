import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeafLit
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLitArithmetic

/-!
# Theorem 5.3, Lane RC0 round 20: the calibration leaf's literature form, minimal named inputs

Proposition `ex:arith-central-calibration` (tex 3987–4141), its Kummer coordinate (tex 3877–3909,
4005–4018, 4050–4064). The literature form `CalibrationInputsLit` (`Wiring/CalibrationLeafLit.lean`)
asks at every address for an RC53 model with its Kummer block's named inputs: finite generation
`hfinite`, the places above `2`, no real places `hK`, finite `2`-primary torsion, rank one, and
the three disk-length identifications `hval₁`–`hval₃`. This file removes the redundant ones.

* `diskLengths_of_tie`: given the eight book statements and the other named inputs, the three
  disk-length identifications follow from the RC53 block's own order tie (`DiskTie.determined`
  against the tie of the constructed integral disks, `diskTie_of_literature`); conversely they
  give the tie (`KummerCoordinateBlockLit.tie`). So the identifications restate the old tie.
* `calibrationInputsLit_iff_named`: the literature form is the eight statements and, at every
  address, an RC53 model with `hfinite`, `h2`, `hK`, `finite2` and `rank_one` (no identification).
* `calibrationInputsLit_iff_min`: `hfinite` is derived as well (`centralCohomologyFinite` from the
  two finiteness statements and `h2`): the literature form is exactly the eight statements and, at
  every address, an RC53 model with `h2`, `hK`, `finite2` and `rank_one`.
* `isTotallyComplex_of_quadData_neg`, `hK_of_kfin_neg`: `hK` follows from the model's quadratic
  data when `k < 0` (the converse, that `ℚ(√k)` with `k > 0` has a real place, is standard and not
  formalized here); so wherever the leaf covers an address it asserts `D.kfin < 0` of its data.
* `h_ne_zero_of_finalFamilyAt`, `qstar_three`: `h_x ≠ 0` at every address of a final family, and
  `q* = −3` for `q = 3`, so Lean's admissible families do have addresses with `h_x < 0`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData DiskTie KummerCoordinateBlockG
  CalibrationModelHK2)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve compactCentralComplex)
open ZInQ.Contrib.RC53Assist.CalibrationModel (centralDiskMatrix centralDiskMatrix_det_ne_zero)
open ZInQ.Contrib.RC53Assist.CalibrationShape (centralCohomologyFinite)
open ZInQ.Manuscript.RC.Height (QuadData)
open NumberField IsDedekindDomain

attribute [local instance] Nat.fact_prime_two

/-! **The disk-length identifications are the old tie** -/

/-- **The disk-length identifications from the RC53 tie** (tex 4005–4018, 4050–4060): for an RC53
Kummer block `L` (`KummerCoordinateBlockG`, with its order tie), the eight book statements and the
named inputs (finite generation, the places above `2`, no real places, finite `2`-primary
torsion, rank one), the three disks have the lengths of the constructed integral disks: both
satisfy an order tie for the same genuine data (`L.tie` and `diskTie_of_literature`), and an order
tie determines the valuations (`DiskTie.determined`). Kind: PROVED. -/
theorem diskLengths_of_tie {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ}
    {hZ : ℤ} {n : ℕ} {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])}
    {zK wK : Fin n → PowerSeries ℚ_[2]} {j vL m : ℤ} {tA shaA : ℕ}
    (L : KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA) (B : CalibrationBookProps)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex L.G).homology n))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ L.G.S)
    (hK : IsTotallyComplex K)
    (finite2 : ∀ [DecidableEq K],
      Finite (AddCommGroup.primaryComponent (centralCurve L.G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex L.G).homology 1) = 1) :
    L.x₁.valuation = (centralDiskMatrix L.G hfinite 1).det.valuation ∧
      L.x₂.valuation = (centralDiskMatrix L.G hfinite 2).det.valuation ∧
      L.x₃.valuation = (centralDiskMatrix L.G hfinite 3).det.valuation := by
  classical
  have := finite2
  exact L.tie.determined (diskTie_of_literature L.G hfinite B hK h2 rank_one)
    (ZInQ.Contrib.RC53Assist.Calibration.CentralDiskOrders.x_ne_zero L.hx₁)
    (ZInQ.Contrib.RC53Assist.Calibration.CentralDiskOrders.x_ne_zero L.hx₂)
    (ZInQ.Contrib.RC53Assist.Calibration.CentralDiskOrders.x_ne_zero L.hx₃)
    (centralDiskMatrix_det_ne_zero L.G hfinite 1) (centralDiskMatrix_det_ne_zero L.G hfinite 2)
    (centralDiskMatrix_det_ne_zero L.G hfinite 3)

variable {ℓ : ℕ} {D : RCData ℓ}

/-- **The literature form without the disk-length identifications** ((4.6), tex 3987–4141): the
eight book statements and, at every address of a final family with `ord L(E^{(h_x)}) = 1` and
`ord L(E^{(h_x k)}) = 0`, an RC53 model with finite generation, the places above `2`, no real
places, finite `2`-primary torsion and rank one (`calibrationInputsLit_iff`, with the
identifications from `diskLengths_of_tie`). Kind: PROVED. -/
theorem calibrationInputsLit_iff_named :
    CalibrationInputsLit D ↔ CalibrationBookProps ∧ ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ,
      ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
        AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 →
        ∃ M : CalibrationModelHK2 D vL G₀ F x,
          (∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex M.kummer.G).homology n)) ∧
          (∀ v : HeightOneSpectrum (𝓞 M.K), (2 : 𝓞 M.K) ∈ v.asIdeal → v ∈ M.kummer.G.S) ∧
          IsTotallyComplex M.K ∧
          (∀ [DecidableEq M.K],
            Finite (AddCommGroup.primaryComponent (centralCurve M.kummer.G).toAffine.Point 2)) ∧
          Module.finrank ℤ_[2] ((compactCentralComplex M.kummer.G).homology 1) = 1 := by
  rw [calibrationInputsLit_iff]
  constructor
  · rintro ⟨B, vL, G₀, hvL, H⟩
    refine ⟨B, vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
    obtain ⟨M, hfinite, h2, hK, finite2, rank_one, -, -, -⟩ := H Co Ce F hF x h1 h0
    exact ⟨M, hfinite, h2, hK, finite2, rank_one⟩
  · rintro ⟨B, vL, G₀, hvL, H⟩
    refine ⟨B, vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
    obtain ⟨M, hfinite, h2, hK, finite2, rank_one⟩ := H Co Ce F hF x h1 h0
    obtain ⟨e1, e2, e3⟩ := diskLengths_of_tie M.kummer B hfinite h2 hK finite2 rank_one
    exact ⟨M, hfinite, h2, hK, finite2, rank_one, e1, e2, e3⟩

/-- **The literature form with the minimal named inputs** ((4.6), tex 3987–4141): the eight book
statements and, at every such address, an RC53 model with the places above `2`, no real places,
finite `2`-primary torsion and rank one; finite generation follows from the two finiteness
statements and the places above `2` (`centralCohomologyFinite`), and the disk lengths from the
model's tie (`calibrationInputsLit_iff_named`). Kind: PROVED. -/
theorem calibrationInputsLit_iff_min :
    CalibrationInputsLit D ↔ CalibrationBookProps ∧ ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ,
      ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
        AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 →
        ∃ M : CalibrationModelHK2 D vL G₀ F x,
          (∀ v : HeightOneSpectrum (𝓞 M.K), (2 : 𝓞 M.K) ∈ v.asIdeal → v ∈ M.kummer.G.S) ∧
          IsTotallyComplex M.K ∧
          (∀ [DecidableEq M.K],
            Finite (AddCommGroup.primaryComponent (centralCurve M.kummer.G).toAffine.Point 2)) ∧
          Module.finrank ℤ_[2] ((compactCentralComplex M.kummer.G).homology 1) = 1 := by
  rw [calibrationInputsLit_iff_named]
  constructor
  · rintro ⟨B, vL, G₀, hvL, H⟩
    refine ⟨B, vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
    obtain ⟨M, -, h2, hK, finite2, rank_one⟩ := H Co Ce F hF x h1 h0
    exact ⟨M, h2, hK, finite2, rank_one⟩
  · rintro ⟨B, vL, G₀, hvL, H⟩
    refine ⟨B, vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
    obtain ⟨M, h2, hK, finite2, rank_one⟩ := H Co Ce F hF x h1 h0
    exact ⟨M,
      centralCohomologyFinite M.kummer.G B.milneLocalFiniteness B.milneGlobalFiniteness h2,
      h2, hK, finite2, rank_one⟩

/-! **No real places from `k < 0`** -/

/-- **A number field containing a square root of a negative integer has no real places** (tex
2598–2599, 2616–2626: the companion `k < 0` of the remaining branch): a real embedding would send
the square root to a real number with negative square. Kind: PROVED. -/
theorem isTotallyComplex_of_quadData_neg {K : Type} [Field K] [NumberField K] {k : ℤ}
    (hk : k < 0) (q : QuadData K (k : ℚ)) : IsTotallyComplex K := by
  refine ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mp fun hv => ?_⟩
  let ψ := InfinitePlace.embedding_of_isReal hv
  have h1 : ψ q.s ^ 2 = (k : ℝ) := by
    rw [← map_pow, q.hsk, map_intCast (algebraMap ℚ K), map_intCast]
  have h2 : (k : ℝ) < 0 := by exact_mod_cast hk
  nlinarith [sq_nonneg (ψ q.s)]

/-- **The named input `hK` of a model from `D.kfin < 0`** (the model's field contains `√k`, its
quadratic data `M.quad`). Kind: PROVED. -/
theorem hK_of_kfin_neg {vL G₀ : ℤ} {F : Family} {x : Addr F.b}
    (M : CalibrationModelHK2 D vL G₀ F x) (hk : D.kfin < 0) : IsTotallyComplex M.K :=
  isTotallyComplex_of_quadData_neg hk M.quad

/-! **The sign of `h_x`** -/

/-- **`h_x ≠ 0` at every address of a final family** (tex 1864–1869): `h_x` is a product of
powers of the nonzero `q*` over the family's primes. Kind: PROVED. -/
theorem h_ne_zero_of_finalFamilyAt {Co Ce : ℤ} {F : Family} (hF : D.FinalFamilyAt Co Ce F)
    (x : Addr F.b) : F.h x ≠ 0 := by
  unfold Family.h
  rw [Finset.prod_ne_zero_iff]
  intro q hq
  exact pow_ne_zero _ (qstar_ne_zero (hF.1 q hq).1.ne_zero)

/-- **`q* = −3` for `q = 3`** (so Lean's admissible families have addresses with `h_x < 0`,
whereas the text's families have one real sign, tex 1864–1869). Kind: PROVED. -/
theorem qstar_three : qstar 3 = -3 := by
  unfold qstar
  norm_num

end ZInQ.Manuscript.RC.Wiring
