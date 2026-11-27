import ZInQKernel.Contrib.CloudB3E2Norm.CentralSpecC1

/-!
# The dictionary between the central Kummer data and the presentation

Manuscript `diophantine_zq.tex`, tex 3904, 3911–3915 (`E^{(h)}[2^s] ≅ E[2^s](χ_h)`).

The comparison `CentralStageComparison₂` takes the twist identification `twistPt` of the points
of the central curve `E^{(h)}` of Kummer data `G` with the points of the presentation's curve
`W` as data. **`CentralTwistDict G h01 W s hs`** (definition) records the actual dictionary:
`G.S ⊆ S₀`, `G.W = W`, the twist parameter `hZ = h`, and the square root `G.s ↦ s`.

* **`CentralTwistDict.twistPt`** (definition): the canonical identification
  `E^{(h)}(K_{S_G}) ≃ E(K_{S_G}) → E(K_{S₁})` (`globalTwistPointEquiv`, then the inclusion of
  fields);
* `twistPt_injective` (PROVED);
* **`twistPt_galois`** (PROVED): it is `χ_h`-equivariant,
  `twistPt(g P) = χ_h(g) · g(twistPt P)` for `g ∈ G_{K,S}` (`globalTwistPointEquiv_galois`,
  `ptMap_smul`, and `χ_{G.s} = χ_s` on `G_{K,S}` from `G.s ↦ s`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve globalTwistPointEquiv
  globalTwistPointEquiv_galois)

attribute [local instance] ptSAction

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))} {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- **The dictionary between Kummer data `G` and the presentation's objects** (tex 3904):
`G.S ⊆ S₀`, the same curve, the same twist parameter, the same square root.
Kind: definition (data with its hypotheses). -/
structure CentralTwistDict (G : GenuineKummerData K E₀ hZ) (h01 : S₀ ⊆ S₁) (W : WeierstrassCurve K)
    {h : K} (s : KS K S₀) (hs : s ^ 2 = algebraMap K (KS K S₀) h) : Prop where
  /-- the support of `G` lies in the presentation's old support -/
  hGS : G.S ⊆ S₀
  /-- the same curve -/
  hW : G.W = W
  /-- the same twist parameter -/
  hh : ((hZ : ℤ) : K) = h
  /-- the same square root -/
  hsG : ksIncl hGS G.s = s

variable {G : GenuineKummerData K E₀ hZ} {h01 : S₀ ⊆ S₁} {W : WeierstrassCurve K} {h : K}
  {s : KS K S₀} {hs : s ^ 2 = algebraMap K (KS K S₀) h}

/-- **The canonical twist identification of the central points with `E(K_{S₁})`**.
Kind: definition. -/
def CentralTwistDict.twistPt (D : CentralTwistDict G h01 W s hs) :
    ((centralCurve G).baseChange (KS K G.S)).toAffine.Point →+ PtS K S₁ W :=
  (ptMap (D.hGS.trans h01) W).comp
    ((D.hW ▸ (globalTwistPointEquiv G.W G.s G.hs G.hs0).toAddMonoidHom :
      ((centralCurve G).baseChange (KS K G.S)).toAffine.Point →+ PtS K G.S W))

omit [DecidableEq K] in
/-- The twist identification is injective (PROVED). -/
theorem CentralTwistDict.twistPt_injective (D : CentralTwistDict G h01 W s hs) :
    Function.Injective D.twistPt := by
  obtain ⟨hGS, hW, hh, hsG⟩ := D
  subst hW
  exact (ptMap_injective _ _).comp (globalTwistPointEquiv G.W G.s G.hs G.hs0).injective

omit [DecidableEq K] in
/-- `χ_{G.s} = χ_s` on `G_{K,S}` (PROVED): the two square roots agree in `K_{S₀}`. -/
theorem CentralTwistDict.quadChar_eq (D : CentralTwistDict G h01 W s hs) (hs0 : s ≠ 0)
    (hS : S₀ ⊆ S) (g : GKS K S) :
    quadChar G.s G.hs G.hs0 (inflMap K (D.hGS.trans hS) g) =
      quadChar s hs hs0 (inflMap K hS g) := by
  have e1 := quadChar_spec G.s G.hs G.hs0 (inflMap K (D.hGS.trans hS) g)
  have e2 := quadChar_spec s hs hs0 (inflMap K hS g)
  rw [inflMap_trans D.hGS hS g] at e1
  have e3 := congrArg (ksIncl D.hGS) e1
  rw [ksIncl_infl D.hGS, D.hsG, map_zsmul, D.hsG, e2] at e3
  have hne := neg_ne_self_of_ne_zero s hs0
  rw [inflMap_trans D.hGS hS g]
  rcases Int.units_eq_one_or (quadChar s hs hs0 (inflMap K hS g)) with h1 | h1 <;>
    rcases Int.units_eq_one_or (quadChar G.s G.hs G.hs0 (inflMap K D.hGS (inflMap K hS g))) with
      h2 | h2 <;>
    simp only [h1, h2] at e3 ⊢ <;> simp at e3 <;>
    first | exact absurd e3.symm hne | exact absurd e3 hne

omit [DecidableEq K] in
/-- **The twist identification is `χ_h`-equivariant** (PROVED): for `g ∈ G_{K,S}`,
`twistPt(g P) = χ_h(g) · g(twistPt P)`. -/
theorem CentralTwistDict.twistPt_galois (D : CentralTwistDict G h01 W s hs) (hs0 : s ≠ 0)
    (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S) (g : GKS K S)
    (P : ((centralCurve G).baseChange (KS K G.S)).toAffine.Point) :
    D.twistPt (Affine.Point.map (galS K G.S (inflMap K ((D.hGS.trans h01).trans h1) g)).toAlgHom
        P) =
      ((quadChar s hs hs0 (inflMap K hS g) : ℤˣ) : ℤ) • (inflMap K h1 g • D.twistPt P) := by
  have hq := D.quadChar_eq hs0 hS g
  obtain ⟨hGS, hW, hh, hsG⟩ := D
  subst hW
  change ptMap (hGS.trans h01) G.W (globalTwistPointEquiv G.W G.s G.hs G.hs0
      (Affine.Point.map (galS K G.S (inflMap K ((hGS.trans h01).trans h1) g)).toAlgHom P)) =
    ((quadChar s hs hs0 (inflMap K hS g) : ℤˣ) : ℤ) • (inflMap K h1 g •
      ptMap (hGS.trans h01) G.W (globalTwistPointEquiv G.W G.s G.hs G.hs0 P))
  rw [globalTwistPointEquiv_galois, map_zsmul, inflMap_trans (hGS.trans h01) h1 g,
    ← ptS_smul_def, ptMap_smul, ← inflMap_trans (hGS.trans h01) h1 g,
    show (hGS.trans h01).trans h1 = hGS.trans hS from rfl, hq]

end ZInQ.Contrib.CloudB3E2.NormCochain
