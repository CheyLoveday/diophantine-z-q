import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Leaf
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Chebotarev
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Witness
import ZInQKernel.Contrib.OneProof.RC.Wiring.PreSpec

/-!
# Theorem 5.3, Lane RC24: the address leaf with Chebotarev from the density theorem

The genuine address leaf of `Leaf.lean` with the Galois trace models replaced by the density models
of `Chebotarev.lean`: the PRINT field `chebotarev` and the GLUE field `finiteIndex` of
`GaloisTraceModel` are replaced by the openness (a) and the unramifiedness (b) of `N_U` (GLUE,
tex 9663–9669, 9745–9750), and Chebotarev's theorem is the repository's PROVED density theorem
(`ZInQ.Contrib.ChebFD.C10.frobDense`, `ZInQ.Contrib.chebotarevExists`; tex 9666–9668, 9712–9717,
9768–9770, 9896–9898, 9919–9921).

Round 2: the odd reading is read on the intrinsic odd filter (`LabelData.oddAdmissible`); the model
fields are budgeted (tex 9447–9468, 9649–9654); and the odd witness of the stabilized tables is no
longer an input: `oddWitness_of_dataSpec` derives it from the attained odd minimum
`δ_o ∈ depthSet` (tex 2590–2593, 10190–10199, 10501–10505, 10547), so the consumer
`addressLeaf_of_densityLeaf` takes the data specification and that membership, both available
where the leaf is used.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Symbols
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Filter

section Density

variable {ℓ : ℕ} (W : WData ℓ) (D : LabelData W) (Rev : Finset ℕ → ZMod 2)

/-- **Density models of the odd stage source** (the fields of `GaloisDensityModel`: GLUE trace
identities, ELLIOT readings, tex 9671–9745, 9905–9918; GLUE Kummer, openness, unramifiedness,
tex 9663–9669, 9745–9750): for every cutoff, on a set of stages of the ultrafilter
(tex 10533–10540: "for every |U| ≤ W … at most W+1 vertices"). -/
def OddDensityModels : Prop :=
  ∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ),
    Nonempty (GaloisDensityModel (D.T₁ θ) (Rodd W D θ) (apo ℓ) (Wc + 1) (stageChar D.m₁ (D.ℓ₀ θ)))

/-- **Density models of the transported even source at every budget** (tex 10288–10318; 9450–9452,
9570–9573, 9916: for the even source the divisions are exact at every `U`). -/
def EvenDensityModels : Prop :=
  ∀ B : ℕ, Nonempty (GaloisDensityModel D.T₂ Rev (apk W) B (typChar D.m₂))

/-- **Galois trace models from density models** (PROVED: `GaloisDensityModel.toGaloisTraceModel`,
with `chebotarev` from the density theorem). -/
theorem oddGaloisModels_of_density (h : OddDensityModels W D) : OddGaloisModels W D :=
  fun Wc => (h Wc).mono fun _ ⟨X⟩ => ⟨X.toGaloisTraceModel⟩

/-- **Galois trace models of the even source from density models** (PROVED). -/
theorem evenGaloisModels_of_density (h : EvenDensityModels W D Rev) : EvenGaloisModels W D Rev :=
  fun B => match h B with | ⟨X⟩ => ⟨X.toGaloisTraceModel⟩

end Density

/-! ## The odd witness from the attained minimum -/

/-- **The odd witness of the stabilized tables from the attained odd minimum** (PROVED from
`oddWitness_of_depthMin`; tex 2590–2593, 10190–10199, 10501–10505, 10547): with the data's
specification (the stage support is the prepared filter cut by a stage condition; prepared indices
are positive, squarefree and prime to `W.S`), every visible index lies in the intrinsic odd filter
(`LabelData.oddAdmissible_iff`) and is a unit at `m₁ ℓ₀` (`OddFilter`). This theorem uses
attainment in the supplied stage support. It does not compare the original intrinsic depth set
with the depth set after additional stationary exclusions; the preservation assertion of tex
2609–2612, 10519–10521 and 10549–10551 is separate. -/
theorem oddWitness_of_dataSpec {ℓ : ℕ} {W : WData ℓ} (D : LabelData W) (hdata : PreDataSpec W)
    (hprep : PreparedSpec W)
    (hδ : W.δo ∈ AppGEndpoints.DepthSet W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd)) W.admissible)
    (hU : ¬ W.OddEmptyUnit) (hodd : OddReadings W D) (hofilt : OddFilter W D) :
    OddWitness W D := by
  obtain ⟨T, hadm, -⟩ := hdata.admissible_split
  have hsplit : ∀ θ d, W.admissible θ d → W.prepared d := fun θ d h => ((hadm θ d).mp h).1
  have hsub : ∀ θ d, W.admissible θ d → D.oddAdmissible θ d := fun θ d h =>
    (D.oddAdmissible_iff θ d (fun p hp _ => (hprep d (hsplit θ d h)).2.2.2 p hp)).mpr h
  exact oddWitness_of_depthMin D hδ hU hodd
    (fun θ d h => ⟨(hprep d (hsplit θ d h)).1, (hprep d (hsplit θ d h)).2.1⟩)
    (fun θ d h => (hofilt θ d (hsub θ d h)).2.2.2) hsub

/-- **The genuine address leaf with Chebotarev from the density theorem** (round 2): label data
with the intrinsic odd filter (definition), a fresh prime of `k` (ELLIOT), budgeted density models
of the odd stage source and of the transported even source (GLUE trace identities, Kummer,
openness, unramifiedness; ELLIOT readings), the odd, prepared and even filters (definition), the
`K`-split seed (ELLIOT; under the hypotheses of `exists_unit_of_kSplitSeed` equivalent to a nonempty
`K`-split unit of `Rev`, `kSplitSeed_of_unit`) and the even reading (ELLIOT; (F.1)'s conclusion for
the chosen reading `Rev`; the leaf ties `Rev` to the transported source only through the even
models, the even filter and this clause). The odd witness is not an input
(`oddWitness_of_dataSpec`). Its scope is Branch 2 (`¬ W.OddEmptyUnit`).
The predicate does not itself require attainment of `δ_o`. Its consumer additionally
requires `PreDataSpec`, `PreparedSpec`, `δ_o ∈ depthSet` and the remaining-branch
hypothesis. The bare predicate can retain a zero odd source after replacing its odd
models by zero models, but such a source has empty depth set and cannot satisfy the
consumer's attainment premise. `oddAdmissible_iff` identifies the intrinsic filter only
away from `W.S`; the fields do not uniquely determine its values elsewhere. -/
def AddressDensityLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ (D : LabelData W) (Rev : Finset ℕ → ZMod 2), FreshPrime W D ∧ OddDensityModels W D ∧
    OddFilter W D ∧ PreparedFilter W D ∧ EvenDensityModels W D Rev ∧
    EvenFilter W D Rev ∧ KSplitSeed W D Rev ∧ EvenReading W D Rev

/-- **The genuine address leaf from the density form** (PROVED), in Branch 2, with the data's
specification and the attained minimum. -/
theorem addressGenuineLeaf_of_densityLeaf {ℓ : ℕ} {W : WData ℓ} (hdata : PreDataSpec W)
    (hprep : PreparedSpec W)
    (hδ : W.δo ∈ AppGEndpoints.DepthSet W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd)) W.admissible)
    (hU : ¬ W.OddEmptyUnit) (h : AddressDensityLeaf W) : AddressGenuineLeaf W := by
  obtain ⟨D, Rev, h1, h2, h4, h5, h6, h7, h8, h9⟩ := h
  have hodd : OddReadings W D := oddReadings_of_galois W D (oddGaloisModels_of_density W D h2)
  exact ⟨D, Rev, h1, oddGaloisModels_of_density W D h2,
    oddWitness_of_dataSpec D hdata hprep hδ hU hodd h4, h4, h5,
    evenGaloisModels_of_density W D Rev h6, h7, h8, h9⟩

/-- **`AddressLeaf` from the density form, in Branch 2** (PROVED; tex 2588–2593, 10268–10270,
10501–10505: the address construction is needed only when the odd empty configuration is not a
unit, which `AddressPackageStagedLeaf` takes as a hypothesis). -/
theorem addressLeaf_of_densityLeaf {ℓ : ℕ} {W : WData ℓ} (hℓ : Adm ℓ) (hcomp : CompanionLeaf W)
    (hdata : PreDataSpec W) (hprep : PreparedSpec W)
    (hδ : W.δo ∈ AppGEndpoints.DepthSet W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd)) W.admissible)
    (h : ¬ W.OddEmptyUnit → AddressDensityLeaf W) : AddressLeaf W :=
  addressLeaf_of_stagedPackage W fun A CE CR Cper Cdet h33 h34 h35 hvis hU =>
    addressPackageStagedLeaf_of_genuineLeaf hℓ hcomp
      (addressGenuineLeaf_of_densityLeaf hdata hprep hδ hU (h hU)) A CE CR Cper Cdet h33 h34 h35
      hvis hU

end ZInQ.Manuscript.RC.AddressGenuine
