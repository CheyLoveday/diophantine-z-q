import ZInQKernel.Contrib.OneProof.HeightModelM.EGA977
import ZInQKernel.Contrib.OneProof.SemistableNeronBaseChangeNoSGA3
import ZInQKernel.Contrib.OneProof.SemistablePrintedReadings

/-!
# The identity component of a group model over `𝓞_L` is open (from EGA IV₃ (9.7.7))

For a smooth group model `𝒢` of `A_L` over `𝓞_L`, the union `𝒢⁰ = idCompSet 𝒢.G` of the identity
components of the fibres is open in `𝒢`, given the printed leaf `EGAIV_9_7_7_OL`:

* `geometricallyConnected_genericFibre`: the generic fibre is geometrically connected (it is
  connected, `CToPrinted.idCompGenericFibre`, and has the rational point of the unit section;
  Stacks 04KV, `geomConnOfRationalPoint_proof`);
* `isOpen_idCompSet_of_generic`: `GenericConnectedFibresOL` gives finitely many disconnected
  fibres, and `SGA3Nbhd.isOpen_idCompSet_of_finite` concludes;
* `SGA3_VIB_3_10_NeronOLPrinted`, the openness of `𝒩⁰` for semistable Néron models (semistability
  as printed, `IsSemistablePrinted`), and its proofs from `GenericConnectedFibresOL` and from the
  EGA leaf.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology MonObj
open MonoidalCategory CartesianMonoidalCategory CToPrinted
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.SemistabAssembly
open scoped NumberField

set_option linter.style.haveILetI false

namespace ZInQ.HeightModelM

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- The fibre of a group model over the generic point is connected. -/
theorem isConnected_genericFibre (𝒢 : GroupModel A L) :
    _root_.IsConnected (𝒢.G.hom ⁻¹' {genericPt L}) := by
  have he : (η[𝒢.G] : 𝟙_ (Over _) ⟶ 𝒢.G).left (genericPt L) ∈ 𝒢.G.hom ⁻¹' {genericPt L} :=
    SGA3IdComp.hom_e 𝒢.G _
  have hsub : 𝒢.G.hom ⁻¹' {genericPt L} ⊆ connectedComponentIn (𝒢.G.hom ⁻¹' {genericPt L})
      ((η[𝒢.G] : 𝟙_ (Over _) ⟶ 𝒢.G).left (genericPt L)) := by
    intro x hx
    have hx' : 𝒢.G.hom x = genericPt L := hx
    have h1 := idCompGenericFibre K A L 𝒢 x (by rw [hx']; rfl)
    have h2 : x ∈ connectedComponentIn (𝒢.G.hom ⁻¹' {𝒢.G.hom x})
        ((η[𝒢.G] : 𝟙_ (Over _) ⟶ 𝒢.G).left (𝒢.G.hom x)) := h1
    rwa [hx'] at h2
  have heq := (connectedComponentIn_subset _ _).antisymm hsub
  rw [← heq]
  exact isConnected_connectedComponentIn_iff.mpr he

/-- **The generic fibre of a group model is geometrically connected** (connected with a rational
point: Stacks 04KV, `geomConnOfRationalPoint_proof`). -/
theorem geometricallyConnected_genericFibre (𝒢 : GroupModel A L) :
    GeometricallyConnected (𝒢.G.hom.fiberToSpecResidueField (genericPt L)) := by
  have hc : ConnectedSpace (𝒢.G.hom.fiber (genericPt L)) := by
    have : ConnectedSpace (𝒢.G.hom ⁻¹' {genericPt L}) :=
      Subtype.connectedSpace (isConnected_genericFibre 𝒢)
    exact (𝒢.G.hom.fiberHomeo (genericPt L)).connectedSpace_iff.mpr this
  have hlft : LocallyOfFiniteType (𝒢.G.hom.fiberToSpecResidueField (genericPt L)) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  have hqc : QuasiCompact (𝒢.G.hom.fiberToSpecResidueField (genericPt L)) :=
    MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  exact geomConnOfRationalPoint_proof
    ((Spec (CommRingCat.of (𝓞 L))).residueField (genericPt L)) (𝒢.G.hom.fiber (genericPt L))
    (𝒢.G.hom.fiberToSpecResidueField (genericPt L)) (SGA3IdComp.eF 𝒢.G (genericPt L))
    (SGA3IdComp.eF_fac 𝒢.G (genericPt L)) hlft hqc hc

/-- **`𝒢⁰` is open, from the finiteness of the disconnected fibres.** -/
theorem isOpen_idCompSet_of_generic (h : GenericConnectedFibresOL) (𝒢 : GroupModel A L) :
    IsOpen (idCompSet 𝒢.G) := by
  have hfin : {t : Spec (CommRingCat.of (𝓞 L)) |
      ¬ _root_.IsPreconnected (𝒢.G.hom ⁻¹' {t})}.Finite :=
    h L 𝒢.G.left 𝒢.G.hom (geometricallyConnected_genericFibre 𝒢)
  refine SGA3Nbhd.isOpen_idCompSet_of_finite 𝒢.G _ hfin ?_ (fun t ht => not_not.mp ht)
  intro t ht
  by_cases h0 : t.asIdeal = ⊥
  · exfalso
    apply ht
    have hgt : t = genericPt L := PrimeSpectrum.ext h0
    rw [hgt]
    exact (isConnected_genericFibre 𝒢).isPreconnected
  · have hm : t.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h0 t.isPrime
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal t).mpr hm

/-- **`𝒢⁰` is open, from EGA IV₃ (9.7.7)(ii).** -/
theorem isOpen_idCompSet_of_ega (h : EGAIV_9_7_7_OL) (𝒢 : GroupModel A L) :
    IsOpen (idCompSet 𝒢.G) :=
  isOpen_idCompSet_of_generic (genericConnectedFibresOL_of_ega h) 𝒢

/-- **`𝒩⁰` is open for semistable Néron models over `𝓞_L`** (SGA 3 VI_B 3.10 at the one base
the height comparison needs; semistability as printed). -/
def SGA3_VIB_3_10_NeronOLPrinted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒩 : GroupModel A L), 𝒩.IsNeronModel →
    IsSemistablePrinted 𝒩 → IsOpen (idCompSet 𝒩.G)

/-- `GenericConnectedFibresOL` gives `SGA3_VIB_3_10_NeronOLPrinted`. -/
theorem sga3_VIB_3_10_NeronOLPrinted_of_generic (h : GenericConnectedFibresOL) :
    SGA3_VIB_3_10_NeronOLPrinted :=
  fun _ _ _ _ _ _ _ _ 𝒩 _ _ => isOpen_idCompSet_of_generic h 𝒩

/-- The EGA leaf gives `SGA3_VIB_3_10_NeronOLPrinted`. -/
theorem sga3_VIB_3_10_NeronOLPrinted_of_ega (h : EGAIV_9_7_7_OL) :
    SGA3_VIB_3_10_NeronOLPrinted :=
  sga3_VIB_3_10_NeronOLPrinted_of_generic (genericConnectedFibresOL_of_ega h)

end ZInQ.HeightModelM
