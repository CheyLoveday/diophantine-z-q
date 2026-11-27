import ZInQKernel.Contrib.OneProof.JavanpeykarJacKReader
import ZInQKernel.Contrib.OneProof.FaltingsRestate
import ZInQKernel.Contrib.OneProof.ChevalleyFree

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open LeafModCurves (IsCurve)
open JavanpeykarDict JavanpeykarFix JavanpeykarDirect JavanpeykarAnRetype JavanpeykarRebase
open ZInQ.LeafPush2 (javanpeykarBound UniformizationExists)
open ZInQ.DefFaltings ZInQ.H5Neron ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightFix
open ZInQ.R3Residual ZInQ.SemistabAssembly ZInQ.SSFaltings

namespace JavanpeykarJacK

/-- The same bound as `JavanpeykarThm111JacK`, expressed using one stable height witness
for the Jacobian of the curve over the number field, as in Section 2.3. -/
def JavanpeykarThm111JacKEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X₀ : Over (Spec (CommRingCat.of K))) [IsCurve X₀]
    [IsIntegral (baseChangeCurve X₀ (AlgebraicClosure K)).left],
    (∃ (n : Type) (_ : Finite n)
      (i : (baseChangeCurve X₀ (AlgebraicClosure K)).left ⟶ ℙ(n; Spec (CommRingCat.of (AlgebraicClosure K)))),
      IsClosedImmersion i ∧ i ≫ ℙ(n; Spec (CommRingCat.of (AlgebraicClosure K))) ↘
        Spec (CommRingCat.of (AlgebraicClosure K)) = (baseChangeCurve X₀ (AlgebraicClosure K)).hom) →
    1 ≤ genusBar X₀ →
    ∀ (V : AbelianVariety K)
      (rep : (picardFunctorDegree X₀.hom 0).obj.RepresentableBy V.group.X),
      PicardTensorCompatible X₀.hom V.group rep →
    ∀ (hB : ∃ d, HasBelyiMapOfDegree (baseChangeCurve X₀ (AlgebraicClosure K)) d),
    ∃ x : ℝ, IsAnStableHeightSS (ofVendored V) x ∧
      x ≤ javanpeykarBound (genusBar X₀) (belyiDegree (baseChangeCurve X₀ (AlgebraicClosure K)) hB)

/-- The analytic predicate with printed semistability agrees with the kernel's
real stable height predicate by the existing metric and semistability comparisons. -/
theorem isAnStableHeightSS_iff_kernel (hT35 : UniformizationExists)
    (hD : SemiAbelianDescendsPerfect) {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (x : ℝ) :
    IsAnStableHeightSS A x ↔ IsStableFaltingsHeight A x :=
  (isAnStableHeightSS_iff A x).trans ((isAnStableHeight_iff hT35 A x).trans
    ⟨isStableFaltingsHeight_of_printed hT35 geomConnOfRationalPoint_proof,
      isPrintedStableHeight_of hT35 hD⟩)

/-- Stable analytic height is invariant under group isomorphisms over the base field;
in particular this transports heights between isomorphic Pic⁰ representatives. -/
theorem isAnStableHeightSS_of_iso (hT35 : UniformizationExists)
    (hD : SemiAbelianDescendsPerfect) {K : Type} [Field K] [NumberField K]
    {A B : PkgI3.AbVar K} (e : A.X ≅ B.X) [IsMonHom e.hom] {x : ℝ}
    (hx : IsAnStableHeightSS A x) : IsAnStableHeightSS B x :=
  (isAnStableHeightSS_iff_kernel hT35 hD B x).mpr <|
    isStableFaltingsHeight_of_iso e ((isAnStableHeightSS_iff_kernel hT35 hD A x).mp hx)

/-- Any two tensor-compatible Pic⁰ representatives give the same analytic
height witnesses. The representing isomorphism preserves the identity
because each representation sends the identity to the trivial bundle. -/
theorem isAnStableHeightSS_of_picZero (hT35 : UniformizationExists)
    (hD : SemiAbelianDescendsPerfect) {K : Type} [Field K] [NumberField K]
    (X : Over (Spec (CommRingCat.of K))) [hX : IsCurve X] (V W : AbelianVariety K)
    (repV : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X)
    (repW : (picardFunctorDegree X.hom 0).obj.RepresentableBy W.group.X)
    (htcV : PicardTensorCompatible X.hom V.group repV)
    (htcW : PicardTensorCompatible X.hom W.group repW) {x : ℝ}
    (hx : IsAnStableHeightSS (ofVendored V) x) : IsAnStableHeightSS (ofVendored W) x := by
  let e := repV.uniqueUpToIso repW
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom := TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  have pointed : η[V.group.X] ≫ e.hom = η[W.group.X] := by
    let T := 𝟙_ (Over (Spec (CommRingCat.of K)))
    change (1 : T ⟶ V.group.X) ≫ e.hom = (1 : T ⟶ W.group.X)
    apply repW.homEquiv.injective
    rw [repW.homEquiv_comp]
    have he : repW.homEquiv e.hom = repV.homEquiv (𝟙 V.group.X) := by
      change repW.homEquiv (repW.homEquiv.symm (repV.homEquiv (𝟙 V.group.X))) = _
      exact repW.homEquiv.apply_symm_apply _
    rw [he, ← repV.homEquiv_eq]
    exact (htcV.homMulEquiv T).map_one.trans (htcW.homMulEquiv T).map_one.symm
  have : GeometricallyIntegral V.group.X.hom := (ofVendored V).geomInt
  have hmon : IsMonHom e.hom := isMonHom_of_isProper_of_geometricallyIntegral e.hom pointed
  let eK : (ofVendored V).X ≅ (ofVendored W).X := e
  have : IsMonHom eK.hom := hmon
  exact isAnStableHeightSS_of_iso hT35 hD (A := ofVendored V) (B := ofVendored W) eK hx

/-- Witness uniqueness uses the Faltings base-change comparison reconstructed
by the active fold, together with the existence of Néron models. -/
theorem isAnStableHeightSS_unique (hT35 : UniformizationExists)
    (hN : NeronModelExists) (hF : FaltingsSemistableHeightBC)
    {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {x y : ℝ}
    (hx : IsAnStableHeightSS A x) (hy : IsAnStableHeightSS A y) : x = y := by
  have kernel {z} (hz : IsAnStableHeightSS A z) : IsStableFaltingsHeight A z :=
    isStableFaltingsHeight_of_printed hT35 geomConnOfRationalPoint_proof
      ((isAnStableHeight_iff hT35 A z).mp ((isAnStableHeightSS_iff A z).mp hz))
  exact isStableFaltingsHeight_uniqueF hN hF (kernel hx) (kernel hy)

/-- Semistable reduction, Néron existence and metrization produce a real height
witness. No field-independence theorem is needed for this existence direction. -/
theorem exists_isAnStableHeightSS (hT35 : UniformizationExists)
    (hD : SemiAbelianDescendsPerfect) (hN : NeronModelExists) (hSS : SemistableReductionThm)
    {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) :
    ∃ x : ℝ, IsAnStableHeightSS A x := by
  obtain ⟨L, iF, iN, iA, hss⟩ := hSS K A
  obtain ⟨𝒩, h𝒩⟩ := hN K A L
  obtain ⟨g, M, rfl⟩ := neronMetrizable_of_t35 hT35 K A L 𝒩 h𝒩
  exact ⟨M.hodge.modelHeight, (isAnStableHeightSS_iff_kernel hT35 hD _ _).mpr
    ⟨L, iF, iN, iA, M.model, h𝒩, hss M.model h𝒩,
      groupModel_height_eq (analyticUniformizationUnique_of_t35 hT35) metrizedDimUnique M⟩⟩

/-- With the independent existence of a height witness, the universal bound supplies
the existential form. -/
theorem javanpeykarThm111JacKEx_of_jacK (hJ : JavanpeykarThm111JacK)
    (hT35 : UniformizationExists) (hD : SemiAbelianDescendsPerfect)
    (hN : NeronModelExists) (hSS : SemistableReductionThm) : JavanpeykarThm111JacKEx := by
  intro K _ _ X₀ _ _ hproj hg V rep htc hB
  obtain ⟨x, hx⟩ := exists_isAnStableHeightSS hT35 hD hN hSS (ofVendored V)
  exact ⟨x, hx, hJ K X₀ hproj hg V rep htc hB x hx⟩

/-- The old row supplies the existential version with the Néron existence and
Raynaud inputs already present in the active chain. -/
theorem javanpeykarThm111JacKEx_of_an (hJ : JavanpeykarThm111An)
    (hR : SZRaynaud.SilverbergZarhinThm35)
    (hD : ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind) :
    JavanpeykarThm111JacKEx := by
  have hE := ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind hD
  have hMT := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hSS := semistableReductionThmIF_of_raynaud (SZRaynaud.raynaudSemistable_of_sz35 hR)
    hMT ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof
    (GapNeron.neronSchemeModelExistsNF hE)
    (ReductGlue.semistableLocalGlobal_leaf GapBLR.neronLocalizesDVR_proved)
  exact javanpeykarThm111JacKEx_of_jacK (javanpeykarThm111JacK_of_an hJ)
    (AvSplit.Final.h38 uniformizationLeafAll_proof hMT) ZInQ.ChevFree.semiAbelianDescendsPerfect_proof
    (ZInQ.Contrib.NeronC.neronModelExists_of_extension hE) (semistableReductionThm_of_IF hSS)

/-- With the Faltings base-change comparison, a bounded witness bounds every witness. -/
theorem javanpeykarThm111JacK_of_jacKEx (hJ : JavanpeykarThm111JacKEx)
    (hT35 : UniformizationExists) (hN : NeronModelExists) (hF : FaltingsSemistableHeightBC) :
    JavanpeykarThm111JacK := by
  intro K _ _ X₀ _ _ hproj hg V rep htc hB x hx
  obtain ⟨y, hy, hle⟩ := hJ K X₀ hproj hg V rep htc hB
  rwa [isAnStableHeightSS_unique hT35 hN hF hx hy]

/-- Read the same chain bound from a single height witness. The active fold provides
`hF` via `faltingsSemistableHeightBC_of_faltingsLemma1Print`. -/
theorem javanpeykarBound_of_jacKEx (hJ : JavanpeykarThm111JacKEx)
    (hS : ConstantFieldExtensionUnramifiedFinite) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hD : SemiAbelianDescendsPerfect) (hN : NeronModelExists) (hF : FaltingsSemistableHeightBC) :
    JavanpeykarBound :=
  javanpeykarBound_of_jacK
    (javanpeykarThm111JacK_of_jacKEx hJ (AvSplit.Final.h38 uniformizationLeafAll_proof hMT) hN hF)
    hS hMT hD

end JavanpeykarJacK
