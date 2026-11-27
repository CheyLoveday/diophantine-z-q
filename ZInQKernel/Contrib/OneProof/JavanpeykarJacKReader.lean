import ZInQKernel.Contrib.OneProof.JavanpeykarJacK

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonObj
open LeafModCurves (IsCurve)
open JavanpeykarDict JavanpeykarFix JavanpeykarDirect JavanpeykarAnRetype JavanpeykarRebase
open ZInQ.LeafPush2 (javanpeykarBound)
open ZInQ.HeightFix ZInQ.R3Residual ZInQ.SemistabAssembly

namespace JavanpeykarJacK

/-- Read the bound at the Pic⁰ representative over `K`. Stichtenoth's constant-field
extension result yields the given Belyi degree over the closure; the least degree
can only improve the printed bound. -/
theorem javanpeykarBound_of_jacK (hJ : JavanpeykarThm111JacK)
    (hS : ConstantFieldExtensionUnramifiedFinite)
    (hMT : AvSplit.MumfordTorsionAlgClosed) (hD : ZInQ.HeightFix.SemiAbelianDescendsPerfect) :
    ZInQ.HeightSplit.JavanpeykarBound := by
  intro K _ _ X _ _ P₀ J aj hJac g hg hg1 t ht d hd hd0 x hx
  have hX : IsCurve X := inferInstance
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  letI : X.left.Over (Spec (CommRingCat.of K)) := ⟨X.hom⟩
  have : SmoothOfRelativeDimension 1 (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ Spec (CommRingCat.of K)) := inferInstanceAs (IsProper X.hom)
  have : GeometricallyIntegral (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  -- Identify the kernel Jacobian with the Pic⁰ representative over K.
  obtain ⟨V, rep, htc, -⟩ := exists_abelianVariety_picardDegreeZero (baseField := K) X.left
  obtain ⟨e, he⟩ := abVarIso_picZero_of_isJacobian hX hJac V rep htc
  have hT35 := AvSplit.Final.h38 uniformizationLeafAll_proof hMT
  have hx' : IsAnStableHeightSS (ofVendored V) x :=
    (isAnStableHeightSS_iff _ x).mpr ((isAnStableHeight_iff hT35 _ x).mpr
      (isPrintedStableHeight_of hT35 hD (isStableFaltingsHeight_of_iso e hx)))
  -- (2) `g` is the genus of `X_K̄`
  have hgen : g = genusBar X := by
    have h2 := dim_eq_genusK hX hJac
    rw [hg] at h2
    rw [genusBar_eq hX]
    exact_mod_cast h2
  subst hgen
  -- (3) Stichtenoth, finite form: a Belyi function of `X_K̄` over `K̄`
  obtain ⟨hint, t', ht', hd'⟩ := belyiBaseChange_of_full (full_of_finite hS) K X t ht d hd hd0
  -- (b) the Belyi map
  have : IsProper (baseChangeCurve X (AlgebraicClosure K)).hom :=
    inferInstanceAs (IsProper ((AlgebraicGeometry.baseChange K (AlgebraicClosure K)).obj X).hom)
  have : SmoothOfRelativeDimension 1 (baseChangeCurve X (AlgebraicClosure K)).hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1
      ((AlgebraicGeometry.baseChange K (AlgebraicClosure K)).obj X).hom)
  obtain ⟨β, hβ⟩ := belyiMapOfFunction_proof (AlgebraicClosure K)
    (baseChangeCurve X (AlgebraicClosure K)) t' ht' d hd' hd0
  -- (c) `X_K̄` is projective
  have hproj := exists_closedImmersion_projectiveSpace (baseChangeCurve X (AlgebraicClosure K))
  -- Apply the bound to V/K and compare the least Belyi degree with d.
  have hB : ∃ d, HasBelyiMapOfDegree (baseChangeCurve X (AlgebraicClosure K)) d :=
    ⟨d, hd0, β, hβ⟩
  exact (hJ K X hproj hg1 V rep htc hB x hx').trans
    (javanpeykarBound_mono _ (belyiDegree_le hβ hd0))

end JavanpeykarJacK
