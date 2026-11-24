# rc-model-target results log

## Setup
- Merge of main 29bfbc3f6 into wip/rc-model-neron 64a338f49: commit 11b3db714.
- Item 6 (rc-model-neron.md same-place row): commit 8dee6dc8f.
- Build seed: copy of a prebuilt tree at a later main (3 added files only) plus the neron worktree build.

## Item 4 (generic): RC/ModelTarget/ComplexReading.lean
- IsComplexLaw g : ∀ p q : complexBase ⟶ ellipticTarget E₀, projectiveValue (p*q).left = pv p.left + pv q.left
- exists_complexLaw := J0Cusps.projectiveGroup_exists; complexLaw (choice), complexLaw_spec
- targetReading g hg : (complexBase ⟶ ellipticTarget E₀) →* Multiplicative (E₀.baseChange ℂ).toAffine.Point
- readComplex E jE g hg (hj : IsMonHom jE.hom) := targetReading ∘ IsMonHom.monoidHom jE.hom
- readComplex_eq : (readComplex .. a).toAdd = projectiveValue (a.left ≫ jE.hom.left) (rfl)
- Build OK (13472 jobs), axioms: propext, Classical.choice, Quot.sound.

## Item 4 (local instance): RC/ModelTarget/LocalReading.lean
- neronDVRLocal : NeronExt.NeronDVRLocal := dvrLocal_of_extension (neronSchemeExtensionExists_of_dedekind neronSchemeExtensionDedekind_proof)
- detectorTarget ell E₀ := ModelNeron.localTarget neronDVRLocal
- neronLaw T : GrpObj T.E := grpObjOfNeron … (complexLaw E₀) T.jE (Néron transport)
- neronLaw_isMonHom T : IsMonHom T.jE.hom (isMonHom_of_neron)
- localReadComplex T, localReadComplex_eq T (rfl), localReadComplex_fits
- Build OK (14381 jobs, no warnings in module), axioms standard.
- Note: LocalTarget.groupE is an arbitrary field; the GoodRow supply uses groupE := neronLaw T, not T.groupE.

## Item 1 (smoothness), chart algebra
- ChartRing.lean: Chart W i := Away grading (coord i); chartConst, ratio, ratio_self, dehomogenize,
  chart_equation, chart_ringHom_ext, chartLift (+_mk/_ratio/_const), chartEquiv. Build OK, std axioms.
- ChartPresentation.lean: presLift/presDehom/presEquiv (AdjoinRoot q ≃+* Chart W i);
  zyEquiv : W.toAffine.CoordinateRing ≃+* Chart W 2; zxEquiv : AdjoinRoot (zxPoly W) ≃+* Chart W 2 (monic in x);
  yEquiv hw : AdjoinRoot (yPoly W c w) ≃+* Chart W 1 (shear x = x'+cz; hw : w*(c³+a₂c²+a₄c+a₆) = -1). Build OK, std axioms.
- ChartSmooth.lean: smooth_away_derivative (monic q over R[X], localized at q' : smooth over R via StandardEtalePair),
  smooth_transport, smooth_zy, smooth_zx, span_partials_zChart [W.IsElliptic], smooth_chartZ : RingHom.Smooth (chartConst W 2). Build OK, std axioms.
- ChartSmoothY.lean: yDeriv, derivative_yPoly, yPoly_monic, smooth_ydz hw, span_yChart hw,
  smooth_yChart_awayZ [W.IsElliptic] (overlap D₊(YZ) via Away.isLocalization_mul twice),
  smooth_chartY [W.IsElliptic] hw : RingHom.Smooth (chartConst W 1). Build OK, std axioms.
