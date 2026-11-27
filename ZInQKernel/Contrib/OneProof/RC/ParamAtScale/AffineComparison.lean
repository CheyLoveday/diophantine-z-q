import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.Coordinates
import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.SchemeComparison

/-! The Laurent expansions of the two coordinates determine their pullbacks
on the affine chart, as used in tex 1785–1787. Provenance (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Topology WeierstrassCurve ModularCurve
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.RC53Assist.IsogenyScheme

namespace ZInQ.Manuscript.RC.ParamAtScale

open PreparedParam

/-- The section `Y/Z` on the affine chart of the projective model. -/
def sectionYOverZ (E : WeierstrassCurve ℚ) :
    Γ(Proj E.toProjective.grading, Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)) :=
  (Proj.awayToSection E.toProjective.grading (E.toProjective.coord 2)).hom (zChartY E)

/-- The affine section `Y/Z` has generic value `y`. -/
theorem projFunctionFieldEquiv_sectionYOverZ (E : WeierstrassCurve ℚ) :
    projFunctionFieldEquiv E
        ((Proj E.toProjective.grading).germToFunctionField _ (sectionYOverZ E)) =
      E.toAffine.genericY := by
  rw [projFunctionFieldEquiv_germ]
  have key := atPrimeEquivFunctionField_mapId_awayMk (genericPoint_proj_ideal E)
    (E.toProjective.coord_mem_grading 2) (Submonoid.powers_le.mpr (Ideal.mem_primeCompl_iff.mpr
      ((Proj.mem_basicOpen _ _ _).mp
        (genericPoint_mem E (Proj.basicOpen _ (E.toProjective.coord 2)))))) 1
    (E.toProjective.coord 1) (coord_mem_grading_smul E 1)
  exact key.trans (by rw [dehomogenization_coord, dehomogenization_coord]; simp)

private theorem coordinate_germ {N : ℕ} [NeZero N] (X : X0Model N) {Y : Scheme.{0}}
    [IsIntegral Y] (π : X.X ⟶ Y) (q : Y ⟶ Spec (.of ℚ)) (hQ : π ≫ q = X.overQ)
    (ι : Y.functionField →+* modularFunctionField N)
    (hgen : letI := X.integral; X.X.fromSpecFunctionField ≫ π =
      Spec.map (CommRingCat.ofHom (X.functionField.symm.toRingHom.comp ι)) ≫
        Y.fromSpecFunctionField)
    (V : Y.Opens) [Nonempty V] (a : Γ(Y, V))
    (τ : UpperHalfPlane) (hτ : ((X.complexPoint τ).comp π hQ).val default ∈ V)
    {g : ℂ → ℂ} (hg : MeromorphicOn g {z : ℂ | 0 < z.im}) (T : ℝ)
    (hseries : ∀ σ : UpperHalfPlane, T < σ.im →
      HasSum (fun n : ℤ =>
        (((ι (Y.germToFunctionField V a) : LaurentSeries ℚ).coeff n : ℚ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (σ : ℂ))) (g σ)) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (τ : ℂ) ∧
      ((X.complexPoint τ).comp π hQ).evalSection V hτ a = G τ ∧
        G =ᶠ[𝓝[≠] (τ : ℂ)] g := by
  let := X.integral
  have hx : (X.complexPoint τ).val default ∈ π ⁻¹ᵁ V := hτ
  have : Nonempty (π ⁻¹ᵁ V) := ⟨⟨_, hx⟩⟩
  have he : X.functionField (X.X.germToFunctionField (π ⁻¹ᵁ V) (π.app V a)) =
      ι (Y.germToFunctionField V a) := by
    rw [germToFunctionField_pullback _ _ hgen, RingHom.comp_apply]
    exact X.functionField.apply_symm_apply _
  rw [evalSection_comp]
  exact section_meromorphic_germ X _ _ hg T (fun σ hσ => by rw [he]; exact hseries σ hσ) τ hx

/-- Given the specified rational function-field coordinates with their analytic
Laurent expansions at infinity, the extended morphism agrees with them as
meromorphic germs at every chart point landing on the affine chart. -/
theorem affine_germ_agreement_of_expansions {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [NeZero (newformLevel E)] (X : X0Model (newformLevel E))
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) (ι : E.toAffine.FunctionField →+* modularFunctionField (newformLevel E))
    (T : ℝ)
    (hX : ∀ τ : UpperHalfPlane, T < τ.im →
      HasSum (fun n : ℤ => (((ι E.toAffine.genericX : LaurentSeries ℚ).coeff n : ℚ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ))) (xCoordinate E f Lat κ τ))
    (hY : ∀ τ : UpperHalfPlane, T < τ.im →
      HasSum (fun n : ℤ => (((ι E.toAffine.genericY : LaurentSeries ℚ).coeff n : ℚ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ))) (yCoordinate E f Lat κ τ)) :
    ∃ (π : X.X ⟶ Proj E.toProjective.grading) (hQ : π ≫ projectiveOverQ E = X.overQ),
      IsDominant π ∧
        ∀ (τ : UpperHalfPlane) (hτ : ((X.complexPoint τ).comp π hQ).val default ∈
            Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)),
          ∃ Gx Gy : ℂ → ℂ, AnalyticAt ℂ Gx (τ : ℂ) ∧ AnalyticAt ℂ Gy (τ : ℂ) ∧
            ((X.complexPoint τ).comp π hQ).evalSection _ hτ (sectionXOverZ E) = Gx τ ∧
            ((X.complexPoint τ).comp π hQ).evalSection _ hτ (sectionYOverZ E) = Gy τ ∧
            Gx =ᶠ[𝓝[≠] (τ : ℂ)] xCoordinate E f Lat κ ∧
            Gy =ᶠ[𝓝[≠] (τ : ℂ)] yCoordinate E f Lat κ := by
  let := X.integral
  obtain ⟨π, hQ, hdom, hgen⟩ := morphism_of_functionField X ι
  refine ⟨π, hQ, hdom, fun τ hτ => ?_⟩
  obtain ⟨hmX, hmY⟩ := coordinates_meromorphic E f Lat κ
  let j := ι.comp (projFunctionFieldEquiv E).toRingHom
  have hJx : j ((Proj E.toProjective.grading).germToFunctionField _ (sectionXOverZ E)) =
      ι E.toAffine.genericX :=
    congrArg (fun k => ι k) (projFunctionFieldEquiv_sectionXOverZ E)
  have hJy : j ((Proj E.toProjective.grading).germToFunctionField _ (sectionYOverZ E)) =
      ι E.toAffine.genericY :=
    congrArg (fun k => ι k) (projFunctionFieldEquiv_sectionYOverZ E)
  obtain ⟨Gx, hax, hvalx, hex⟩ := coordinate_germ X π (projectiveOverQ E) hQ j hgen
    _ (sectionXOverZ E) τ hτ hmX T (by
      intro σ hσ
      rw [hJx]
      exact hX σ hσ)
  obtain ⟨Gy, hay, hvaly, hey⟩ := coordinate_germ X π (projectiveOverQ E) hQ j hgen
    _ (sectionYOverZ E) τ hτ hmY T (by
      intro σ hσ
      rw [hJy]
      exact hY σ hσ)
  exact ⟨Gx, Gy, hax, hay, hvalx, hvaly, hex, hey⟩


end ZInQ.Manuscript.RC.ParamAtScale
