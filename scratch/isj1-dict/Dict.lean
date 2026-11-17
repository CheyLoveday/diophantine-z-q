import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.OneProof.R16Used

/-! # isj1-dict, part 1: the `IsJ1` dictionary behind `AfTateCharPoly` -/

noncomputable section

namespace ISJ1Dict

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open scoped TensorProduct

/-! ## 1. Isomorphic abelian varieties -/

/-- `J` and `J'` are isomorphic abelian varieties over `K`: an isomorphism of `K`-schemes which is
a homomorphism. -/
def AbVarIso {K : Type} [Field K] (J J' : AbVar K) : Prop :=
  ∃ e : J.X ≅ J'.X, IsMonHom e.hom

theorem AbVarIso.symm {K : Type} [Field K] {J J' : AbVar K} (h : AbVarIso J J') : AbVarIso J' J := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, by change IsMonHom e.inv; infer_instance⟩

theorem AbVarIso.trans {K : Type} [Field K] {J J' J'' : AbVar K} (h : AbVarIso J J')
    (h' : AbVarIso J' J'') : AbVarIso J J'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e ≪≫ e', by change IsMonHom (e.hom ≫ e'.hom); infer_instance⟩

/-! ## 2. The body of `AfTateCharPoly` at one Jacobian, and its transport -/

/-- The conclusion of `R16Used.AfTateCharPoly` for one abelian variety `J` (verbatim). -/
def AfTateAt (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ) : Prop :=
  ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
    AlgebraicGeometry.Surjective π.hom.left ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      ∃ b : (letI := R16Used.tensorModule ℓ A θ;
          Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ)),
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
            (R16Used.frobMat ℓ A θ b σ).charpoly =
              R16Used.esPoly ℓ (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f)
                (c * (p : coeffField f))

theorem afTateCharPoly_iff : R16Used.AfTateCharPoly ↔
    ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
      0 < N → IsNewform f χ → IsJ1 N J → AfTateAt N χ f J := Iff.rfl

/-- **Transport (glue).** The body only depends on `J` up to isomorphism: compose `π` with the
inverse isomorphism. -/
theorem AfTateAt.of_iso {N : ℕ} {χ : DirichletCharacter ℂ N} {f : CF N 2} {J J' : AbVar ℚ}
    (h : AfTateAt N χ f J) (e : AbVarIso J J') : AfTateAt N χ f J' := by
  obtain ⟨A, π, θ, hπ, hrest⟩ := h
  obtain ⟨e, he⟩ := e
  refine ⟨A, Hom.mk' (e.inv ≫ π.hom), θ, ?_, hrest⟩
  rw [Hom.hom_mk', Over.comp_left]
  have : AlgebraicGeometry.Surjective π.hom.left := hπ
  infer_instance


/-! ## 3. `Pic⁰` is the Albanese: every Jacobian in the kernel's sense is the degree-zero Picard
scheme (vendored Jacobian-Challenge library) -/

/-- A vendored abelian variety (commutative group scheme, smooth, proper, geometrically
irreducible) as a kernel `AbVar`. -/
def ofVendored {K : Type} [Field K] (V : AbelianVariety K) : AbVar K :=
  haveI : GeometricallyIntegral V.group.X.hom := Smooth.geometricallyIntegral V.group.X.hom
  { X := V.group.X
    grp := V.group.grp
    proper := V.proper
    smooth := V.smooth
    geomInt := inferInstance }

@[simp] theorem ofVendored_X {K : Type} [Field K] (V : AbelianVariety K) :
    (ofVendored V).X = V.group.X := rfl

/-- **The Abel–Jacobi map into `Pic⁰` is a Jacobian in the kernel's sense (glue, from the
vendored library).** For a curve `X` over `K` (`IsCurve`), a representation `rep` of the
degree-zero Picard functor `Pic⁰_{X/K}` by an abelian variety `V` whose group law is the tensor
product of line bundles, and any `K`-point `P₀`, the Abel–Jacobi map `X → V` based at `P₀` has
the Albanese property `IsJacobian`. -/
theorem isJacobian_picZero {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K)))
    (hX : IsCurve X) (V : AbelianVariety K)
    (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X)
    (htc : PicardTensorCompatible X.hom V.group rep)
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) :
    ∃ aj : X ⟶ (ofVendored V).X, IsJacobian X P₀ (ofVendored V) aj := by
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  have : GeometricallyIrreducible X.hom := inferInstance
  let aj : X ⟶ V.group.X :=
    Curve.abelJacobiMap (⟨X⟩ : Curve K) P₀.left (by simp) rep
  have alb : IsAlbanese P₀ V aj := Curve.isAlbanese_abelJacobiMap ⟨X⟩ P₀ V rep htc
  refine ⟨aj, ⟨alb.1, ?_⟩⟩
  intro A f hf
  obtain ⟨g, hg, huniq⟩ := alb.existsUnique_schemeMap f hf
  have pointed : η[V.group.X] ≫ g = η[A.X] := by
    rw [← alb.1, Category.assoc, ← hg, hf]
  have : GeometricallyIntegral V.group.X.hom := Smooth.geometricallyIntegral V.group.X.hom
  have hmon : IsMonHom g := isMonHom_of_isProper_of_geometricallyIntegral g pointed
  exact ⟨g, ⟨hmon, hg.symm⟩, fun φ hφ => huniq φ hφ.2.symm⟩

/-- **Every kernel Jacobian is `Pic⁰` (glue).** If `(J, aj)` is a Jacobian of `(X, P₀)` in the
kernel's sense (`IsJacobian`, the Albanese property), then `J` is isomorphic, as an abelian
variety, to every tensor-compatible representing object of `Pic⁰_{X/K}`. -/
theorem abVarIso_picZero_of_isJacobian {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    (hX : IsCurve X) {P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X} {J : AbVar K}
    {aj : X ⟶ J.X} (h : IsJacobian X P₀ J aj) (V : AbelianVariety K)
    (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X)
    (htc : PicardTensorCompatible X.hom V.group rep) : AbVarIso J (ofVendored V) := by
  obtain ⟨aj', h'⟩ := isJacobian_picZero X hX V rep htc P₀
  obtain ⟨e, he, -, -⟩ := h.unique h'
  exact ⟨e, he⟩

/-- `Pic⁰_{X/K}` of a curve is represented by a tensor-compatible abelian variety (vendored
`exists_abelianVariety_picardDegreeZero`). -/
theorem exists_picZero {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) (hX : IsCurve X) :
    ∃ (V : AbelianVariety K) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
      PicardTensorCompatible X.hom V.group rep := by
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  let : X.left.Over (Spec (.of K)) := ⟨X.hom⟩
  have : SmoothOfRelativeDimension 1 (X.left ↘ Spec (.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ Spec (.of K)) := inferInstanceAs (IsProper X.hom)
  have : GeometricallyIntegral (X.left ↘ Spec (.of K)) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  obtain ⟨V, rep, htc, -⟩ := exists_abelianVariety_picardDegreeZero (baseField := K) X.left
  exact ⟨V, rep, htc⟩

/-- **Base-point independence (glue).** Two Jacobians of the same curve, for any two base points,
are isomorphic abelian varieties (both are `Pic⁰_{X/K}`). -/
theorem abVarIso_of_isJacobian {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    (hX : IsCurve X) {P₀ P₁ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X} {J J' : AbVar K}
    {aj : X ⟶ J.X} {aj' : X ⟶ J'.X} (h : IsJacobian X P₀ J aj) (h' : IsJacobian X P₁ J' aj') :
    AbVarIso J J' := by
  obtain ⟨V, rep, htc⟩ := exists_picZero X hX
  exact (abVarIso_picZero_of_isJacobian hX h V rep htc).trans
    (abVarIso_picZero_of_isJacobian hX h' V rep htc).symm

/-- **Transport of a Jacobian along an isomorphism of curves (glue).** -/
theorem IsJacobian.of_iso {K : Type} [Field K] {X X' : Over (Spec (CommRingCat.of K))}
    (e : X ≅ X') {P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X'} {J : AbVar K} {aj : X' ⟶ J.X}
    (h : IsJacobian X' P₀ J aj) : IsJacobian X (P₀ ≫ e.inv) J (e.hom ≫ aj) := by
  refine ⟨by rw [Category.assoc, e.inv_hom_id_assoc, h.base], ?_⟩
  intro A f hf
  obtain ⟨φ, ⟨hφ, hφf⟩, hu⟩ := h.univ A (e.inv ≫ f) (by rw [← Category.assoc, hf])
  refine ⟨φ, ⟨hφ, by rw [Category.assoc, hφf, e.hom_inv_id_assoc]⟩, ?_⟩
  rintro ψ ⟨hψ, hψf⟩
  refine hu ψ ⟨hψ, ?_⟩
  rw [← hψf, Category.assoc, e.inv_hom_id_assoc]

/-! ## 4. Uniqueness of `J₁(N)` from two printed leaves -/

/-- **LEAF (Igusa; the Galois group of the `N`-division field of the generic elliptic curve is
transitive on the `x`-coordinates of points of exact order `N`).** For `N ≥ 1` and points `P, P'`
of exact order `N` of `E_j` over `\overline{ℚ(j)}`, some `σ ∈ Aut(\overline{ℚ(j)}/ℚ(j))` maps
`x(P)` to `x(P')`. -/
def X1PointsConjugate : Prop :=
  ∀ (N : ℕ) (P P' : EjBar.toAffine.Point), 0 < N → addOrderOf P = N → addOrderOf P' = N →
    ∃ σ : Kbar ≃ₐ[Qj] Kbar, σ (xCoord P) = xCoord P'

/-- **LEAF (a smooth proper curve is determined by its function field).** Two integral smooth
proper geometrically connected curves over `ℚ` with isomorphic function fields are isomorphic
over `ℚ`. -/
def CurveIsoOfFunctionFieldIso : Prop :=
  ∀ (X X' : Over SpecQ) [IsIntegral X.left] [IsIntegral X'.left], IsCurve X → IsCurve X' →
    Nonempty (X.left.functionField ≃+* X'.left.functionField) → Nonempty (X ≅ X')

/-- `K_N` does not depend on the point (glue): a `ℚ(j)`-automorphism carrying `x(P)` to `x(P')`
carries `ℚ(j)(x(P))` onto `ℚ(j)(x(P'))`. -/
def fieldX1Equiv {P P' : EjBar.toAffine.Point} (σ : Kbar ≃ₐ[Qj] Kbar)
    (hσ : σ (xCoord P) = xCoord P') : fieldX1 P ≃+* fieldX1 P' :=
  ((IntermediateField.equivMap (fieldX1 P) (σ : Kbar →ₐ[Qj] Kbar)).trans
    (IntermediateField.equivOfEq (by
      rw [fieldX1, fieldX1, IntermediateField.adjoin_map, Set.image_singleton]
      exact congrArg (fun x => IntermediateField.adjoin Qj {x}) hσ))).toRingEquiv

/-- **Uniqueness of `J₁(N)` (glue, from the two leaves).** Any two abelian varieties satisfying
`IsJ1 N` (`N ≥ 1`) are isomorphic. -/
theorem abVarIso_of_isJ1 (hI : X1PointsConjugate) (hC : CurveIsoOfFunctionFieldIso) {N : ℕ}
    (hN : 0 < N) {J J' : AbVar ℚ} (h : IsJ1 N J) (h' : IsJ1 N J') : AbVarIso J J' := by
  obtain ⟨X, P₀, aj, ⟨hXc, hXi, P, hP, ⟨eX⟩⟩, hJ⟩ := h
  obtain ⟨X', P₀', aj', ⟨hXc', hXi', P', hP', ⟨eX'⟩⟩, hJ'⟩ := h'
  obtain ⟨σ, hσ⟩ := hI N P P' hN hP hP'
  obtain ⟨e⟩ := @hC X X' hXi hXi' hXc hXc' ⟨(eX.trans (fieldX1Equiv σ hσ)).trans eX'.symm⟩
  exact abVarIso_of_isJacobian hXc hJ (IsJacobian.of_iso e hJ')

/-! ## 5. The leaf restated over one Jacobian, and over `Pic⁰` -/

/-- `AfTateCharPoly`, existence form over one Jacobian of one model. -/
def AfTateCharPolyJ1Exists : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N → IsNewform f χ →
    ∃ J : AbVar ℚ, IsJ1 N J ∧ AfTateAt N χ f J

/-- **`AfTateCharPoly` from its form over one Jacobian (glue).** -/
theorem afTateCharPoly_of_exists (h : AfTateCharPolyJ1Exists) (hI : X1PointsConjugate)
    (hC : CurveIsoOfFunctionFieldIso) : R16Used.AfTateCharPoly := by
  intro N χ f J hN hf hJ
  obtain ⟨J₀, hJ₀, hA⟩ := h N χ f hN hf
  exact hA.of_iso (abVarIso_of_isJ1 hI hC hN hJ₀ hJ)

/-- **LEAF candidate: `AfTateCharPoly` over `Pic⁰` of one model of `X₁(N)`.** For `N ≥ 1` and a
newform `f ∈ S₂(Γ₁(N))` with nebentypus `χ` there is a model `X` of `X₁(N)` over `ℚ` (`IsX1Model`:
smooth proper geometrically connected integral, function field `ℚ(j)(x(P))`, `P` of exact order
`N`) such that the degree-zero Picard scheme `J₁(N) = Pic⁰_{X/ℚ}` (any representing abelian
variety with the tensor group law) satisfies the conclusion of `AfTateCharPoly`. -/
def AfTateCharPolyPicZero : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N → IsNewform f χ →
    ∃ X : Over SpecQ, IsX1Model N X ∧
      ∀ (V : AbelianVariety ℚ) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
        PicardTensorCompatible X.hom V.group rep → AfTateAt N χ f (ofVendored V)

/-- **`AfTateCharPoly` from its `Pic⁰` form (glue).** No rational point is assumed on the model:
it is transported from the one carried by `IsJ1`. -/
theorem afTateCharPoly_of_picZero (h : AfTateCharPolyPicZero) (hI : X1PointsConjugate)
    (hC : CurveIsoOfFunctionFieldIso) : R16Used.AfTateCharPoly := by
  intro N χ f J hN hf hJ
  obtain ⟨X₀, ⟨hXc₀, hXi₀, P₀', hP₀', ⟨eX₀⟩⟩, hA⟩ := h N χ f hN hf
  obtain ⟨X, P₀, aj, ⟨hXc, hXi, P, hP, ⟨eX⟩⟩, hJac⟩ := hJ
  obtain ⟨σ, hσ⟩ := hI N P₀' P hN hP₀' hP
  obtain ⟨e⟩ := @hC X₀ X hXi₀ hXi hXc₀ hXc ⟨(eX₀.trans (fieldX1Equiv σ hσ)).trans eX.symm⟩
  obtain ⟨V, rep, htc⟩ := exists_picZero X₀ hXc₀
  exact (hA V rep htc).of_iso
    (abVarIso_picZero_of_isJacobian hXc₀ (IsJacobian.of_iso e hJac) V rep htc).symm

/-- The `Pic⁰` form is a consequence of `AfTateCharPoly` and the existence of a model with a
rational point (so it is never stronger than the current leaf, given `X1ModelExists`-type input). -/
theorem afTateCharPolyPicZero_of_afTate (h : R16Used.AfTateCharPoly)
    (hx : ∀ N : ℕ, 0 < N → ∃ (X : Over SpecQ) (_ : RatPt X), IsX1Model N X) :
    AfTateCharPolyPicZero := by
  intro N χ f hN hf
  obtain ⟨X, P₀, hX⟩ := hx N hN
  refine ⟨X, hX, fun V rep htc => ?_⟩
  obtain ⟨aj, hJ⟩ := isJacobian_picZero X hX.1 V rep htc P₀
  exact h N χ f (ofVendored V) hN hf ⟨X, P₀, aj, hX, hJ⟩

end ISJ1Dict

#print axioms ISJ1Dict.afTateCharPoly_of_exists
#print axioms ISJ1Dict.afTateCharPoly_of_picZero
#print axioms ISJ1Dict.afTateCharPolyPicZero_of_afTate
#print axioms ISJ1Dict.abVarIso_of_isJ1
