import ZInQKernel.Contrib.OneProof.WeberField

noncomputable section

set_option linter.unusedSectionVars false

namespace AfTateOr

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open scoped TensorProduct

/-! ## 1. Diamond–Shurman's `X₁(N)_alg`: function field `ℚ(j, f₁)` -/

/-- `ℤ[J][T] → ℚ[J][T]`. -/
def toQ : Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial ℚ) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℚ))

/-- `F(a, b)` for `F ∈ ℤ[J][T]`, in any commutative ring. -/
def ev2 {K : Type*} [CommRing K] (F : Polynomial (Polynomial ℤ)) (a b : K) : K :=
  (F.map (Polynomial.eval₂RingHom (Int.castRingHom K) a)).eval b

/-- **Diamond–Shurman's `X₁(N)_alg`, as far as the kernel can state it.** `X` is a smooth proper
geometrically connected integral curve over `ℚ` (`IsCurve`) whose function field is `ℚ(j, f₁)`:
it is generated, as a field, by two elements `j_X`, `t_X` whose polynomial relations with integer
coefficients are exactly those of `(j(τ), f₁(τ))` on `ℍ`, where `f₁(τ) = T5Glue.weber ⟨1, τ⟩ (1/N)`
`= g₂(τ)g₃(τ)℘_τ(1/N)/Δ(τ)` (at the points with `g₂(τ)g₃(τ) ≠ 0`, Weber's generic branch). -/
def IsX1AlgDS (N : ℕ) (X : Over SpecQ) : Prop :=
  IsCurve X ∧ ∃ (_ : IsIntegral X.left) (jX tX : X.left.functionField),
    Subfield.closure {jX, tX} = ⊤ ∧
    ∀ F : Polynomial (Polynomial ℤ), ev2 F jX tX = 0 ↔
      ∀ τ : UpperHalfPlane, (T5Glue.pp τ).g₂ ≠ 0 → (T5Glue.pp τ).g₃ ≠ 0 →
        X1Igusa.Weber.evAn N (toQ F) τ = 0

/-! ## 2. The conclusion: characteristic polynomial, or "satisfies" with oddness -/

/-- The conclusion of the leaf at one abelian variety `J`. -/
def AfTateOrAt (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ) : Prop :=
  ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
    AlgebraicGeometry.Surjective π.hom.left ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      ∃ b : (letI := R16Used.tensorModule ℓ A θ;
          Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ)),
        (∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
            (R16Used.frobMat ℓ A θ b σ).charpoly =
              R16Used.esPoly ℓ (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f)
                (c * (p : coeffField f))) ∨
        ((∀ (emb : coeffField f →+* PadicAlgCl ℓ) (c : GQ), ZInQ.Contrib.G9.PkgI4.IsComplexConj c →
          LinearMap.det (frobOn ℓ A θ emb c) = -1) ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
            Polynomial.aeval (R16Used.frobMat ℓ A θ b σ)
              (R16Used.esPoly ℓ (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f)
                (c * (p : coeffField f))) = 0)

/-- **LEAF.** -/
def AfTateDSOr : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ X : Over SpecQ, IsX1AlgDS N X →
      ∀ (V : AbelianVariety ℚ) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
        PicardTensorCompatible X.hom V.group rep → AfTateOrAt N χ f (R16IsJ1Dict.ofVendored V)

/-! ## 3. From the disjunction to the weak-odd form -/

theorem weakOddAt_of_orAt {N : ℕ} {χ : DirichletCharacter ℂ N} {f : CF N 2} {J : AbVar ℚ}
    (hT : TateModuleFree) (hN : 0 < N) (hf : IsNewform f χ) (h : AfTateOrAt N χ f J) :
    R16IsJ1Dict.AfTateWeakOddAt N χ f J := by
  obtain ⟨A, π, θ, hπ, hb⟩ := h
  refine ⟨A, π, θ, hπ, fun ℓ _ => ?_⟩
  obtain ⟨b, hcp | ⟨hodd, hweak⟩⟩ := hb ℓ
  · refine ⟨b, fun emb c hc => ?_, fun p hp hpN σ hσ => ?_⟩
    · rw [(R16IsJ1Dict.trace_det_frobOn ℓ A θ b emb c).2]
      exact R16IsJ1Dict.odd_of_charpoly ℓ A hT (coeffField f) θ b emb N hN χ
        (fun p => ⟨PkgI4.coeff f p, coeff_mem_coeffField f p⟩)
        (R16IsJ1Dict.chi_neg_one_of_newform hf) hcp c hc
    · obtain ⟨c, hc, hch⟩ := hcp p hp hpN σ hσ
      exact ⟨c, hc, by rw [← hch]; exact Matrix.aeval_self_charpoly _⟩
  · exact ⟨b, hodd, hweak⟩

/-- The charpoly form gives the disjunction (or-introduction). -/
theorem orAt_of_afTateAt {N : ℕ} {χ : DirichletCharacter ℂ N} {f : CF N 2} {J : AbVar ℚ}
    (h : R16IsJ1Dict.AfTateAt N χ f J) : AfTateOrAt N χ f J := by
  obtain ⟨A, π, θ, hπ, hb⟩ := h
  exact ⟨A, π, θ, hπ, fun ℓ _ => by obtain ⟨b, hcp⟩ := hb ℓ; exact ⟨b, Or.inl hcp⟩⟩

/-- The weak-odd form gives the disjunction (or-introduction). -/
theorem orAt_of_weakOddAt {N : ℕ} {χ : DirichletCharacter ℂ N} {f : CF N 2} {J : AbVar ℚ}
    (h : R16IsJ1Dict.AfTateWeakOddAt N χ f J) : AfTateOrAt N χ f J := by
  obtain ⟨A, π, θ, hπ, hb⟩ := h
  exact ⟨A, π, θ, hπ, fun ℓ _ => by
    obtain ⟨b, hodd, hw⟩ := hb ℓ; exact ⟨b, Or.inr ⟨hodd, hw⟩⟩⟩

/-! ## 4. The dictionary: a kernel model of `X₁(N)` is Diamond–Shurman's `X₁(N)_alg` -/

theorem map_ev2 {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L) (F : Polynomial (Polynomial ℤ))
    (a b : K) : φ (ev2 F a b) = ev2 F (φ a) (φ b) := by
  unfold ev2
  rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, Polynomial.map_map]
  congr 2
  refine Polynomial.ringHom_ext (fun n => ?_) ?_
  · simp
  · simp

open X1Igusa.Weber in
theorem evAlg_toQ (F : Polynomial (Polynomial ℤ)) (P : EjBar.toAffine.Point) :
    evAlg (toQ F) P = ev2 F (algebraMap Qj Kbar RatFunc.X) (wOf P) := by
  unfold evAlg ev2 toQ
  rw [Polynomial.coe_mapRingHom, Polynomial.map_map]
  congr 2
  refine Polynomial.ringHom_ext (fun n => ?_) ?_
  · simp
  · simp [RatFunc.algebraMap_X]

open X1Igusa.Weber in
/-- `ℚ(j)(w(P))` is generated as a field by `j` and `w(P)`. -/
theorem closure_eq_top (P : EjBar.toAffine.Point) (hw : wOf P ∈ fieldX1 P) :
    Subfield.closure ({algebraMap Qj (fieldX1 P) RatFunc.X, ⟨wOf P, hw⟩} : Set (fieldX1 P)) = ⊤ := by
  set S := Subfield.closure ({algebraMap Qj (fieldX1 P) RatFunc.X, ⟨wOf P, hw⟩} : Set (fieldX1 P))
  let U : Subfield Kbar := S.map (fieldX1 P).val.toRingHom
  have hj : algebraMap Qj Kbar RatFunc.X ∈ U :=
    Subfield.mem_map.mpr ⟨algebraMap Qj (fieldX1 P) RatFunc.X, Subfield.subset_closure (by simp), rfl⟩
  have hwU : wOf P ∈ U :=
    Subfield.mem_map.mpr ⟨⟨wOf P, hw⟩, Subfield.subset_closure (by simp), rfl⟩
  have hpol : ∀ p : Polynomial ℚ, algebraMap Qj Kbar (algebraMap (Polynomial ℚ) Qj p) ∈ U := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow,
        RatFunc.algebraMap_X]
      refine mul_mem ?_ (pow_mem hj n)
      have : algebraMap Qj Kbar (algebraMap (Polynomial ℚ) Qj (Polynomial.C c)) = (c : Kbar) :=
        eq_ratCast ((algebraMap Qj Kbar).comp ((algebraMap (Polynomial ℚ) Qj).comp Polynomial.C)) c
      rw [this]
      exact SubfieldClass.ratCast_mem U c
  have hq : ∀ q : Qj, algebraMap Qj Kbar q ∈ U := by
    intro q
    induction q using RatFunc.induction_on with
    | f p r hr => rw [map_div₀]; exact div_mem (hpol p) (hpol r)
  let U' : IntermediateField Qj Kbar := Subfield.toIntermediateField U hq
  have hle : fieldX1 P ≤ U' := by
    rw [← adjoin_wOf, IntermediateField.adjoin_simple_le_iff]
    exact hwU
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := Subfield.mem_map.mp (hle x.2)
  have : y = x := Subtype.ext hyx
  rwa [← this]

open X1Igusa.Weber in
/-- **The dictionary (glue, proved).** For `N ≥ 2`, a kernel model of `X₁(N)` (`IsX1Model`) is a
model of Diamond–Shurman's `X₁(N)_alg` (`IsX1AlgDS`): weber-field's comparison, `ℚ(j)(w(P)) =
ℚ(j)(x(P))`, and Igusa (`X1PointsConjugate`) to move from the model's point to weber-field's. -/
theorem isX1AlgDS_of_isX1Model (hI : R16IsJ1Dict.X1PointsConjugate) {N : ℕ} (hN : 2 ≤ N)
    {X : Over SpecQ} (h : IsX1Model N X) : IsX1AlgDS N X := by
  obtain ⟨hC, hInt, P', hP', ⟨e⟩⟩ := h
  obtain ⟨P, hP, hrel⟩ := weberFieldComparison N hN
  obtain ⟨σ, hσ⟩ := hI N P' P (by omega) hP' hP
  let e' : X.left.functionField ≃+* fieldX1 P := e.trans (R16IsJ1Dict.fieldX1Equiv σ hσ)
  have hw : wOf P ∈ fieldX1 P := by
    rw [← adjoin_wOf]; exact IntermediateField.mem_adjoin_simple_self _ _
  refine ⟨hC, hInt, e'.symm (algebraMap Qj (fieldX1 P) RatFunc.X), e'.symm ⟨wOf P, hw⟩, ?_,
    fun F => ?_⟩
  · set S := Subfield.closure ({e'.symm (algebraMap Qj (fieldX1 P) RatFunc.X), e'.symm ⟨wOf P, hw⟩} :
      Set X.left.functionField)
    have hle : Subfield.closure ({algebraMap Qj (fieldX1 P) RatFunc.X, ⟨wOf P, hw⟩} :
        Set (fieldX1 P)) ≤ S.map e'.toRingHom := by
      rw [Subfield.closure_le]
      rintro x (rfl | rfl)
      · exact Subfield.mem_map.mpr ⟨e'.symm (algebraMap Qj (fieldX1 P) RatFunc.X),
          Subfield.subset_closure (by simp), by simp⟩
      · exact Subfield.mem_map.mpr ⟨e'.symm ⟨wOf P, hw⟩, Subfield.subset_closure (by simp), by simp⟩
    rw [closure_eq_top P hw] at hle
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ := Subfield.mem_map.mp (hle (Subfield.mem_top (e' x)))
    rwa [← e'.injective hyx]
  · rw [hrel (toQ F), evAlg_toQ]
    have h1 := map_ev2 e'.symm.toRingHom F (algebraMap Qj (fieldX1 P) RatFunc.X) ⟨wOf P, hw⟩
    have h2 := map_ev2 (fieldX1 P).val.toRingHom F (algebraMap Qj (fieldX1 P) RatFunc.X) ⟨wOf P, hw⟩
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h1
    change e'.symm _ = _ at h1
    rw [← h1, map_eq_zero_iff _ e'.symm.injective]
    change _ = ev2 F (algebraMap Qj Kbar RatFunc.X) (wOf P) at h2
    rw [← h2]
    exact (map_eq_zero_iff _ (fieldX1 P).val.toRingHom.injective).symm

end AfTateOr
