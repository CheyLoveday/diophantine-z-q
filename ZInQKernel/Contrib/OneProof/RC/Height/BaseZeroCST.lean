import ZInQKernel.Contrib.OneProof.RC.Height.Torsion
import ZInQKernel.Contrib.CloudB3RC53.Prints.CST
import ZInQKernel.Contrib.CloudB3RC53.Basic

/-!
# Lane RC19 (height): the conductor-one height formula makes the specified point torsion

Lemma `ex:arith-base-zero` of the 11/5 manuscript (`diophantine_zq.tex`, lines 4330–4376), proof,
lines 4345–4346: "The conductor-one height formula makes the specified point torsion when
`L'(E/K,1) = 0`." Lane RC15 (`RC/Central/Nodes.lean`, `baseZero_node`) takes this step as the
hypothesis

  `hheight : CSTThm11 → ProductOrderGeTwo E k → IsOfFinAddOrder P`

and leaves its derivation from the project's statement of Cai–Shu–Tian, Theorem 1.1
(`ZInQ.Contrib.CloudB3RC53.CST.CSTThm11Split`) open: it needs the factorization
`L(E/K,s) = L(E,s)L(E^{(k)},s)` of the character-one `twistedLFunction`, `ĥ = 0 ⇔ torsion`, and the
conductor-one Heegner hypotheses. This file proves `hheight` from:

* `CSTThm11Split` (PRINT: L. Cai, J. Shu, Y. Tian, *Explicit Gross–Zagier and Waldspurger
  formulae*, Algebra & Number Theory 8 (2014) 2523–2572, Theorem 1.1, pp. 2524–2525; stated in the
  blueprint; read as Theorem 1.1, p. 2, of arXiv:1408.1733v2 in lane RV1, journal pages unchecked)
  at conductor `c = 1` and trivial character `χ = 1` (which is
  primitive of conductor one);
* the conductor-one Heegner data (`K` imaginary quadratic, `D ∉ {−3, −4}`, every prime of the
  level split, a Heegner form `[A, B, C]` of discriminant `D`, a point `y ∈ E(H₁)` with
  `ι(y) = φ(τ)`), as in the print's hypotheses; "the specified point" `P ∈ E(K)` is the trace
  `P_{H₁} = Σ_{σ ∈ Gal(H₁/K)} σ y` of the Heegner point (tex 4345: "the specified point");
* `LFactorizationConductorOne` (GLUE, the factorization `L(E/K, s) = L(E, s) L(E^{(k)}, s)` of the
  character-one `twistedLFunction`, with `K = ℚ(√k)`; tex 5736 reads it as the definition of
  the left side); this is not a height fact and is kept as an explicit hypothesis;
* `ĥ = 0 ⇔ torsion` over the number field `H₁` (PROVED, `Torsion.lean`).

Every theorem in this file is PROVED; `LFactorizationConductorOne` is a definition (the GLUE
statement).

* `deriv_eq_zero_of_two_le_analyticOrderAt`: an entire function vanishing to order `≥ 2` at `1`
  has `F'(1) = 0`.
* `heightK_one_eq`: at trivial character, `ĥ_K(P_χ) = [H : K]⁻¹ ĥ_H(Σ_σ σ y)`.
* `hheight_of_CST`: **RC15's `hheight`**, from the print, the Heegner data and the GLUE
  factorization.
-/

noncomputable section

open Height NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Complex

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST

/-- **The conductor-one `L`-factorization** (GLUE; tex 5736): the character-one twisted
`L`-function of `E/K` (Euler product over the primes of `K` of Mathlib's local factors of `E/K`) is
`L(E, s) L(E^{(k)}, s)` on `Re s > 3/2`, for `K = ℚ(√k)`. -/
def LFactorizationConductorOne (E : WeierstrassCurve ℚ) (K : Type) [Field K] [NumberField K]
    (k : ℚ) : Prop :=
  ∀ s : ℂ, 3 / 2 < s.re →
    LSeries (twistedLFunction E (chiAt (conductorOrder K 1) 1)) s =
      E.LSeries s * (qtwist E k).LSeries s

/-- An entire function vanishing to order at least two at `1` has vanishing derivative there.
PROVED. -/
theorem deriv_eq_zero_of_two_le_analyticOrderAt {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h2 : 2 ≤ analyticOrderAt F 1) : deriv F 1 = 0 := by
  have := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 2)
    (hF.analyticAt 1)).mp (by exact_mod_cast h2) 1 (by norm_num)
  rwa [iteratedDeriv_one] at this

/-- The trivial ring class character is primitive of conductor one (the condition is vacuous).
PROVED. -/
theorem isPrimitiveRingClassChar_one (K : Type) [Field K] [NumberField K] :
    IsPrimitiveRingClassChar K 1 1 := by
  intro c' _ hc' hne
  exact absurd (Nat.dvd_one.mp hc') hne

open Classical in
/-- **The height at trivial character** (`heightK`, CST statement): with `χ = 1` the hermitian form
`[H : K]⁻¹ Σ_{σ,σ'} χ(σ) conj χ(σ') ⟨σy, σ'y⟩_H` is `[H : K]⁻¹ ĥ_H(Σ_σ σ y)`, by bilinearity of the
Néron–Tate pairing. PROVED. -/
theorem heightK_one_eq (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K]
    [NumberField K] (c : ℕ) [NeZero c]
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point) :
    heightK E K c 1 y =
      (((Module.finrank K (ringClassField (conductorOrder K c)) : ℝ)⁻¹ : ℝ) : ℂ) *
        ((((∑ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
          Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y :
            (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)).canonicalHeight :
              ℝ) : ℂ) := by
  simp only [heightK, MonoidHom.one_apply, Units.val_one, map_one, one_mul]
  congr 1
  have hnt : ∀ P Q : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point,
      ntPairing E P Q =
        (E.baseChange (ringClassField (conductorOrder K c))).toAffine.neronTatePairing P Q := by
    intro P Q
    unfold ntPairing
    have hdec : Classical.decEq (ringClassField (conductorOrder K c)) =
        (inferInstance : DecidableEq (ringClassField (conductorOrder K c))) :=
      Subsingleton.elim _ _
    rw [hdec]
  simp only [hnt]
  rw [← neronTatePairing_self, LinearMap.map_sum₂, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [map_sum, Complex.ofReal_sum]

open Classical in
/-- **RC15's `hheight` from Cai–Shu–Tian at conductor one** (tex 4345–4346): if `L'(E/K, 1) = 0`
(`ProductOrderGeTwo E k`, with the GLUE factorization), the conductor-one height formula gives
`ĥ_K(P_χ) = 0` for the trivial character, so the trace `Σ_σ σ y ∈ E(H₁)` has height zero, hence is
torsion (`ĥ = 0 ⇔ torsion` over the number field `H₁`), and so is the specified point `P ∈ E(K)`,
whose base change to `H₁` is that trace (`hP`). PROVED. -/
theorem hheight_of_CST (E : WeierstrassCurve ℚ) [E.IsElliptic] (k : ℚ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hnCM : IsNonCMLattice Lat)
    (κ : ℂ) (hκ : IsParamScale (newformLevel E) f Lat κ)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (hKc : IsTotallyComplex K) (hD3 : discr K ≠ -3) (hD4 : discr K ≠ -4)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (A B C' : ℤ) (hH : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) A B C')
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)
    (hy : Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat κ (cmPoint A B (discr K * (1 : ℕ) ^ 2)))
    (P : (E.baseChange K).toAffine.Point)
    (hP : Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)
    (hL : LFactorizationConductorOne E K k) :
    CSTThm11Split → ProductOrderGeTwo E k → IsOfFinAddOrder P := by
  intro hCST hord
  obtain ⟨C, hC, hcst⟩ := hCST E f hf Lat hLat hnCM κ hκ
  obtain ⟨F, hFd, hFeq, hF2⟩ := hord
  have hF : ∀ s : ℂ, 3 / 2 < s.re →
      F s = LSeries (twistedLFunction E (chiAt (conductorOrder K 1) 1)) s := by
    intro s hs
    rw [hFeq s hs, hL s hs]
  have key := hcst K hK2 hKc hD3 hD4 hsplit 1 (Nat.coprime_one_left _) 1
    (isPrimitiveRingClassChar_one K) A B C' hH ι y hy F hFd hF
  rw [deriv_eq_zero_of_two_le_analyticOrderAt hFd hF2, heightK_one_eq] at key
  -- the constants are nonzero
  have hD : (discr K : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero K
  have hc : ((C / (((1 : ℕ) : ℝ) * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < C / (((1 : ℕ) : ℝ) * Real.sqrt |(discr K : ℝ)|) := by
      apply div_pos hC
      rw [Nat.cast_one, one_mul]
      exact Real.sqrt_pos.mpr (abs_pos.mpr hD)
    exact_mod_cast this.ne'
  have hdeg : (((Module.finrank K (ringClassField (conductorOrder K 1)) : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Module.finrank K (ringClassField (conductorOrder K 1)) := Module.finrank_pos
    exact_mod_cast (inv_pos.mpr (by exact_mod_cast this : (0 : ℝ) < _)).ne'
  have hT := ((mul_eq_zero.mp key.symm).resolve_left hc)
  have hT' := (mul_eq_zero.mp hT).resolve_left hdeg
  have hT0 : ((∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
      Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y :
        (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)).canonicalHeight =
          0 := by
    exact_mod_cast hT'
  have htor := isOfFinAddOrder_of_canonicalHeight_eq_zero'
    (E.baseChange (ringClassField (conductorOrder K 1))) hT0
  rw [← hP] at htor
  exact isOfFinAddOrder_of_map_isOfFinAddOrder _ (Point.map_injective _) htor

open Classical in
/-- **The height formula makes the trace nontorsion at a known simple zero** (tex 2464,
8268–8272): if some entire continuation `F` of `L(E, s) L(E^{(k)}, s)` has `F'(1) ≠ 0`,
then the specified point `P ∈ E(K)` (the trace of the conductor-one Heegner point) is not torsion.
PROVED. -/
theorem not_isOfFinAddOrder_of_CST (E : WeierstrassCurve ℚ) [E.IsElliptic] (k : ℚ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (hnCM : IsNonCMLattice Lat)
    (κ : ℂ) (hκ : IsParamScale (newformLevel E) f Lat κ)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (hKc : IsTotallyComplex K) (hD3 : discr K ≠ -3) (hD4 : discr K ≠ -4)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (A B C' : ℤ) (hH : IsHeegnerForm (newformLevel E) (discr K * (1 : ℕ) ^ 2) A B C')
    (ι : ringClassField (conductorOrder K 1) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)
    (hy : Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat κ (cmPoint A B (discr K * (1 : ℕ) ^ 2)))
    (P : (E.baseChange K).toAffine.Point)
    (hP : Point.baseChange K (ringClassField (conductorOrder K 1)) P =
      ∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)
    (hL : LFactorizationConductorOne E K k) (hCST : CSTThm11Split)
    (F : ℂ → ℂ) (hFd : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s * (qtwist E k).LSeries s)
    (hderiv : deriv F 1 ≠ 0) : ¬IsOfFinAddOrder P := by
  intro hPt
  obtain ⟨C, hC, hcst⟩ := hCST E f hf Lat hLat hnCM κ hκ
  have hF : ∀ s : ℂ, 3 / 2 < s.re →
      F s = LSeries (twistedLFunction E (chiAt (conductorOrder K 1) 1)) s := by
    intro s hs
    rw [hFeq s hs, hL s hs]
  have key := hcst K hK2 hKc hD3 hD4 hsplit 1 (Nat.coprime_one_left _) 1
    (isPrimitiveRingClassChar_one K) A B C' hH ι y hy F hFd hF
  rw [heightK_one_eq] at key
  have htor : IsOfFinAddOrder
      ((∑ σ : ringClassField (conductorOrder K 1) ≃ₐ[K] ringClassField (conductorOrder K 1),
        Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y :
          (E.baseChange (ringClassField (conductorOrder K 1))).toAffine.Point)) := by
    rw [← hP]
    exact (Point.baseChange K (ringClassField (conductorOrder K 1))).isOfFinAddOrder hPt
  rw [Point.canonicalHeight_eq_zero_of_isOfFinAddOrder htor] at key
  simp at key
  exact hderiv key

end ZInQ.Manuscript.RC.Height
