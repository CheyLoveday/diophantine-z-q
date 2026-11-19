import ZInQKernel.Contrib.OneProof.RC.Wiring.SignedSelmer

/-!
# Theorem 5.3, Lane RC36: universal coefficients for `E_t` at a signed parameter

The RC53 group's universal-coefficient layer (`CentralUniversal/Arithmetic.lean`) is stated for
the curve `Ecurve ℓ`, `ℓ : ℕ`, over `K = ℚ(√k)`: the genuine compact Kummer complex `C_K` of
`(E_ℓ)_K`, its coefficient quotient `C_K ⊗ ℚ₂/ℤ₂`, the cocycle complex of the genuine full Selmer
group `Sel_{2^∞}(E_ℓ/K)`, and the two arithmetic inputs `KummerCohomologyFinite` (finite generation
of `H¹`, `H²`) and `KummerCoefficientComparison` (the truncated cochain comparison). This file
restates that layer for the family curve `E_t = curve t`, `t : ℚ` of either sign (the
ellipticity instance `[(curve t).IsElliptic]` is `t ≠ 0`, `curve_isElliptic_iff`), over the same
genuine objects, and reproves the parameter-independent algebra:

* the objects: `arithmeticCompactComplexSigned` (`C_K` for `(E_t)_K`, torsion-free terms),
  `arithmeticRationalComplexSigned`, `arithmeticCoefficientComplexSigned` (the cokernel of the
  canonical coefficient map), `discreteSelmerComplexSigned` (cocycles of `SelKSigned t k`, all
  zero-cochains retained) with `discreteSelmerHomologyEquivSigned : H¹ ≃ Sel_{2^∞}(E_t/K)`;
* the two inputs, restated: `KummerCohomologyFiniteSigned` and `KummerCoefficientComparisonSigned`
  (GLUE, exactly the RC53 group's comparison with `Ecurve ℓ` replaced by `curve t`);
* the universal-coefficient sequence `0 → (ℚ₂/ℤ₂)^r → Sel_{2^∞}(E_t/K) → H²(C_K)_tors → 0` in the
  integral free-part basis (one basis for both coordinates: `arithmetic_jSigned_on_tensor`,
  `arithmeticRationalH1EquivSigned_on_tensor`; `arithmetic_jSigned_injective`,
  `arithmetic_jSigned_exact`, `arithmetic_jSigned_cokernelEquiv`;
  `arithmetic_jSigned_boundedDefects` from finite generation of `H²`);
* rank = Selmer corank: `arithmeticRankSigned_eq_finrank_ratTate`
  (`rank_{ℤ₂} H¹(C_K)/tors = dim V₂ Sel_{2^∞}(E_t/K)`), and with the quadratic descent
  `arithmeticRankSigned_eq_add`, `arithmeticRankSigned_eq_one`;
* faithfulness: `KummerCoefficientComparisonSigned.ofNat`,
  `KummerCoefficientComparisonSigned.toNat` (inverse to each other, by `rfl`),
  `kummerCohomologyFiniteSigned_natCast_iff` (at `t = ℓ` the restated inputs are the originals) and
  `KummerCoefficientComparisonSigned.congrParam` (transport along an equality of parameters).

Every theorem below is PROVED; the comparison is a named input (GLUE), not constructed here.
-/

noncomputable section



namespace ZInQ.Manuscript.RC

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Manuscript.RC53Assist.CentralUniversal
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.BaseZeroLimit
open scoped TensorProduct

/-! **The discrete Selmer complex of `E_t` over `K`** -/

/-- **The cocycle complex of `Sel_{2^∞}(E_t/ℚ(√k))`** (the target of the coefficient comparison):
all zero-cochains, and in degree one the continuous cocycles representing classes of the genuine
full Selmer group, plus coboundaries (the RC53 group's `subgroupCocycleComplex`).
Kind: definition. -/
abbrev discreteSelmerComplexSigned (t : ℚ) (k : ℤ) : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  subgroupCocycleComplex (SelKSigned t k)

/-- Its first cohomology is the genuine `Sel_{2^∞}(E_t/ℚ(√k))`, through the cocycle-class map.
Kind: definition (PROVED equivalence). -/
def discreteSelmerHomologyEquivSigned (t : ℚ) (k : ℤ) :
    (discreteSelmerComplexSigned t k).homology 1 ≃+ SelKSigned t k :=
  subgroupCocycleHomologyEquiv (SelKSigned t k)

section Objects

variable (t : ℚ) (k : ℤ) [(curve t).IsElliptic]
  (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
  (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
    ((curve t).baseChange (QuadraticField k)) (2 ^ n))

/-- **The genuine compact Kummer complex `C_K` of `(E_t)_K`** (tex 4006–4018), `K = ℚ(√k)`, with
the Tate-module coefficients and the `2`-adic Kummer conditions at the places of `S`.
Kind: definition. -/
abbrev arithmeticCompactComplexSigned : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ :=
  compactKummerComplex S ((curve t).baseChange (QuadraticField k)) hFull

/-- Its genuine rational scalar extension `C_K ⊗ ℚ₂`. Kind: definition. -/
abbrev arithmeticRationalComplexSigned : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ :=
  rationalKummerComplex S ((curve t).baseChange (QuadraticField k)) hFull

/-- The terms of `C_K` are torsion-free (so the coefficient sequence is short exact).
Kind: PROVED. -/
instance arithmeticCompactTermSigned_isTorsionFree (n : ℤ) :
    Module.IsTorsionFree ℤ_[2] ((arithmeticCompactComplexSigned t k S hFull).X n) :=
  compactKummerTerm_isTorsionFree S _ hFull n

/-- **Input (finite generation)**: `H¹(C_K)` and `H²(C_K)` are finitely generated over `ℤ₂` (the
RC53 group's `KummerCohomologyFinite` for `curve t`; at an address it follows from the two Milne
finiteness prints, `centralCohomologyFinite`). Kind: definition (input). -/
structure KummerCohomologyFiniteSigned : Prop where
  finite_one : Module.Finite ℤ_[2] ((arithmeticCompactComplexSigned t k S hFull).homology 1)
  finite_two : Module.Finite ℤ_[2] ((arithmeticCompactComplexSigned t k S hFull).homology 2)

/-- **The coefficient quotient `C_K ⊗ ℚ₂/ℤ₂`**: the cokernel of the canonical coefficient map
`C_K → C_K ⊗ ℚ₂`. Kind: definition. -/
abbrev arithmeticCoefficientComplexSigned : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ :=
  coefficientQuotientComplex (arithmeticCompactComplexSigned t k S hFull)

/-- **Input (the coefficient and local-Kummer comparison; GLUE)**, the RC53 group's
`KummerCoefficientComparison` with `Ecurve ℓ` replaced by `curve t`: `S` is finite and a
quasi-isomorphism from the canonical truncation `τ_{≤1}` of the coefficient quotient (as a complex
of abelian groups) to the cocycle complex of `Sel_{2^∞}(E_t/ℚ(√k))`. Source and target are the
genuine fixed complexes; no corank, rank or dimension statement is included. This is the discrete
Selmer binding (the truncated cochain comparison) for the signed curve. Kind: definition (input). -/
structure KummerCoefficientComparisonSigned where
  finite_support : S.Finite
  comparison :
    (integerCoefficientComplex (arithmeticCoefficientComplexSigned t k S hFull)).truncLE 1 ⟶
      discreteSelmerComplexSigned t k
  quasiIso : QuasiIso comparison

end Objects

/-! **Faithfulness: the restated inputs at a natural parameter, and transport** -/

section Faithful

/-- **The original comparison is the signed one at `t = ℓ`** (the fields of the two structures agree
by unfolding `Ecurve ℓ = curve ℓ`). Kind: definition. -/
def KummerCoefficientComparisonSigned.ofNat {ℓ : ℕ} {k : ℤ} [(Ecurve ℓ).IsElliptic]
    {S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))}
    {hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
      ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n)}
    (I : KummerCoefficientComparison ℓ k S hFull) :
    KummerCoefficientComparisonSigned (ℓ : ℚ) k S hFull :=
  ⟨I.finite_support, I.comparison, I.quasiIso⟩

/-- **The signed comparison at `t = ℓ` is the original one.** Kind: definition. -/
def KummerCoefficientComparisonSigned.toNat {ℓ : ℕ} {k : ℤ} [(Ecurve ℓ).IsElliptic]
    {S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))}
    {hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
      ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n)}
    (I : KummerCoefficientComparisonSigned (ℓ : ℚ) k S hFull) :
    KummerCoefficientComparison ℓ k S hFull :=
  ⟨I.finite_support, I.comparison, I.quasiIso⟩

/-- `toNat` after `ofNat` is the identity. Kind: PROVED. -/
theorem KummerCoefficientComparisonSigned.toNat_ofNat {ℓ : ℕ} {k : ℤ} [(Ecurve ℓ).IsElliptic]
    {S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))}
    {hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
      ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n)}
    (I : KummerCoefficientComparison ℓ k S hFull) :
    (KummerCoefficientComparisonSigned.ofNat I).toNat = I :=
  rfl

/-- `ofNat` after `toNat` is the identity. Kind: PROVED. -/
theorem KummerCoefficientComparisonSigned.ofNat_toNat {ℓ : ℕ} {k : ℤ} [(Ecurve ℓ).IsElliptic]
    {S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))}
    {hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
      ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n)}
    (I : KummerCoefficientComparisonSigned (ℓ : ℚ) k S hFull) :
    KummerCoefficientComparisonSigned.ofNat I.toNat = I :=
  rfl

/-- At `t = ℓ` a signed comparison exists exactly when an original one does (`toNat`, `ofNat`).
Kind: PROVED. -/
theorem kummerCoefficientComparisonSigned_natCast_nonempty_iff {ℓ : ℕ} {k : ℤ}
    [(Ecurve ℓ).IsElliptic] {S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))}
    {hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
      ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n)} :
    Nonempty (KummerCoefficientComparisonSigned (ℓ : ℚ) k S hFull) ↔
      Nonempty (KummerCoefficientComparison ℓ k S hFull) :=
  ⟨fun ⟨I⟩ => ⟨I.toNat⟩, fun ⟨I⟩ => ⟨KummerCoefficientComparisonSigned.ofNat I⟩⟩

/-- At `t = ℓ` the signed finite-generation input is the original one. Kind: PROVED. -/
theorem kummerCohomologyFiniteSigned_natCast_iff {ℓ : ℕ} {k : ℤ} [(Ecurve ℓ).IsElliptic]
    {S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))}
    {hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
      ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n)} :
    KummerCohomologyFiniteSigned (ℓ : ℚ) k S hFull ↔ KummerCohomologyFinite ℓ k S hFull :=
  ⟨fun F => ⟨F.finite_one, F.finite_two⟩, fun F => ⟨F.finite_one, F.finite_two⟩⟩

/-- **Transport of the comparison along an equality of parameters** `t = t'` (the instance and the
full-torsion witnesses are propositions). Kind: definition. -/
def KummerCoefficientComparisonSigned.congrParam {t t' : ℚ} (htt : t = t') {k : ℤ}
    [(curve t).IsElliptic] [(curve t').IsElliptic]
    {S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))}
    {hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
      ((curve t).baseChange (QuadraticField k)) (2 ^ n)}
    {hFull' : ∀ n : ℕ, FullTorsion (QuadraticField k) S
      ((curve t').baseChange (QuadraticField k)) (2 ^ n)}
    (I : KummerCoefficientComparisonSigned t k S hFull) :
    KummerCoefficientComparisonSigned t' k S hFull' := by
  subst htt
  exact I

end Faithful

/-! **Universal coefficients** -/

section Universal

variable {t : ℚ} {k : ℤ} [(curve t).IsElliptic]
  {S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))}
  {hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
    ((curve t).baseChange (QuadraticField k)) (2 ^ n)}

/-- **The Selmer identification induced by the cochain comparison**:
`H¹(C_K ⊗ ℚ₂/ℤ₂) ≃ Sel_{2^∞}(E_t/K)`. Kind: definition. -/
def KummerCoefficientComparisonSigned.selmerEquiv
    (I : KummerCoefficientComparisonSigned t k S hFull) :
    (arithmeticCoefficientComplexSigned t k S hFull).homology 1 ≃+ SelKSigned t k := by
  haveI : QuasiIso I.comparison := I.quasiIso
  let C := integerCoefficientComplex (arithmeticCoefficientComplexSigned t k S hFull)
  exact (integerHomologyEquiv (arithmeticCoefficientComplexSigned t k S hFull) 1).symm.trans
    ((asIso (HomologicalComplex.homologyMap (C.ιTruncLE 1) 1)).toLinearEquiv.toAddEquiv.symm.trans
      ((asIso (HomologicalComplex.homologyMap I.comparison 1)).toLinearEquiv.toAddEquiv.trans
        (discreteSelmerHomologyEquivSigned t k)))

variable (t k S hFull)

/-- **The manuscript's universal-coefficient map** `H¹(C_K) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(E_t/K)`, with the
tensor factors in the manuscript's order. Kind: definition. -/
def arithmeticUniversalCoefficientMapSigned (I : KummerCoefficientComparisonSigned t k S hFull) :
    ((arithmeticCompactComplexSigned t k S hFull).homology 1 ⊗[ℤ_[2]] Q2Z2) →+ SelKSigned t k :=
  (I.selmerEquiv).toAddMonoidHom.comp
    ((universalCoefficientMap (arithmeticCompactComplexSigned t k S hFull)).toAddMonoidHom.comp
      (TensorProduct.comm ℤ_[2] ((arithmeticCompactComplexSigned t k S hFull).homology 1)
        Q2Z2).toAddMonoidHom)

/-- **The Selmer connecting map** onto the actual torsion of `H²(C_K)`. Kind: definition. -/
def arithmeticSelmerConnectingSigned (I : KummerCoefficientComparisonSigned t k S hFull) :
    SelKSigned t k →+
      Submodule.torsion ℤ_[2] ((arithmeticCompactComplexSigned t k S hFull).homology 2) :=
  (coefficientTorsionConnecting (arithmeticCompactComplexSigned t k S hFull)).toAddMonoidHom.comp
    I.selmerEquiv.symm.toAddMonoidHom

/-- **The integral rank** `rank_{ℤ₂} H¹(C_K)/tors`, fixed by the genuine cohomology.
Kind: definition. -/
abbrev arithmeticRankSigned : ℕ :=
  Module.finrank ℤ_[2] (FreePart ((arithmeticCompactComplexSigned t k S hFull).homology 1))

/-- A basis of the actual integral free quotient of `H¹(C_K)`. Kind: definition. -/
def arithmeticFreeBasisSigned (F : KummerCohomologyFiniteSigned t k S hFull) :
    Module.Basis (Fin (arithmeticRankSigned t k S hFull)) ℤ_[2]
      (FreePart ((arithmeticCompactComplexSigned t k S hFull).homology 1)) := by
  have := F.finite_one
  exact freePartBasis _

/-- Divisible coordinates induced by that integral basis. Kind: definition. -/
def arithmeticDivisibleCoordinatesSigned (F : KummerCohomologyFiniteSigned t k S hFull) :
    Q2Z2 ⊗[ℤ_[2]] (arithmeticCompactComplexSigned t k S hFull).homology 1 ≃ₗ[ℤ_[2]]
      (Fin (arithmeticRankSigned t k S hFull) → Q2Z2) := by
  have := F.finite_one
  exact divisibleCoordinates _

/-- The rational identification `H¹(C_K ⊗ ℚ₂) ≃ ℚ₂^r`, by flat base change and the same integral
basis. Kind: definition. -/
def arithmeticRationalH1EquivSigned (F : KummerCohomologyFiniteSigned t k S hFull) :
    (arithmeticRationalComplexSigned t k S hFull).homology 1 ≃ₗ[ℚ_[2]]
      (Fin (arithmeticRankSigned t k S hFull) → ℚ_[2]) := by
  have := F.finite_one
  exact (rationalKummerHomologyIso S ((curve t).baseChange (QuadraticField k)) hFull
    1).toLinearEquiv.trans
      (rationalCoordinates ((arithmeticCompactComplexSigned t k S hFull).homology 1))

/-- The basis identifies `(ℚ₂/ℤ₂)^r` with the genuine tensor `H¹(C_K) ⊗ ℚ₂/ℤ₂`.
Kind: definition. -/
def arithmeticBasisToTensorSigned (F : KummerCohomologyFiniteSigned t k S hFull) :
    (Fin (arithmeticRankSigned t k S hFull) → Q2Z2) ≃+
      ((arithmeticCompactComplexSigned t k S hFull).homology 1 ⊗[ℤ_[2]] Q2Z2) :=
  ((arithmeticDivisibleCoordinatesSigned t k S hFull F).symm.trans
    (TensorProduct.comm ℤ_[2] Q2Z2
      ((arithmeticCompactComplexSigned t k S hFull).homology 1))).toAddEquiv

/-- **The universal-coefficient map in integral free-part coordinates**,
`j : (ℚ₂/ℤ₂)^r → Sel_{2^∞}(E_t/K)`. Kind: definition. -/
def arithmetic_jSigned (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) :
    (Fin (arithmeticRankSigned t k S hFull) → Q2Z2) →+ SelKSigned t k :=
  (arithmeticUniversalCoefficientMapSigned t k S hFull I).comp
    (arithmeticBasisToTensorSigned t k S hFull F).toAddMonoidHom

/-- `j` is the universal-coefficient map transported by the two specified equivalences.
Kind: PROVED. -/
theorem arithmetic_jSigned_as_transport (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) :
    arithmetic_jSigned t k S hFull I F = I.selmerEquiv.toAddMonoidHom.comp
      ((universalCoefficientMap (arithmeticCompactComplexSigned t k S hFull)).toAddMonoidHom.comp
        (arithmeticDivisibleCoordinatesSigned t k S hFull F).symm.toAddMonoidHom) := by
  apply AddMonoidHom.ext
  intro x
  change I.selmerEquiv
    (universalCoefficientMap (arithmeticCompactComplexSigned t k S hFull)
      ((TensorProduct.comm ℤ_[2] ((arithmeticCompactComplexSigned t k S hFull).homology 1) Q2Z2)
        ((TensorProduct.comm ℤ_[2] ((arithmeticCompactComplexSigned t k S hFull).homology 1)
          Q2Z2).symm ((arithmeticDivisibleCoordinatesSigned t k S hFull F).symm x)))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The universal-coefficient map is the coefficient-quotient formula on pure tensors.
Kind: PROVED. -/
theorem arithmeticUniversalCoefficientMapSigned_formula
    (I : KummerCoefficientComparisonSigned t k S hFull) (q : ℚ_[2])
    (x : (arithmeticCompactComplexSigned t k S hFull).homology 1) :
    arithmeticUniversalCoefficientMapSigned t k S hFull I (x ⊗ₜ[ℤ_[2]] divisibleQuotient q) =
      I.selmerEquiv (rationalToDivisible (arithmeticCompactComplexSigned t k S hFull)
        (q ⊗ₜ[ℤ_[2]] x)) := by
  change I.selmerEquiv
    (universalCoefficientMap (arithmeticCompactComplexSigned t k S hFull)
      (divisibleQuotient q ⊗ₜ[ℤ_[2]] x)) = _
  exact congrArg I.selmerEquiv (universalTensorMap_tmul _ _ _ q x)

/-- On a genuine cohomology tensor, `j` uses exactly the integral free-part basis.
Kind: PROVED. -/
theorem arithmetic_jSigned_on_tensor (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull)
    (x : (arithmeticCompactComplexSigned t k S hFull).homology 1) (d : Q2Z2) :
    arithmetic_jSigned t k S hFull I F
        (fun i => (arithmeticFreeBasisSigned t k S hFull F).equivFun
          ((Submodule.torsion ℤ_[2]
            ((arithmeticCompactComplexSigned t k S hFull).homology 1)).mkQ x) i • d) =
      arithmeticUniversalCoefficientMapSigned t k S hFull I (x ⊗ₜ[ℤ_[2]] d) := by
  have := F.finite_one
  have hc : arithmeticDivisibleCoordinatesSigned t k S hFull F (d ⊗ₜ[ℤ_[2]] x) =
      (fun i => (arithmeticFreeBasisSigned t k S hFull F).equivFun
        ((Submodule.torsion ℤ_[2]
          ((arithmeticCompactComplexSigned t k S hFull).homology 1)).mkQ x) i • d) := by
    funext i
    exact divisibleCoordinates_tmul _ d x i
  rw [arithmetic_jSigned_as_transport, ← hc]
  change I.selmerEquiv (universalCoefficientMap (arithmeticCompactComplexSigned t k S hFull)
    ((arithmeticDivisibleCoordinatesSigned t k S hFull F).symm
      (arithmeticDivisibleCoordinatesSigned t k S hFull F (d ⊗ₜ[ℤ_[2]] x)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The rational identification is the flat-base-change identification in the same integral
basis. Kind: PROVED. -/
theorem arithmeticRationalH1EquivSigned_on_tensor (F : KummerCohomologyFiniteSigned t k S hFull)
    (q : ℚ_[2]) (x : (arithmeticCompactComplexSigned t k S hFull).homology 1)
    (i : Fin (arithmeticRankSigned t k S hFull)) :
    arithmeticRationalH1EquivSigned t k S hFull F
        ((rationalKummerHomologyIso S ((curve t).baseChange (QuadraticField k)) hFull 1).inv.hom
          (q ⊗ₜ[ℤ_[2]] x)) i =
      ((arithmeticFreeBasisSigned t k S hFull F).equivFun
        ((Submodule.torsion ℤ_[2]
          ((arithmeticCompactComplexSigned t k S hFull).homology 1)).mkQ x) i : ℚ_[2]) * q := by
  have := F.finite_one
  let e := rationalKummerHomologyIso S ((curve t).baseChange (QuadraticField k)) hFull 1
  have h : e.hom.hom (e.inv.hom (q ⊗ₜ[ℤ_[2]] x)) = q ⊗ₜ[ℤ_[2]] x :=
    congrArg (fun f => f.hom (q ⊗ₜ[ℤ_[2]] x)) e.inv_hom_id
  change rationalCoordinates ((arithmeticCompactComplexSigned t k S hFull).homology 1)
    (e.hom.hom (e.inv.hom (q ⊗ₜ[ℤ_[2]] x))) i = _
  rw [h]
  exact rationalCoordinates_tmul _ q x i

/-- **`j` is injective** (no kernel is lost in the universal-coefficient map). Kind: PROVED. -/
theorem arithmetic_jSigned_injective (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) :
    Function.Injective (arithmetic_jSigned t k S hFull I F) := by
  rw [arithmetic_jSigned_as_transport]
  exact I.selmerEquiv.injective.comp
    ((universalCoefficientMap_injective (arithmeticCompactComplexSigned t k S hFull)).comp
      (arithmeticDivisibleCoordinatesSigned t k S hFull F).symm.injective)

/-- **`j` and the Selmer connecting map are exact.** Kind: PROVED. -/
theorem arithmetic_jSigned_exact (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) :
    Function.Exact (arithmetic_jSigned t k S hFull I F)
      (arithmeticSelmerConnectingSigned t k S hFull I) := by
  rw [arithmetic_jSigned_as_transport]
  exact exact_transport_addEquiv
    (universalCoefficientMap (arithmeticCompactComplexSigned t k S hFull)).toAddMonoidHom
    (coefficientTorsionConnecting (arithmeticCompactComplexSigned t k S hFull)).toAddMonoidHom
    (arithmeticDivisibleCoordinatesSigned t k S hFull F).symm.toAddEquiv I.selmerEquiv
    (universalCoefficient_exact _)

/-- **Every torsion class of `H²(C_K)` is a Selmer connecting class.** Kind: PROVED. -/
theorem arithmeticSelmerConnectingSigned_surjective
    (I : KummerCoefficientComparisonSigned t k S hFull) :
    Function.Surjective (arithmeticSelmerConnectingSigned t k S hFull I) := by
  intro y
  obtain ⟨x, hx⟩ :=
    coefficientTorsionConnecting_surjective (arithmeticCompactComplexSigned t k S hFull) y
  refine ⟨I.selmerEquiv x, ?_⟩
  change coefficientTorsionConnecting (arithmeticCompactComplexSigned t k S hFull)
    (I.selmerEquiv.symm (I.selmerEquiv x)) = y
  rw [AddEquiv.symm_apply_apply]
  exact hx

/-- **The universal-coefficient sequence**: the cokernel of `j` is the actual torsion of
`H²(C_K)`, `Sel_{2^∞}(E_t/K) / j((ℚ₂/ℤ₂)^r) ≃ H²(C_K)_tors`. Kind: definition (PROVED
equivalence). -/
def arithmetic_jSigned_cokernelEquiv (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) :
    (SelKSigned t k ⧸ (arithmetic_jSigned t k S hFull I F).range) ≃+
      Submodule.torsion ℤ_[2] ((arithmeticCompactComplexSigned t k S hFull).homology 2) :=
  QuotientAddGroup.liftEquiv (arithmetic_jSigned t k S hFull I F).range
    (arithmeticSelmerConnectingSigned_surjective t k S hFull I) (by
      ext y
      change (∃ x, arithmetic_jSigned t k S hFull I F x = y) ↔
        arithmeticSelmerConnectingSigned t k S hFull I y = 0
      exact (arithmetic_jSigned_exact t k S hFull I F y).symm)

/-- **A fixed power of two kills the cokernel of `j`** (finite generation of `H²`).
Kind: PROVED. -/
theorem arithmetic_jSigned_coker_two_power (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) :
    ∃ n : ℕ, ∀ y : SelKSigned t k, ∃ x,
      arithmetic_jSigned t k S hFull I F x = (2 ^ n : ℕ) • y := by
  have := F.finite_two
  obtain ⟨n, hn⟩ :=
    universalCoefficientMap_coker_two_power (arithmeticCompactComplexSigned t k S hFull)
  refine ⟨n, ?_⟩
  rw [arithmetic_jSigned_as_transport]
  exact coker_transport_addEquiv
    (universalCoefficientMap (arithmeticCompactComplexSigned t k S hFull)).toAddMonoidHom
    (arithmeticDivisibleCoordinatesSigned t k S hFull F).symm.toAddEquiv I.selmerEquiv (2 ^ n) hn

/-- **`j` has bounded defects**: zero kernel and a cokernel killed by a power of two.
Kind: PROVED. -/
theorem arithmetic_jSigned_boundedDefects (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) :
    BoundedDefects (arithmetic_jSigned t k S hFull I F) := by
  obtain ⟨n, hn⟩ := arithmetic_jSigned_coker_two_power t k S hFull I F
  refine ⟨1, 2 ^ n, one_ne_zero, pow_ne_zero n two_ne_zero, fun x hx => ?_, hn⟩
  have hx0 : x = 0 := arithmetic_jSigned_injective t k S hFull I F (hx.trans (map_zero _).symm)
  simpa only [one_nsmul] using hx0

/-- The number of coordinates is the genuine rational dimension of `H¹(C_K ⊗ ℚ₂)`.
Kind: PROVED. -/
theorem arithmeticRankSigned_eq_rational_finrank (F : KummerCohomologyFiniteSigned t k S hFull) :
    arithmeticRankSigned t k S hFull =
      Module.finrank ℚ_[2] ((arithmeticRationalComplexSigned t k S hFull).homology 1) := by
  rw [(arithmeticRationalH1EquivSigned t k S hFull F).finrank_eq, Module.finrank_fin_fun]

/-- **The rational Tate comparison `H¹(C_K ⊗ ℚ₂) ≃ V₂ Sel_{2^∞}(E_t/K)`**, induced by the actual
universal-coefficient map. Kind: definition. -/
def arithmeticRatTateEquivSigned (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) :
    (arithmeticRationalComplexSigned t k S hFull).homology 1 ≃ₗ[ℚ_[2]] RatTate (SelKSigned t k) :=
  universalCoefficientsRatTateEquiv (arithmeticRationalH1EquivSigned t k S hFull F)
    (arithmetic_jSigned t k S hFull I F) (arithmetic_jSigned_boundedDefects t k S hFull I F)

/-- **Rank = Selmer corank**: the integral rank of `H¹(C_K)` is the dimension of the rational Tate
module of the genuine `Sel_{2^∞}(E_t/ℚ(√k))`. Kind: PROVED. -/
theorem arithmeticRankSigned_eq_finrank_ratTate (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) :
    arithmeticRankSigned t k S hFull = Module.finrank ℚ_[2] (RatTate (SelKSigned t k)) :=
  (arithmeticRankSigned_eq_rational_finrank t k S hFull F).trans
    (arithmeticRatTateEquivSigned t k S hFull I F).finrank_eq

/-- **Rank additivity under the quadratic descent**: with coranks `r₁` of `Sel_{2^∞}(E_t/ℚ)` and
`r₂` of `Sel_{2^∞}(E_t^{(k)}/ℚ)`, the integral rank of `H¹(C_K)` is `r₁ + r₂`. Kind: PROVED. -/
theorem arithmeticRankSigned_eq_add (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) {r₁ r₂ : ℕ}
    (h₁ : Z2Corank (selmerTwoPower (curve t)) r₁)
    (h₂ : Z2Corank (selmerTwoPower (qtwist (curve t) (k : ℚ))) r₂) :
    arithmeticRankSigned t k S hFull = r₁ + r₂ := by
  rw [arithmeticRankSigned_eq_finrank_ratTate t k S hFull I F,
    finrank_ratTate_selKSigned t hk h₁ h₂]

/-- **Under the signed Selmer input the integral rank of `H¹(C_K)` is one.** Kind: PROVED. -/
theorem arithmeticRankSigned_eq_one (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) (hSel : SelmerCorankOneOverKSigned t k) :
    arithmeticRankSigned t k S hFull = 1 :=
  arithmeticRankSigned_eq_add t k S hFull hk I F hSel.1 hSel.2

end Universal

end ZInQ.Manuscript.RC
