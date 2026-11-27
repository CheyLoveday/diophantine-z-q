import ZInQKernel.Contrib.OneProof.RC.CoefModules.LocalConditions

/-!
# Lane RC28 (coefficient modules), part 8: the genuine Selmer complexes of the actual modules
and their finite Selmer duality

Manuscript `diophantine_zq.tex` (11/5): (4.3) at tex 3458–3463,

> `C_U = Cone(RΓ(G_{K,S}, M_i) ⊕ ⊕_{v∈S} U_v → ⊕_{v∈S} RΓ(K_v, M_i))[−1]`,

and Lemma `ex:arith-conjugate-duality`, tex 2761–2830:

> finite Selmer duality gives `C_U(M_i) ≃ RHom_{R_i}(C_{U⊥}(M_i^*(1)), R_i)[−3]` … A full
> condition is paired with the zero condition.

* `actualSelData`: lane RC26's genuine `galoisSelData` at the actual `M_i` (inflated to the
  Selmer support `S`) with the actual local conditions (`actualConditions`: given conditions at
  the old places `S₀`, unramified ones at `S − S₀`); `actualSelData_full`, `actualSelData_zero`
  (full and zero conditions everywhere).
* `weilPairingData`: the coefficient pairing `M_i × M_i(α⁻¹) → A_i(1)` with lane RC26's four
  hypotheses (`hβ`, `hb`, `hb'`, `IsCyclotomicTwist`) discharged: equivariance and the cyclotomic
  twist PROVED, perfectness PROVED from `FullTorsion` (GLUE, Néron–Ogg–Shafarevich).
* **`actualSelmerDuality_full_zero`**: for `M = M_i` with the full condition at every place and
  `M' = M_i(α⁻¹) ≅ M_i^*(1)` with the zero condition, the genuine Selmer duality map
  `C_full(M_i) → Hom_{A_i}(C_zero(M_i^*(1)), A_i)[−3]` is a quasi-isomorphism — PROVED from lane
  RC26's PRINT `NekovarProp543` (Nekovář 5.4.3) and its PROVED orthogonality of the full and zero
  conditions (`orthogonal_relaxed_strict`), with the hypotheses of the print discharged for the
  actual data (`nekovarFiniteSetting_acoef`, `isCyclotomicTwist_tate1`, the Weil pairing).

Kinds: definitions; PROVED (from the PRINT and the GLUE `FullTorsion`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain CategoryTheory ZInQ.Manuscript.RC.HeegnerAlgebra
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- The discrete topology on `A_i` (used only to state the unramified condition through lane
RC26's `TopRep`-based unramified complex; the local conditions do not depend on it). -/
abbrev acoefTop (i : ℕ) : TopologicalSpace (Acoef i) := ⊥

theorem acoefTop_discrete (i : ℕ) : @DiscreteTopology (Acoef i) (acoefTop i) :=
  @DiscreteTopology.mk (Acoef i) (acoefTop i) rfl

section Actual

variable {S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]

/-- **The genuine Selmer data (4.3) at the actual coefficient module** `M_i` (inflated to `S`),
for local conditions given at the old places `S₀` and the unramified conditions at `S − S₀`. -/
def actualSelData (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v) :
    SelData (Acoef i) :=
  letI := acoefTop i
  haveI := acoefTop_discrete i
  galoisSelData K S (Acoef i) (MinS hS W i α) (actualConditions hS W i α c)

/-- The actual local conditions are subcomplexes of the local cochains when the given ones at
`S₀` are (the shape of the leaf's `IsGaloisSelData`). Kind: PROVED. -/
theorem actualConditions_injective
    (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v)
    (hc : ∀ v h, (c v h).IsInjective) (v : Places K S) (n : ℤ) :
    letI := acoefTop i
    haveI := acoefTop_discrete i
    Function.Injective (((actualConditions hS W i α c).i v).f n n rfl) :=
  letI := acoefTop i
  haveI := acoefTop_discrete i
  ofCondAt_injective K S _ _ _ (urOutside_isInjective hS (Acoef i) (Mcoef K S₀ W i α) c hc) v n

end Actual

section Global

variable (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]

/-- The genuine Selmer data with the **full** condition at every place of `S`. -/
def actualSelData_full : SelData (Acoef i) :=
  galoisSelData K S (Acoef i) (Mcoef K S W i α) (relaxedConditions (Acoef i) _ _ _ _)

/-- The genuine Selmer data with the **zero** condition at every place of `S` (compactly
supported cochains, lane RC26's `strictIso`). -/
def actualSelData_zero : SelData (Acoef i) :=
  galoisSelData K S (Acoef i) (Mcoef K S W i α) (strictConditions (Acoef i) _ _ _ _)

variable (hμ : HasRootsOfUnity K S (2 ^ i))

/-- **The coefficient pairing of the duality** `M_i × M_i(α⁻¹) → A_i(1)` (the Weil pairing,
tex 2798–2804). -/
abbrev weilPairingData :
    Mcoef K S W i α →ₗ[Acoef i] Mcoef K S W i (charInv α) →ₗ[Acoef i] Tate1 (Acoef i) hμ :=
  weilPairingM W hμ (Acoef i) α

/-- **Finite Selmer duality for the actual coefficient modules, full against zero** (Lemma
`ex:arith-conjugate-duality`, tex 2761–2830, "A full condition is paired with the zero
condition"; Nekovář, *Selmer complexes*, 6.3.4, p. 143): for an imaginary quadratic (totally
complex) `K`, a finite `S ⊇ {v | 2}` over which `E[2^i]` is defined (`FullTorsion`, GLUE) and any
trace `tr` on `C³_c(G_{K,S}, A_i(1))` killing coboundaries and inducing `H³_c ≅ A_i`, the genuine
Selmer duality map
`C_full(M_i) → Hom_{A_i}(C_zero(M_i(α⁻¹)), A_i)[−3]`, `M_i(α⁻¹) ≅ M_i^*(1)` (`weilDualEquiv`),
is a quasi-isomorphism. Kind: PROVED from lane RC26's PRINT `NekovarProp543` (Nekovář 5.4.3) and
the GLUE `FullTorsion`; every other hypothesis of the print is discharged here. -/
theorem actualSelmerDuality_full_zero [NeZero i] (h543 : NekovarProp543 K)
    (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hW : FullTorsion K S W (2 ^ i))
    (tr : (galoisCompactT K S (Acoef i) (weilPairingData W i α hμ)
      (weilPairingM_smul W hμ (Acoef i) α) (relaxedConditions (Acoef i) _ _ _ _)
      (strictConditions (Acoef i) _ _ _ _)
      (relaxedStrictIsotropy K (weilPairingData W i α hμ)
        (weilPairingM_smul W hμ (Acoef i) α))).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactT K S (Acoef i) (weilPairingData W i α hμ)
      (weilPairingM_smul W hμ (Acoef i) α) (relaxedConditions (Acoef i) _ _ _ _)
      (strictConditions (Acoef i) _ _ _ _)
      (relaxedStrictIsotropy K (weilPairingData W i α hμ)
        (weilPairingM_smul W hμ (Acoef i) α))).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairData K S (Acoef i)
      (weilPairingData W i α hμ) (weilPairingM_smul W hμ (Acoef i) α)
      (relaxedConditions (Acoef i) _ _ _ _) (strictConditions (Acoef i) _ _ _ _)
      (relaxedStrictIsotropy K (weilPairingData W i α hμ)
        (weilPairingM_smul W hμ (Acoef i) α))) tr htr)) :=
  genuineSelmerDuality K (weilPairingData W i α hμ) (weilPairingM_smul W hμ (Acoef i) α)
    (relaxedConditions (Acoef i) _ _ _ _) (strictConditions (Acoef i) _ _ _ _)
    (relaxedStrictIsotropy K (weilPairingData W i α hμ) (weilPairingM_smul W hμ (Acoef i) α))
    tr htr h543 2 (nekovarFiniteSetting_acoef K hK S hSfin h2 i)
    (weilPairingM_bijective W hμ (Acoef i) α hW) (weilPairingM_flip_bijective W hμ (Acoef i) α hW)
    (isCyclotomicTwist_tate1 (Acoef i) hμ) htr3
    (orthogonal_relaxed_strict K (weilPairingData W i α hμ) (weilPairingM_smul W hμ (Acoef i) α)
      tr htr)

end Global

end ZInQ.Manuscript.RC.CoefModules
