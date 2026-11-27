import ZInQKernel.Contrib.OneProof.HeightModelM.MetricTransport

/-!
# Gaudron–Rémond's height on a semi-abelian model, and the identification (item M)

**Print.** É. Gaudron, G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*,
Comment. Math. Helv. 89 (2014) (GR1), §2.3, p. 351: "soit `K` une extension finie de `k` sur
laquelle `A` est définie et admet réduction semi-abélienne. Soient `π : 𝒜 → Spec 𝒪_K` un modèle
semi-abélien de `A` et `ε : Spec 𝒪_K → 𝒜` sa section nulle." The height `h(A)` is the
normalized Arakelov degree (Def. 2.1) of `ε*Ω^g_{𝒜/Spec 𝒪_K}` with the metric
`‖s‖²_σ = (2π)^{-g} ∫ |s ∧ s̄|`; "Cette définition est indépendante des choix de `K` et de `𝒜`."
P. 352: Faltings' original `h_F(A)` omits the `π`, and `h_F(A) = h(A) - (g/2) log π`.

**Lean.** `IsGR1StableHeightOriginal A x`: there are a number field `K'` over the base, a
semi-abelian group model `𝒜` of `A_{K'}` over `𝓞_{K'}` (`IsSemiAbelianModel`), and a nonzero
section `η` of `ε*Ω^g = ⋀^g ω_𝒜` (the printed lattice `printedDetLattice`, `ω = Γ(S, e*Ω¹)`) with
finite index, whose archimedean norms `r τ = ‖η‖²_τ` are those of the measure `(i/2)^g η̃ ∧ η̄̃` on
`A_τ(ℂ)^an` (`IsAnMetricSq`; this is `2^{-g} ∫ |η ∧ η̄|`, Faltings' original normalization), and
`x` is the normalized Arakelov degree `(log #(ω/𝓞 η) - ½ Σ_τ log r τ) / [K' : ℚ]`. So `x = h_F(A)`
and `h(A) = x + (g/2) log π`. It is `IsAnStableHeightSS` with the Néron model and its
semistability replaced by a semi-abelian model.

**Identification** (`isGR1StableHeightOriginal_of_isAnStableHeightSS`): from EGA IV₃ (9.7.7)(ii),
the height computed on the semistable Néron model `𝒩` is the height on the semi-abelian model
`𝒩⁰` (`exists_semiAbelianModel`): same field, the section pulled back along `𝒩⁰ → 𝒩`, the same
index (`secIndex_hodgeMap`) and the same norms (`isAnMetricSq_hodgeMap`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology MonObj
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightDict ZInQ.HeightFix
open ZInQ.R3Residual ZInQ.H5Glue ZInQ.SemistabAssembly CToPrinted
open scoped NumberField

set_option linter.style.haveILetI false

namespace ZInQ.HeightModelM

/-- **Gaudron–Rémond's stable height on a semi-abelian model, original normalization** (GR1 §2.3,
p. 351, with `h_F = h - (g/2) log π`, p. 352): `x = h_F(A)` computed on some semi-abelian group
model `𝒜` of `A` over the ring of integers of a number field `K'` over the base. -/
def IsGR1StableHeightOriginal {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (𝒜 : GroupModel A K')
    (g : ℕ), IsSemiAbelianModel 𝒜 ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta ∈ printedDetLattice 𝒜 g, eta ≠ 0 ∧ secIndex (printedDetLattice 𝒜 g) eta ≠ 0 ∧
      ∃ r : (K' →+* ℂ) → ℝ, (∀ τ, IsAnMetricSq 𝒜 τ eta (r τ)) ∧
        x = (Real.log (secIndex (printedDetLattice 𝒜 g) eta) -
          (1 / 2) * ∑ τ : K' →+* ℂ, Real.log (r τ)) / Module.finrank ℚ K'

/-- The identification with the openness input stated as the finiteness of the disconnected
fibres (`GenericConnectedFibresOL`). The witness is `𝒩⁰`, over the same field. -/
theorem isGR1StableHeightOriginal_of_generic (hG : GenericConnectedFibresOL) {K : Type}
    [Field K] {A : PkgI3.AbVar K} {x : ℝ} (hx : IsAnStableHeightSS A x) :
    IsGR1StableHeightOriginal A x := by
  obtain ⟨L, iF, iN, iA, 𝒩, g, -, hS, hg, eta, heta, hne, hsec, r, hr, hxeq⟩ := hx
  have hO : IsOpen (idCompSet 𝒩.G) := isOpen_idCompSet_of_generic hG 𝒩
  obtain ⟨𝒢₀, i, hoi, hmh, -, hsa⟩ := exists_semiAbelianModel 𝒩 hO hS
  haveI := hoi
  haveI := hmh
  refine ⟨L, iF, iN, iA, 𝒢₀, g, hsa, hg, hodgeMap 𝒢₀ 𝒩 i g eta,
    hodgeMap_mem_printedDetLattice 𝒢₀ 𝒩 i g heta, ?_, ?_, r,
    fun τ => isAnMetricSq_hodgeMap 𝒢₀ 𝒩 i τ eta (r τ) (hr τ), ?_⟩
  · intro h0
    exact hne (hodgeMap_injective 𝒢₀ 𝒩 i g (h0.trans (map_zero _).symm))
  · rw [secIndex_hodgeMap]
    exact hsec
  · rw [secIndex_hodgeMap]
    exact hxeq

/-- **Item M: the height on the semistable Néron model is Gaudron–Rémond's height on a
semi-abelian model** (given EGA IV₃ (9.7.7)(ii)). -/
theorem isGR1StableHeightOriginal_of_isAnStableHeightSS (hE : EGAIV_9_7_7_OL) {K : Type}
    [Field K] {A : PkgI3.AbVar K} {x : ℝ} (hx : IsAnStableHeightSS A x) :
    IsGR1StableHeightOriginal A x :=
  isGR1StableHeightOriginal_of_generic (genericConnectedFibresOL_of_ega hE) hx

end ZInQ.HeightModelM
