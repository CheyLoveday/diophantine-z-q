import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenuineSteps
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuityGenuine
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.LocalJ
import ZInQKernel.Contrib.CloudB3RC53.Detecting.Exists

/-!
# RC53 SwitchInputs: wiring the quadratic switch steps

Proposition `ex:limits-uniform-lower-bound`, the quadratic switch (tex L5003–5136). The
homology-level quadratic steps of `GenuineSteps.lean` (`QuasiQuadSwitch`, `QuasiMixedStep`,
`QuasiSingleStep`) take as inputs the involutions on the four cohomology groups with their
compatibilities, the duality in RC16's `localPair` form, and the fixed-prime `DetectingPrime(Plus)`.
This file wires those inputs to the results that supply them:

* **(1) the involutions** (tex L5009–5037): `QuasiDiagramInvolution` — one Selmer involution of the
  relaxed data (GaloisInvolution's `SelEndo`, on genuine complexes `CondConj.selEndo`) with stable
  side and strict conditions — gives the four involutions and the diagram compatibilities
  (`QuasiDiagramInvolution.fields`, PROVED). The two side clauses `hβ′` (`J` on `F`) and `hβ″` (`−J`
  on `S`) are PROVED from the single relaxed clause `hl` (`hβF_of_hl`, `hβS_of_hl`), the strict
  compatibility `hα″` from an equivariant strict identification (`hα''_of_strict`), and `hl` itself
  from LocalJ's cocycle computation (`hl_of_cocycleRep`, via `hloc_of_cocycleRep`).
  `QuasiDiagramInvolution.toQuasiQuadSwitch` builds the actual `QuasiQuadSwitch`.
* **(3) the `localPair`-form duality** (tex L5046–5054, L5068–5075): for the symmetric normalization
  `σ = 1`, RC16's `switchPairing ε 1 J` IS `localPair ε (toLin' J)` (`switchPairing_one_eq_localPair`,
  PROVED), so `U = U^⊥` in the switch-pairing form (`LocalizationDualityInput`, e.g. from
  `DualityFromSelmer.duality`) gives the quadratic steps' `hU` (`hU_of_orthogonal`,
  `hU_of_dualityFromSelmer`, PROVED).
* **(2) the detecting prime**: the other team's provable form `DetectingPrimeExists` over the candidate
  new primes gives a prime `q` with the fixed-prime `DetectingPrime` there (`exists_detectingPrime`);
  `quasiMixedStep_of_exists` / `quasiSingleStep_of_exists` build the step at that `q` from candidate
  switch data indexed by the new primes, and `quasiMixedStep_of_genuine` /
  `quasiSingleStep_of_genuine` additionally take the duality from `DualityFromSelmer` (PROVED from the
  inputs in their types).

Remaining inputs (in the types): the Selmer involution `X` and the stability of the side and strict
conditions (on genuine complexes: `GaloisInvolution.CondConj`); the local-representative hypotheses of
`hl_of_cocycleRep` (the genuine local component acts on cocycle representatives, and the localization
reads `(c(φ), c(σ))`); the equivariance `heK` of the strict identification; finiteness of the side
`H¹`; `DualityFromSelmer` (its `hγ` / `hsw`) with `σ = 1`; `DetectingPrimeExists`; and the
equivariant fibre isomorphisms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.UniformSwitch
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.Uniform.QuadraticCase

/-! ### (1) The involutions from one Selmer involution -/

section Involution

variable {k : Type} [Field k]

/-- **One involution for the quasi change-of-condition diagram** (tex L5009–5013, L5065–5069): a
Selmer involution `X` of the relaxed data `C(U_rel)` (on genuine continuous cochains:
`GaloisInvolution.CondConj.selEndo`), with involutions `μ_F`, `μ_S` of the side conditions and
`μ_{F,str}` of the finite strict condition commuting with the inclusions. The quasi-side analogue of
`DiagramInvolution`. -/
structure QuasiDiagramInvolution (R : QuasiRelaxedLocalization k)
    (SF : QuasiSwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k)))
    (SS : QuasiSwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))) where
  X : SelEndo R.D
  hX : X.IsInvolution
  μF : GHom SF.U₁ SF.U₁
  hμF : ∀ i (u : SF.U₁.X i), SF.f₁.f i i rfl (μF.f i i rfl u) = X.mu.f i i rfl (SF.f₁.f i i rfl u)
  hμF2 : ∀ i (u : SF.U₁.X i), μF.f i i rfl (μF.f i i rfl u) = u
  μFs : GHom SF.Ustr SF.Ustr
  hμFs : ∀ i (u : SF.Ustr.X i), SF.fs.f i i rfl (μFs.f i i rfl u) = μF.f i i rfl (SF.fs.f i i rfl u)
  hμFs2 : ∀ i (u : SF.Ustr.X i), μFs.f i i rfl (μFs.f i i rfl u) = u
  μS : GHom SS.U₁ SS.U₁
  hμS : ∀ i (u : SS.U₁.X i), SS.f₁.f i i rfl (μS.f i i rfl u) = X.mu.f i i rfl (SS.f₁.f i i rfl u)
  hμS2 : ∀ i (u : SS.U₁.X i), μS.f i i rfl (μS.f i i rfl u) = u

namespace QuasiDiagramInvolution

variable {R : QuasiRelaxedLocalization k}
  {SF : QuasiSwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))}
  {SS : QuasiSwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))} (Y : QuasiDiagramInvolution R SF SS)

/-- The induced Selmer involution of the finite side `C(U_F)`. -/
def XF : SelEndo SF.Dside := Y.X.restrict SF.f₁ Y.μF Y.hμF

/-- The induced Selmer involution of the singular side `C(U_S)`. -/
def XS : SelEndo SS.Dside := Y.X.restrict SS.f₁ Y.μS Y.hμS

/-- The induced Selmer involution of the finite strict data `C(U_str)`. -/
def XK : SelEndo SF.Dstr := Y.XF.restrict SF.fs Y.μFs Y.hμFs

/-- `σ_r = H¹(σ)` on `H¹(C(U_rel))`. -/
def σr : (selCx R.D).toCC.homology 1 →ₗ[k] (selCx R.D).toCC.homology 1 := H1 Y.X.sigma
/-- `σ_V` on `V = H¹(C(U_F))`. -/
def σV : (selCx SF.Dside).toCC.homology 1 →ₗ[k] (selCx SF.Dside).toCC.homology 1 := H1 Y.XF.sigma
/-- `σ_{V′}` on `V′ = H¹(C(U_S))`. -/
def σV' : (selCx SS.Dside).toCC.homology 1 →ₗ[k] (selCx SS.Dside).toCC.homology 1 := H1 Y.XS.sigma
/-- `σ_K` on `K₀ = H¹(C(U_str))`. -/
def σK : (selCx SF.Dstr).toCC.homology 1 →ₗ[k] (selCx SF.Dstr).toCC.homology 1 := H1 Y.XK.sigma

/-- **The four involutions and the diagram compatibilities** of `QuasiQuadSwitch` from one
involution (tex L5065–5086). PROVED. -/
theorem fields :
    Y.σr ∘ₗ Y.σr = LinearMap.id ∧ Y.σV ∘ₗ Y.σV = LinearMap.id ∧ Y.σV' ∘ₗ Y.σV' = LinearMap.id ∧
    Y.σK ∘ₗ Y.σK = LinearMap.id ∧
    H1 (changeMap SF.Dside SF.fs) ∘ₗ Y.σK = Y.σV ∘ₗ H1 (changeMap SF.Dside SF.fs) ∧
    H1 (changeMap R.D SF.f₁) ∘ₗ Y.σV = Y.σr ∘ₗ H1 (changeMap R.D SF.f₁) ∧
    H1 (changeMap R.D SS.f₁) ∘ₗ Y.σV' = Y.σr ∘ₗ H1 (changeMap R.D SS.f₁) := by
  have hF := Y.X.restrict_isInvolution SF.f₁ Y.μF Y.hμF Y.hX Y.hμF2
  have hS := Y.X.restrict_isInvolution SS.f₁ Y.μS Y.hμS Y.hX Y.hμS2
  have hK := Y.XF.restrict_isInvolution SF.fs Y.μFs Y.hμFs hF Y.hμFs2
  refine ⟨Y.X.H1_sigma_sigma Y.hX, Y.XF.H1_sigma_sigma hF, Y.XS.H1_sigma_sigma hS,
    Y.XK.H1_sigma_sigma hK, ?_, ?_, ?_⟩
  · exact (Y.XF.H1_changeMap_sigma SF.fs Y.μFs Y.hμFs).symm
  · exact (Y.X.H1_changeMap_sigma SF.f₁ Y.μF Y.hμF).symm
  · exact (Y.X.H1_changeMap_sigma SS.f₁ Y.μS Y.hμS).symm

/-- **`J` on the finite plane from the relaxed clause** (tex L5027–5037): if the relaxed localization
is equivariant, `λ ∘ σ_r = (J × −J) ∘ λ`, then the finite localization satisfies `β ∘ σ_V = J ∘ β`.
PROVED (from `hγ′` of `fields`). -/
theorem hβF_of_hl (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hl : R.lamQ ∘ₗ Y.σr = localInv J ∘ₗ R.lamQ) : SF.βF ∘ₗ Y.σV = J ∘ₗ SF.βF := by
  have hγ := Y.fields.2.2.2.2.2.1
  ext1 v
  have e1 := LinearMap.congr_fun hγ v
  have e2 := LinearMap.congr_fun hl (H1 (changeMap R.D SF.f₁) v)
  have e3 : R.lamQ (H1 (changeMap R.D SF.f₁) (Y.σV v)) =
      localInv J (R.lamQ (H1 (changeMap R.D SF.f₁) v)) := (congrArg R.lamQ e1).trans e2
  exact congrArg Prod.fst e3

/-- **`−J` on the singular plane from the relaxed clause** (tex L5027–5037). PROVED (from `hγ″`). -/
theorem hβS_of_hl (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hl : R.lamQ ∘ₗ Y.σr = localInv J ∘ₗ R.lamQ) : SS.βS ∘ₗ Y.σV' = (-J) ∘ₗ SS.βS := by
  have hγ := Y.fields.2.2.2.2.2.2
  ext1 v
  have e1 := LinearMap.congr_fun hγ v
  have e2 := LinearMap.congr_fun hl (H1 (changeMap R.D SS.f₁) v)
  have e3 : R.lamQ (H1 (changeMap R.D SS.f₁) (Y.σV' v)) =
      localInv J (R.lamQ (H1 (changeMap R.D SS.f₁) v)) := (congrArg R.lamQ e1).trans e2
  exact congrArg Prod.snd e3

/-- **The strict compatibility `hα″` from an equivariant strict identification** (tex L5072–5083,
"with `D⁰` retained"): if the singular strict condition carries an involution `μ_{S,str}` compatible
with `μ_S`, and the strict identification `eK` intertwines the two strict involutions, then
`hα″` holds. PROVED. -/
theorem hα''_of_strict (μSs : GHom SS.Ustr SS.Ustr)
    (hμSs : ∀ i (u : SS.Ustr.X i), SS.fs.f i i rfl (μSs.f i i rfl u) = Y.μS.f i i rfl (SS.fs.f i i rfl u))
    (eK : (selCx SS.Dstr).toCC.homology 1 ≃ₗ[k] (selCx SF.Dstr).toCC.homology 1)
    (heK : eK.toLinearMap ∘ₗ H1 (Y.XS.restrict SS.fs μSs hμSs).sigma = Y.σK ∘ₗ eK.toLinearMap) :
    (H1 (changeMap SS.Dside SS.fs) ∘ₗ eK.symm.toLinearMap) ∘ₗ Y.σK =
      Y.σV' ∘ₗ (H1 (changeMap SS.Dside SS.fs) ∘ₗ eK.symm.toLinearMap) := by
  have hc := Y.XS.H1_changeMap_sigma SS.fs μSs hμSs
  ext1 v
  have e0 : eK.symm (Y.σK v) = H1 (Y.XS.restrict SS.fs μSs hμSs).sigma (eK.symm v) := by
    apply eK.injective
    rw [LinearEquiv.apply_symm_apply]
    exact ((LinearMap.congr_fun heK (eK.symm v)).trans
      (congrArg Y.σK (eK.apply_symm_apply v))).symm
  calc H1 (changeMap SS.Dside SS.fs) (eK.symm (Y.σK v))
      = H1 (changeMap SS.Dside SS.fs) (H1 (Y.XS.restrict SS.fs μSs hμSs).sigma (eK.symm v)) :=
        congrArg _ e0
    _ = Y.σV' (H1 (changeMap SS.Dside SS.fs) (eK.symm v)) :=
        (LinearMap.congr_fun hc (eK.symm v)).symm

/-- **`QuasiQuadSwitch` from one diagram involution** (tex L5009–5086): the four involutions and
`hK, hV, hV′, hr, hα′, hγ′, hγ″` from `fields`, the side clauses `hβ′, hβ″` from the relaxed clause
`hl`; in the type remain finiteness of the two side `H¹`, the strict identification `eK` with `hα″`
(supplied by `hα''_of_strict`), and `hl` (supplied by `hl_of_cocycleRep`). PROVED. -/
def toQuasiQuadSwitch (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (fV : FiniteDimensional k ((selCx SF.Dside).toCC.homology 1))
    (fV' : FiniteDimensional k ((selCx SS.Dside).toCC.homology 1))
    (eK : (selCx SS.Dstr).toCC.homology 1 ≃ₗ[k] (selCx SF.Dstr).toCC.homology 1)
    (hα'' : (H1 (changeMap SS.Dside SS.fs) ∘ₗ eK.symm.toLinearMap) ∘ₗ Y.σK =
      Y.σV' ∘ₗ (H1 (changeMap SS.Dside SS.fs) ∘ₗ eK.symm.toLinearMap))
    (hl : R.lamQ ∘ₗ Y.σr = localInv J ∘ₗ R.lamQ) : QuasiQuadSwitch k J :=
  have h := Y.fields
  { R := R, SF := SF, SS := SS, fV := fV, fV' := fV', eK := eK,
    σK := Y.σK, σV := Y.σV, σV' := Y.σV', σr := Y.σr,
    hK := h.2.2.2.1, hV := h.2.1, hV' := h.2.2.1, hr := h.1,
    hα' := h.2.2.2.2.1, hβ' := Y.hβF_of_hl J hl, hγ' := h.2.2.2.2.2.1, hα'' := hα'',
    hβ'' := Y.hβS_of_hl J hl, hγ'' := h.2.2.2.2.2.2, hl := hl }

/-- **The relaxed clause `hl` from LocalJ's cocycle computation** (tex L5027–5037): with the tame
local relations at the inert derivative prime (`φ = Φ²`, `Φ⁻¹σΦ = σ^m`, `σ` acting trivially,
`m ≡ −1`, `J = ρ(Φ)` with `J² = 1`), if every class of `H¹(C(U_rel))` has a local cocycle
representative whose coordinates `(c(φ), c(σ))` are its relaxed localization, and `σ_r` acts on
representatives by the cocycle action up to a coboundary, then `λ ∘ σ_r = (J × −J) ∘ λ`.
PROVED (from `LocalJ.hloc_of_cocycleRep`). -/
theorem hl_of_cocycleRep {G : Type} [Group G] (ρ : G →* Module.End k (Fin 2 → k)) (φ σ Φ : G)
    (m : ℤ) (hφ : φ = Φ * Φ) (hconj : Φ⁻¹ * σ * Φ = σ ^ m) (hσ : ρ σ = 1) (hm : (m : k) = -1)
    (hJ2 : ρ Φ * ρ Φ = 1) (rep : (selCx R.D).toCC.homology 1 → G → (Fin 2 → k))
    (hrep : ∀ v, IsCocycle ρ (rep v)) (hcoord : ∀ v, coord φ σ (rep v) = R.lamQ v)
    (hact : ∀ v, ∃ t : Fin 2 → k, ∀ g, rep (Y.σr v) g = cocAct ρ Φ (rep v) g + (ρ g t - t)) :
    R.lamQ ∘ₗ Y.σr = localInv (ρ Φ) ∘ₗ R.lamQ :=
  LinearMap.ext (hloc_of_cocycleRep ρ φ σ Φ m hφ hconj hσ hm hJ2 Y.σr R.lamQ rep hrep hcoord hact)

end QuasiDiagramInvolution

/-- A literal diagram involution is a quasi one (same Selmer involution and conditions). PROVED. -/
def DiagramInvolution.toQuasi {R : RelaxedLocalization k}
    {SF : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))}
    {SS : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))} (Y : DiagramInvolution R SF SS) :
    QuasiDiagramInvolution R.toQuasi SF.toQuasi SS.toQuasi :=
  ⟨Y.X, Y.hX, Y.μF, Y.hμF, Y.hμF2, Y.μFs, Y.hμFs, Y.hμFs2, Y.μS, Y.hμS, Y.hμS2⟩

end Involution

/-! ### (3) The `localPair`-form duality from the switch-pairing form -/

section Bridge

variable {k : Type} [Field k]

/-- **The symmetric switch pairing is the local pairing** (tex L5038–5054): for `σ = 1`,
`switchPairing ε 1 J (u, w) = localPair ε (toLin' J) (u, w)`. PROVED. -/
theorem switchPairing_one_eq_localPair (ε : k) (J : Matrix (Fin 2) (Fin 2) k)
    (u w : (Fin 2 → k) × (Fin 2 → k)) :
    switchPairing ε 1 J u w = localPair ε (Matrix.toLin' J) u w := by
  simp only [planePairing_apply, crossPairing_apply, one_mul, localPair, crossPair, weil_apply,
    e₂_apply, Matrix.toLin'_apply]

/-- The local pairing is symmetric. PROVED. -/
theorem localPair_symm (ε : k) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (u w : (Fin 2 → k) × (Fin 2 → k)) : localPair ε J u w = localPair ε J w u := by
  unfold localPair
  ring

/-- **The `localPair`-form self-annihilation from the switch-pairing form** (tex L5068–5075 with
L5046–5054): `U^⊥ = U` for `switchPairing ε 1 J` gives `u ∈ U ↔ ∀ w ∈ U, localPair ε (toLin' J) u w
= 0`, the field `hU` of the quadratic steps. PROVED. -/
theorem hU_of_orthogonal (ε : k) (J : Matrix (Fin 2) (Fin 2) k)
    (U : Submodule k ((Fin 2 → k) × (Fin 2 → k))) (h : (switchPairing ε 1 J).orthogonal U = U) :
    ∀ u, u ∈ U ↔ ∀ w ∈ U, localPair ε (Matrix.toLin' J) u w = 0 := by
  intro u
  conv_lhs => rw [← h]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun w _ => ?_
  rw [switchPairing_one_eq_localPair, localPair_symm]

/-- `LocalizationDualityInput` with `σ = 1` gives the `localPair` form. PROVED. -/
theorem hU_of_localizationDuality (ε : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0)
    (hJ2 : J * J = 1) (U : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (h : LocalizationDualityInput ε 1 J hε one_ne_zero hJ2 U) :
    ∀ u, u ∈ U ↔ ∀ w ∈ U, localPair ε (Matrix.toLin' J) u w = 0 :=
  hU_of_orthogonal ε J U h

/-- **The quadratic `hU` from Selmer duality** (tex L5068–5075): for `DualityFromSelmer` with the
symmetric normalization `σ = 1` (the hyperbolic planes are symmetric, tex L5046–5052), the actual
relaxed image satisfies the `localPair`-form self-annihilation. PROVED (from the inputs of
`DualityFromSelmer`, via the other team's `switchAdjunctionFromDuality_proof`). -/
theorem hU_of_dualityFromSelmer {R : QuasiRelaxedLocalization k} (D : DualityFromSelmer R)
    (hσ1 : D.σ = 1) :
    ∀ u, u ∈ R.U ↔ ∀ w ∈ R.U, localPair D.ε (Matrix.toLin' D.J) u w = 0 := by
  have h := D.duality
  unfold LocalizationDualityInput at h
  rw [hσ1] at h
  exact hU_of_orthogonal D.ε D.J R.U h

end Bridge

/-! ### (2) The steps at a detecting prime -/

section Steps

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- **The mixed-sign step at a detecting prime** (tex L5086–5122): candidate switch data `X q` at
the new primes `q ∈ P`, each with an equivariant isomorphism of its finite side `H¹` with the old
stage fibre and of its singular side `H¹` with the new stage fibre, the `localPair` duality at each
`q`, nonzero classes of both signs in the old fibre, and the other team's `DetectingPrimeExists` for
the localizations at the candidates. Then some candidate gives a `QuasiMixedStep`. PROVED. -/
theorem quasiMixedStep_of_exists {ι : A →+* F} {ρ : A →+* k} {S : TwoTermStage ι}
    {σS : fiberH1 ρ S →ₗ[k] fiberH1 ρ S} {P : Type} {S' : P → TwoTermStage ι}
    {σS' : ∀ q, fiberH1 ρ (S' q) →ₗ[k] fiberH1 ρ (S' q)}
    (h2 : (2 : k) ≠ 0) (ε : k) (hε : ε ≠ 0) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) (X : P → QuasiQuadSwitch k J)
    (hU : ∀ q u, u ∈ (X q).R.U ↔ ∀ w ∈ (X q).R.U, localPair ε J u w = 0)
    (φ : ∀ q, (selCx (X q).SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S)
    (hφ : ∀ q, (φ q).toLinearMap ∘ₗ (X q).σV = σS ∘ₗ (φ q).toLinearMap)
    (φ' : ∀ q, (selCx (X q).SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ (S' q))
    (hφ' : ∀ q, (φ' q).toLinearMap ∘ₗ (X q).σV' = σS' q ∘ₗ (φ' q).toLinearMap)
    (cp cm : fiberH1 ρ S) (hp0 : cp ≠ 0) (hm0 : cm ≠ 0) (hcp : σS cp = cp) (hcm : σS cm = -cm)
    (hex : DetectingPrimeExists σS (fun q => (X q).R.lamQ ∘ₗ H1 (changeMap (X q).R.D (X q).SF.f₁) ∘ₗ
      (φ q).symm.toLinearMap) cp cm) :
    ∃ q, Nonempty (QuasiMixedStep ρ S (S' q) σS (σS' q)) := by
  obtain ⟨q, hq⟩ := exists_detectingPrime hex hp0 hm0 hcp hcm
  have hsym : ∀ x, (X q).σV ((φ q).symm x) = (φ q).symm (σS x) := by
    intro x
    apply (φ q).injective
    have := LinearMap.congr_fun (hφ q) ((φ q).symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    rw [LinearEquiv.apply_symm_apply, this]
  have hcp' : (X q).σV ((φ q).symm cp) = (φ q).symm cp := by rw [hsym, hcp]
  have hcm' : (X q).σV ((φ q).symm cm) = -(φ q).symm cm := by rw [hsym, hcm, map_neg]
  exact ⟨q, ⟨⟨h2, ε, hε, J, hJ2, ep, em, hp, hm, he, X q, hU q, (φ q).symm cp, (φ q).symm cm,
    hcp', hcm', fun _ _ => hq hcp hcm, φ q, hφ q, φ' q, hφ' q⟩⟩⟩

/-- **The single-sign step at a detecting prime** (tex L5123–5136), with the other team's
`DetectingPrimePlusExists`. PROVED. -/
theorem quasiSingleStep_of_exists {ι : A →+* F} {ρ : A →+* k} {S : TwoTermStage ι}
    {σS : fiberH1 ρ S →ₗ[k] fiberH1 ρ S} {P : Type} {S' : P → TwoTermStage ι}
    {σS' : ∀ q, fiberH1 ρ (S' q) →ₗ[k] fiberH1 ρ (S' q)}
    (h2 : (2 : k) ≠ 0) (ε : k) (hε : ε ≠ 0) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) (X : P → QuasiQuadSwitch k J)
    (hU : ∀ q u, u ∈ (X q).R.U ↔ ∀ w ∈ (X q).R.U, localPair ε J u w = 0)
    (φ : ∀ q, (selCx (X q).SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S)
    (hφ : ∀ q, (φ q).toLinearMap ∘ₗ (X q).σV = σS ∘ₗ (φ q).toLinearMap)
    (φ' : ∀ q, (selCx (X q).SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ (S' q))
    (hφ' : ∀ q, (φ' q).toLinearMap ∘ₗ (X q).σV' = σS' q ∘ₗ (φ' q).toLinearMap ∨
      (φ' q).toLinearMap ∘ₗ (X q).σV' = (-σS' q) ∘ₗ (φ' q).toLinearMap)
    (hs1 : ∀ q, 1 < finrank k ↥(signPart (X q).σV (1 : k)))
    (hs0 : ∀ q, 0 = finrank k ↥(signPart (X q).σV (-1 : k)))
    (cp : fiberH1 ρ S) (hp0 : cp ≠ 0) (hcp : σS cp = cp)
    (hex : DetectingPrimePlusExists σS (fun q => (X q).R.lamQ ∘ₗ
      H1 (changeMap (X q).R.D (X q).SF.f₁) ∘ₗ (φ q).symm.toLinearMap) cp) :
    ∃ q, Nonempty (QuasiSingleStep ρ S (S' q) (σS' q)) := by
  obtain ⟨q, hq⟩ := exists_detectingPrimePlus hex hp0 hcp
  have hcp' : (X q).σV ((φ q).symm cp) = (φ q).symm cp := by
    apply (φ q).injective
    have := LinearMap.congr_fun (hφ q) ((φ q).symm cp)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    rw [LinearEquiv.apply_symm_apply, this, hcp]
  exact ⟨q, ⟨⟨h2, ε, hε, J, hJ2, ep, em, hp, hm, he, X q, hU q, (φ q).symm cp, hcp',
    fun _ => hq hcp, hs1 q, hs0 q, φ q, φ' q, hφ' q⟩⟩⟩

/-- **The mixed-sign step with its duality from Selmer duality** (tex L5068–5122): as
`quasiMixedStep_of_exists`, with the `localPair` duality at every candidate from
`DualityFromSelmer` (symmetric normalization `σ = 1`, cross pairing `ε e₂(·, J ·)`), via
`hU_of_dualityFromSelmer`. PROVED (from the inputs). -/
theorem quasiMixedStep_of_genuine {ι : A →+* F} {ρ : A →+* k} {S : TwoTermStage ι}
    {σS : fiberH1 ρ S →ₗ[k] fiberH1 ρ S} {P : Type} {S' : P → TwoTermStage ι}
    {σS' : ∀ q, fiberH1 ρ (S' q) →ₗ[k] fiberH1 ρ (S' q)}
    (h2 : (2 : k) ≠ 0) (ε : k) (hε : ε ≠ 0) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) (X : P → QuasiQuadSwitch k J)
    (D : ∀ q, DualityFromSelmer (X q).R) (hDε : ∀ q, (D q).ε = ε) (hDσ : ∀ q, (D q).σ = 1)
    (hDJ : ∀ q, Matrix.toLin' (D q).J = J)
    (φ : ∀ q, (selCx (X q).SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S)
    (hφ : ∀ q, (φ q).toLinearMap ∘ₗ (X q).σV = σS ∘ₗ (φ q).toLinearMap)
    (φ' : ∀ q, (selCx (X q).SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ (S' q))
    (hφ' : ∀ q, (φ' q).toLinearMap ∘ₗ (X q).σV' = σS' q ∘ₗ (φ' q).toLinearMap)
    (cp cm : fiberH1 ρ S) (hp0 : cp ≠ 0) (hm0 : cm ≠ 0) (hcp : σS cp = cp) (hcm : σS cm = -cm)
    (hex : DetectingPrimeExists σS (fun q => (X q).R.lamQ ∘ₗ H1 (changeMap (X q).R.D (X q).SF.f₁) ∘ₗ
      (φ q).symm.toLinearMap) cp cm) :
    ∃ q, Nonempty (QuasiMixedStep ρ S (S' q) σS (σS' q)) := by
  refine quasiMixedStep_of_exists h2 ε hε J hJ2 ep em hp hm he X (fun q => ?_) φ hφ φ' hφ'
    cp cm hp0 hm0 hcp hcm hex
  have h := hU_of_dualityFromSelmer (D q) (hDσ q)
  rw [hDε q, hDJ q] at h
  exact h

/-- **The single-sign step with its duality from Selmer duality** (tex L5068–5136). PROVED (from
the inputs). -/
theorem quasiSingleStep_of_genuine {ι : A →+* F} {ρ : A →+* k} {S : TwoTermStage ι}
    {σS : fiberH1 ρ S →ₗ[k] fiberH1 ρ S} {P : Type} {S' : P → TwoTermStage ι}
    {σS' : ∀ q, fiberH1 ρ (S' q) →ₗ[k] fiberH1 ρ (S' q)}
    (h2 : (2 : k) ≠ 0) (ε : k) (hε : ε ≠ 0) (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) (X : P → QuasiQuadSwitch k J)
    (D : ∀ q, DualityFromSelmer (X q).R) (hDε : ∀ q, (D q).ε = ε) (hDσ : ∀ q, (D q).σ = 1)
    (hDJ : ∀ q, Matrix.toLin' (D q).J = J)
    (φ : ∀ q, (selCx (X q).SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S)
    (hφ : ∀ q, (φ q).toLinearMap ∘ₗ (X q).σV = σS ∘ₗ (φ q).toLinearMap)
    (φ' : ∀ q, (selCx (X q).SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ (S' q))
    (hφ' : ∀ q, (φ' q).toLinearMap ∘ₗ (X q).σV' = σS' q ∘ₗ (φ' q).toLinearMap ∨
      (φ' q).toLinearMap ∘ₗ (X q).σV' = (-σS' q) ∘ₗ (φ' q).toLinearMap)
    (hs1 : ∀ q, 1 < finrank k ↥(signPart (X q).σV (1 : k)))
    (hs0 : ∀ q, 0 = finrank k ↥(signPart (X q).σV (-1 : k)))
    (cp : fiberH1 ρ S) (hp0 : cp ≠ 0) (hcp : σS cp = cp)
    (hex : DetectingPrimePlusExists σS (fun q => (X q).R.lamQ ∘ₗ
      H1 (changeMap (X q).R.D (X q).SF.f₁) ∘ₗ (φ q).symm.toLinearMap) cp) :
    ∃ q, Nonempty (QuasiSingleStep ρ S (S' q) (σS' q)) := by
  refine quasiSingleStep_of_exists h2 ε hε J hJ2 ep em hp hm he X (fun q => ?_) φ hφ φ' hφ'
    hs1 hs0 cp hp0 hcp hex
  have h := hU_of_dualityFromSelmer (D q) (hDσ q)
  rw [hDε q, hDJ q] at h
  exact h

end Steps

/-! ### Non-vacuity -/

section NonVacuity

/-- **A genuine quasi diagram involution** with non-trivial involutions (identity on `G`, `J₀` on
`F`, `−J₀` on `S` and on `L`): NonVacuityGenuine's `exDiagramInvolution` on the quasi sides. -/
def exQuasiDiagramInvolution :
    QuasiDiagramInvolution exRel.toQuasi exSideF.toQuasi exSideS.toQuasi :=
  exDiagramInvolution.toQuasi

/-- **The `QuasiQuadSwitch` of the quasi diagram involution** (`toQuasiQuadSwitch`, with the side
clauses derived from the relaxed clause): the switch with both signs of `exQuadSwitchA`. -/
def exQuasiDiagramSwitch : QuasiQuadSwitch ℚ J₀L :=
  exQuasiDiagramInvolution.toQuasiQuadSwitch J₀L exDiagramSwitch.fin_V exDiagramSwitch.fin_V'
    exDiagramSwitch.eK exDiagramSwitch.hα''
    (by rw [RelaxedLocalization.toQuasi_lamQ]; exact exDiagramSwitch.hl)

/-- The bridge on the example: `U = F` with `switchPairing 1 1 J₀` gives the `localPair` form
for `localPair 1 J₀`. PROVED. -/
theorem exBridge :
    ∀ u, u ∈ exRel.toQuasi.U ↔ ∀ w ∈ exRel.toQuasi.U, localPair (1 : ℚ) J₀L u w = 0 := by
  rw [RelaxedLocalization.toQuasi_U, exRel_U]
  exact hU_of_localizationDuality 1 J₀ one_ne_zero J₀_sq _
    (exLocalizationDuality 1 1 one_ne_zero one_ne_zero J₀ J₀_sq)

/-- **The detecting-prime constructor reproduces any homology-level mixed step** (one candidate
prime): the fixed-prime detection of `M` gives the existence form, and `quasiMixedStep_of_exists`
rebuilds a step from `M`'s data. PROVED. -/
theorem quasiMixedStep_of_exists_self {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]
    {ι : A →+* F} {ρ : A →+* k} {S S' : TwoTermStage ι} {σS : fiberH1 ρ S →ₗ[k] fiberH1 ρ S}
    {σS' : fiberH1 ρ S' →ₗ[k] fiberH1 ρ S'} (M : QuasiMixedStep ρ S S' σS σS') :
    ∃ _ : Unit, Nonempty (QuasiMixedStep ρ S S' σS σS') := by
  obtain ⟨hl1, hl2⟩ := M.hdet M.hcp M.hcm
  have hcp0 : M.cp ≠ 0 := fun h => hl1 (by rw [h, map_zero])
  have hcm0 : M.cm ≠ 0 := fun h => hl2 (by rw [h, map_zero])
  have hφa : ∀ x, σS (M.φ x) = M.φ (M.X.σV x) := fun x =>
    (LinearMap.congr_fun M.hφ x).symm
  refine quasiMixedStep_of_exists (P := Unit) (S' := fun _ => S') (σS' := fun _ => σS') M.h2 M.ε
    M.hε M.J M.hJ2 M.ep M.em M.hp M.hm M.he (fun _ => M.X) (fun _ => M.hU) (fun _ => M.φ)
    (fun _ => M.hφ) (fun _ => M.φ') (fun _ => M.hφ') (M.φ M.cp) (M.φ M.cm)
    (fun h => hcp0 (M.φ.injective (by rw [h, map_zero])))
    (fun h => hcm0 (M.φ.injective (by rw [h, map_zero])))
    (by rw [hφa, M.hcp]) (by rw [hφa, M.hcm, map_neg])
    (detectingPrimeExists_of_fixed () fun _ _ => ?_)
  have e1 : M.φ.symm (M.φ M.cp) = M.cp := M.φ.symm_apply_apply _
  have e2 : M.φ.symm (M.φ M.cm) = M.cm := M.φ.symm_apply_apply _
  exact ⟨fun h => hl1 (by rw [← e1]; exact h), fun h => hl2 (by rw [← e2]; exact h)⟩

/-- **Non-vacuity of the detecting-prime constructor**: applied to the homology-level mixed step
`exQuasiMixedStep` (genuine involutions with both signs). PROVED. -/
theorem exQuasiMixedStep_of_exists (u u' : ℚ) :
    ∃ (σS : _) (σS' : _), ∃ _ : Unit,
      Nonempty (QuasiMixedStep (RingHom.id ℚ) (exStage3 u) (exStage1 u') σS σS') :=
  ⟨_, _, quasiMixedStep_of_exists_self (exQuasiMixedStep u u')⟩

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
