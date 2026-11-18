import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GaloisFamily
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuityModelQuad
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SwitchAdjunction

/-!
# RC53 SwitchInputs: homology-level switch steps over genuine fibres

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex L4976–5195), with the switch
exact sequences (5.5a) (tex L5055–5086) and the localization duality (tex L5068–5075).

`GaloisFamily.lean` found that the step bundles of `SwitchData.lean` (`NonquadModelStep` and the
`SelmerQuad*Step`s through `SelmerQuadSwitch`) demand finite-dimensional COCHAIN modules
(`fG : FiniteDimensional k (R.D.G.X 1)`, `fL`, `fF`, `fS`). For the genuine continuous-cochain
Selmer complexes (`galoisSelData`) these modules are infinite-dimensional, so those bundles cannot be
inhabited by genuine fibres. This file gives HOMOLOGY-LEVEL step bundles, which only ask for
finiteness of the cohomology `H¹` (finiteness of Galois cohomology), on the quasi switch sides of
`QuasiSide.lean` (quotient local conditions only quasi-isomorphic to degree one):

* exactness of the switch sequences on `H¹` for quasi sides (`QuasiSwitchSide.h1_exact`,
  `range_gamma`, `range_alpha`, `lam_gamma_F/S`, `range_alpha_F/S`) — PROVED from the
  change-of-condition short exact sequences;
* `DualityFromSelmer` — the inputs of the other team's PROVED
  `ZInQ.Manuscript.RC.SelmerComplex.switchAdjunctionFromDuality_proof` (Selmer pairing data `Q` with
  trace, the 6.3.4 quasi-isomorphism `hγ` — discharged by their `adjunction_of_prints` for a finite
  residue field — and the ELLIOT coordinate-pairing identity `hsw`, tex 2816–2818); it gives
  `LocalizationDualityInput` for the actual relaxed image (`DualityFromSelmer.duality`), replacing the
  GLUE `SwitchDualityAdjunction` / `TiedSwitchDualityAdjunction` of `QuasiSide.lean` /
  `TiedDuality.lean`;
* `QuasiNonquadStep` → `NonquadDims` of the stage fibre dimensions (`toNonquadDims`), with no cochain
  finiteness;
* `QuasiQuadSwitch` → `QuadMixedDims` / `QuadSingleDims` (`toQuadMixedDims`, `toQuadSingleDims`),
  the cohomology-level analogue of `SelmerQuadSwitch` (finiteness only of the two side `H¹`);
* `GaloisSwitchData Φ ι ρ u` — the variant of `GenuineSwitchData` (`GenuineSwitch.lean`, same
  configuration family `Φ` as a parameter, e.g. `galoisSwitchFamily` with genuine `galoisSelData`
  fibres) whose steps are these homology-level bundles, sides tied to the configurations' fibres;
  `toHeightOneSwitchData` and `regular_of_galoisSwitchData'` (regularity, via UniformSwitch's
  `regular_of_switchData`).

Remaining GLUE (in the types where consumed): the stage homotopy equivalences
`C(fibre c) ≃ [k^{n+1} → k^{n+1}]`; the identification of the genuine derivative local conditions
with the quasi sides (the side complexes are tied to the fibres by `hF`, `hS`); `hγ`/`hsw` of
`DualityFromSelmer`; in the quadratic steps the duality in the `localPair` form `hU` (the bridge from
the switch-pairing form of `LocalizationDualityInput` is not written), the involutions on the four
cohomology groups (supplied on genuine complexes by `GaloisInvolution.lean` +
`LocalJ.hloc_of_cocycleRep`, not wired here), `DetectingPrime(Plus)`; and `CoordStep`.
No name clash: the other team's `GenuineSwitch` lives in `ZInQ.Manuscript.RC.SelmerComplex`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.UniformSwitch
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.Uniform.QuadraticCase

/-! ### Exactness of the switch sequences on `H¹` for quasi sides -/

section QuasiExact

variable {k : Type} [Field k]

/-- The relaxed localization `λ = e_R ∘ H¹(C_rel → W_rel)` of a quasi relaxed localization. -/
def QuasiRelaxedLocalization.lamQ (R : QuasiRelaxedLocalization k) :
    (selCx R.D).toCC.homology 1 →ₗ[k] (Fin 2 → k) × (Fin 2 → k) :=
  R.eR.toLinearMap ∘ₗ H1 (quotMap R.D R.gR)

theorem QuasiRelaxedLocalization.range_lamQ (R : QuasiRelaxedLocalization k) :
    LinearMap.range R.lamQ = R.U := by
  rw [QuasiRelaxedLocalization.lamQ, LinearMap.range_comp]; rfl

variable {R : QuasiRelaxedLocalization k} {P : Submodule k ((Fin 2 → k) × (Fin 2 → k))}

/-- **Exactness on `H¹` for a quasi side** (tex L5076–5083): `H¹(C_str) → H¹(C(U₁))` is injective,
its image is the kernel of `H¹(C(U₁) → W₁)`, and the image of `H¹(C(U₁)) → H¹(C_rel)` is the kernel
of `H¹(C_rel → W₂)`. PROVED from the two short exact sequences and `H⁰(W₁) = 0`. -/
theorem QuasiSwitchSide.h1_exact (S : QuasiSwitchSide R P) :
    Function.Injective (H1 (changeMap S.Dside S.fs)) ∧
    LinearMap.range (H1 (changeMap S.Dside S.fs)) = LinearMap.ker (H1 (quotMap S.Dside S.g₁)) ∧
    LinearMap.range (H1 (changeMap R.D S.f₁)) = LinearMap.ker (H1 (quotMap R.D S.g₂)) := by
  have h1 := S.ses₁
  have h2 := S.ses₂
  refine ⟨?_, (h1.homology_exact₂ 1).moduleCat_range_eq_ker,
    (h2.homology_exact₂ 1).moduleCat_range_eq_ker⟩
  have h0 : Subsingleton ((changeSES S.Dside S.fs S.g₁ S.hfg₁).X₃.homology 0) := S.h0
  have mono1 : Mono (HomologicalComplex.homologyMap (changeSES S.Dside S.fs S.g₁ S.hfg₁).f 1) :=
    (h1.homology_exact₁ 0 1 (by simp)).mono_g
      ((@Limits.IsZero.of_iso _ _ _ _ (ModuleCat.isZero_of_subsingleton _) (Iso.refl _)).eq_of_src
        _ _)
  exact (ModuleCat.mono_iff_injective _).mp mono1

theorem QuasiSwitchSide.H1_comm (S : QuasiSwitchSide R P) (v : (selCx S.Dside).toCC.homology 1) :
    H1 (quotMap R.D R.gR) (H1 (changeMap R.D S.f₁) v) = H1 S.i (H1 (quotMap S.Dside S.g₁) v) := by
  calc H1 (quotMap R.D R.gR) (H1 (changeMap R.D S.f₁) v)
      = (HomologicalComplex.homologyMap
          (GHom.toCC (changeMap R.D S.f₁) ≫ GHom.toCC (quotMap R.D R.gR)) 1).hom v := by
        rw [HomologicalComplex.homologyMap_comp]; rfl
    _ = (HomologicalComplex.homologyMap
          (GHom.toCC (quotMap S.Dside S.g₁) ≫ GHom.toCC S.i) 1).hom v :=
        congrArg (fun f => ModuleCat.Hom.hom (HomologicalComplex.homologyMap f 1) v) S.comm_lam
    _ = H1 S.i (H1 (quotMap S.Dside S.g₁) v) := by
        rw [HomologicalComplex.homologyMap_comp]; rfl

theorem QuasiSwitchSide.H1_fac (S : QuasiSwitchSide R P) (v : (selCx R.D).toCC.homology 1) :
    H1 (quotMap R.D S.g₂) v = H1 S.p (H1 (quotMap R.D R.gR) v) := by
  calc H1 (quotMap R.D S.g₂) v
      = (HomologicalComplex.homologyMap
          (GHom.toCC (quotMap R.D R.gR) ≫ GHom.toCC S.p) 1).hom v := by
        rw [S.fac_p]
    _ = H1 S.p (H1 (quotMap R.D R.gR) v) := by
        rw [HomologicalComplex.homologyMap_comp]; rfl

/-- **The image of the side in `H¹(C_rel)`** (tex L5080–5083): if `P = ker π`, then
`im(H¹(C(U₁)) → H¹(C_rel)) = ker(π ∘ λ)`. PROVED. -/
theorem QuasiSwitchSide.range_gamma (S : QuasiSwitchSide R P)
    (π : (Fin 2 → k) × (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (hπ : ∀ z, z ∈ P ↔ π z = 0) :
    LinearMap.range (H1 (changeMap R.D S.f₁)) = LinearMap.ker (π ∘ₗ R.lamQ) := by
  have key : ∀ z, z ∈ P ↔ z ∈ (LinearMap.range (H1 S.i)).map R.eR.toLinearMap := fun z => by
    rw [S.hP]
  rw [S.h1_exact.2.2]
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, S.H1_fac, LinearMap.comp_apply]
  have hlam : R.lamQ v = R.eR (H1 (quotMap R.D R.gR) v) := rfl
  rw [hlam, ← hπ, key, ← LinearMap.mem_ker, S.hpi]
  constructor
  · intro hy; exact ⟨_, hy, rfl⟩
  · rintro ⟨y', hy', he⟩
    have : y' = H1 (quotMap R.D R.gR) v := R.eR.injective he
    exact this ▸ hy'

/-- The image of the strict condition is the kernel of the relaxed localization on the side. -/
theorem QuasiSwitchSide.range_alpha (S : QuasiSwitchSide R P) :
    LinearMap.range (H1 (changeMap S.Dside S.fs)) =
      LinearMap.ker (R.lamQ ∘ₗ H1 (changeMap R.D S.f₁)) := by
  rw [S.h1_exact.2.1]
  ext v
  simp only [LinearMap.mem_ker]
  change _ ↔ R.eR (H1 (quotMap R.D R.gR) (H1 (changeMap R.D S.f₁) v)) = 0
  rw [S.H1_comm]
  constructor
  · intro h; rw [h, map_zero, map_zero]
  · intro h
    have h' : H1 S.i (H1 (quotMap S.Dside S.g₁) v) = 0 := R.eR.injective (by rw [h, map_zero])
    exact S.hi (by rw [h', map_zero])

/-- The finite localization `β : H¹(C(U_F)) → F = k²` of a quasi finite side. -/
def QuasiSwitchSide.βF (S : QuasiSwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))) :
    (selCx S.Dside).toCC.homology 1 →ₗ[k] (Fin 2 → k) :=
  LinearMap.fst k _ _ ∘ₗ R.lamQ ∘ₗ H1 (changeMap R.D S.f₁)

/-- The singular localization `β' : H¹(C(U_S)) → S = k²` of a quasi singular side. -/
def QuasiSwitchSide.βS (S : QuasiSwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))) :
    (selCx S.Dside).toCC.homology 1 →ₗ[k] (Fin 2 → k) :=
  LinearMap.snd k _ _ ∘ₗ R.lamQ ∘ₗ H1 (changeMap R.D S.f₁)

/-- **The finite localization square** `λ ∘ γ = inl ∘ β`. PROVED. -/
theorem QuasiSwitchSide.lam_gamma_F (S : QuasiSwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))) :
    R.lamQ ∘ₗ H1 (changeMap R.D S.f₁) = inlF ∘ₗ S.βF := by
  have hr := S.range_gamma (LinearMap.snd k _ _) (fun _ => mem_finPlane)
  ext1 v
  have hv : H1 (changeMap R.D S.f₁) v ∈ LinearMap.ker (LinearMap.snd k _ _ ∘ₗ R.lamQ) :=
    hr ▸ LinearMap.mem_range_self _ v
  rw [LinearMap.mem_ker] at hv
  refine Prod.ext rfl ?_
  have h2 : (R.lamQ (H1 (changeMap R.D S.f₁) v)).2 = 0 := by simpa using hv
  exact h2

/-- **The singular localization square** `λ ∘ γ' = inr ∘ β'`. PROVED. -/
theorem QuasiSwitchSide.lam_gamma_S (S : QuasiSwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))) :
    R.lamQ ∘ₗ H1 (changeMap R.D S.f₁) = inrS ∘ₗ S.βS := by
  have hr := S.range_gamma (LinearMap.fst k _ _) (fun _ => mem_singPlane)
  ext1 v
  have hv : H1 (changeMap R.D S.f₁) v ∈ LinearMap.ker (LinearMap.fst k _ _ ∘ₗ R.lamQ) :=
    hr ▸ LinearMap.mem_range_self _ v
  rw [LinearMap.mem_ker] at hv
  refine Prod.ext ?_ rfl
  have h1 : (R.lamQ (H1 (changeMap R.D S.f₁) v)).1 = 0 := by simpa using hv
  exact h1

theorem QuasiSwitchSide.range_alpha_F
    (S : QuasiSwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))) :
    LinearMap.range (H1 (changeMap S.Dside S.fs)) = LinearMap.ker S.βF := by
  rw [S.range_alpha, S.lam_gamma_F]
  ext v
  change inlF (S.βF v) = 0 ↔ S.βF v = 0
  constructor
  · intro h; simpa using congrArg Prod.fst h
  · intro h; rw [h, map_zero]

theorem QuasiSwitchSide.range_alpha_S
    (S : QuasiSwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))) :
    LinearMap.range (H1 (changeMap S.Dside S.fs)) = LinearMap.ker S.βS := by
  rw [S.range_alpha, S.lam_gamma_S]
  ext v
  change inrS (S.βS v) = 0 ↔ S.βS v = 0
  constructor
  · intro h; simpa using congrArg Prod.snd h
  · intro h; rw [h, map_zero]

end QuasiExact

/-! ### The localization duality from Selmer duality -/

section Duality

variable {k : Type} [Field k]

/-- **The inputs of the switch duality adjunction from Selmer duality** (tex L5068–5075): the strict
condition `f : U_str → U_rel` of the relaxed localization with quotient `W_rel`, Selmer pairing data
`Q` between `C_str` and `C_rel` with a trace killing coboundaries, the 6.3.4 quasi-isomorphism `hγ`
(PRINT-level: the other team's `adjunction_of_prints`, from `NekovarProp543` and
`OrthogonalComplements` at a finite residue field) and the coordinate-pairing identity `hsw`
(ELLIOT, tex 2816–2818). These are exactly the hypotheses of the other team's PROVED
`switchAdjunctionFromDuality_proof`. -/
structure DualityFromSelmer (R : QuasiRelaxedLocalization k) where
  Ustr : GCx k
  f : GHom Ustr R.D.U
  hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0
  hf : ∀ n, Function.Injective (f.f n n rfl)
  hg : ∀ n, Function.Surjective (R.gR.f n n rfl)
  hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u
  Q : SelPairData (restrictData R.D f) R.D
  tr : (coneCx Q.resE).X 3 →ₗ[k] k
  htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0
  ε : k
  σ : k
  J : Matrix (Fin 2) (Fin 2) k
  hε : ε ≠ 0
  hσ : σ ≠ 0
  hJ2 : J * J = 1
  hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr))
  hsw : ∀ (t u : R.D.U.X 1) (s : Ustr.X 2) (_ht : R.D.U.d 1 2 rfl t = 0)
      (_hu : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s) (ct cu : LinearMap.ker (R.Wrel.d 1 2 rfl))
      (_hct : ct.1 = R.gR.f 1 1 rfl t) (_hcu : cu.1 = R.gR.f 1 1 rfl u),
    tr (selCupFun Q 2 1 3 rfl ((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u))
        ((0 : R.D.G.X 1), t, (0 : R.D.L.X (1 - 1)))) =
      switchPairing ε σ J (R.eR (ZInQ.Manuscript.RC.SelmerComplex.cls1 R.Wrel ct))
        (R.eR (ZInQ.Manuscript.RC.SelmerComplex.cls1 R.Wrel cu))

/-- **`LocalizationDualityInput` for the actual relaxed image from Selmer duality** (tex L5068–5075):
the other team's `switchAdjunctionFromDuality_proof` gives `SwitchDualityAdjunction` for the genuine
connecting map, and `localizationDualityInput_of_adjunction` gives `U = U^⊥`. PROVED (from the
inputs of `DualityFromSelmer`). -/
theorem DualityFromSelmer.duality {R : QuasiRelaxedLocalization k} (D : DualityFromSelmer R) :
    LocalizationDualityInput D.ε D.σ D.J D.hε D.hσ D.hJ2 R.U :=
  localizationDualityInput_of_adjunction R (restrictData R.D D.f) D.ε D.σ D.J D.hε D.hσ D.hJ2 _ _
    (ZInQ.Manuscript.RC.SelmerComplex.switchAdjunctionFromDuality_proof k R D.Ustr D.f D.hfg D.hf
      D.hg D.hex D.Q D.tr D.htr D.ε D.σ D.J D.hε D.hσ D.hJ2 D.hγ D.hsw)

end Duality

/-! ### Homology-level step bundles -/

section Steps

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- **A homology-level nonquadratic switch step** (tex L4997–5003, L5055–5086): a quasi relaxed
localization with finite and singular quasi sides, equal strict `H¹`-dimensions on the two sides
(the shared strict condition, tex L5072–5083), the localization duality `U = U^⊥` (filled from Selmer
duality by `QuasiNonquadStep.ofSelmerDuality`, i.e. by the other team's adjunction theorem),
rank-two detection `F ≤ U`, and isomorphisms of the side `H¹`s with the stage fibres. No cochain
finiteness. -/
structure QuasiNonquadStep {ι : A →+* F} (ρ : A →+* k) (S S' : TwoTermStage ι) where
  R : QuasiRelaxedLocalization k
  SF : QuasiSwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))
  SS : QuasiSwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))
  hk0 : finrank k ((selCx SF.Dstr).toCC.homology 1) = finrank k ((selCx SS.Dstr).toCC.homology 1)
  ε : k
  σ : k
  J : Matrix (Fin 2) (Fin 2) k
  hε : ε ≠ 0
  hσ : σ ≠ 0
  hJ2 : J * J = 1
  hdual : LocalizationDualityInput ε σ J hε hσ hJ2 R.U
  hdet : finPlane k (Fin 2 → k) (Fin 2 → k) ≤ R.U
  φ : (selCx SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S
  φ' : (selCx SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S'

/-- **`NonquadDims` of the stage fibre dimensions from a homology-level step** (tex L4997–5003):
`U = F` from the duality (via the other team's adjunction theorem) and detection
(`relaxedImageFinite_proof`); the two (5.5a) equations from `quasiSwitchSideDims_of_h1Finite`, with
finiteness of the side `H¹` from the fibre isomorphisms. PROVED (from the step's inputs). -/
def QuasiNonquadStep.toNonquadDims {ι : A →+* F} {ρ : A →+* k} {S S' : TwoTermStage ι}
    (X : QuasiNonquadStep ρ S S') : NonquadDims (k := k) (S.fiberDim ρ) (S'.fiberDim ρ) where
  U := X.R.U
  hU := relaxedImageFinite_proof k X.ε X.σ X.J X.hε X.hσ X.hJ2 X.R.U X.hdual X.hdet
  k0 := finrank k ((selCx X.SF.Dstr).toCC.homology 1)
  hs := by
    have := fiberH1_finite ρ S
    have : FiniteDimensional k ((selCx X.SF.Dside).toCC.homology 1) :=
      LinearEquiv.finiteDimensional X.φ.symm
    rw [fiberDim_eq_of_h1Equiv ρ S X.φ]
    exact quasiSwitchSideDims_of_h1Finite X.R _ X.SF inferInstance
  hs' := by
    have := fiberH1_finite ρ S'
    have : FiniteDimensional k ((selCx X.SS.Dside).toCC.homology 1) :=
      LinearEquiv.finiteDimensional X.φ'.symm
    rw [fiberDim_eq_of_h1Equiv ρ S' X.φ', X.hk0]
    exact quasiSwitchSideDims_of_h1Finite X.R _ X.SS inferInstance

/-- **The nonquadratic step with its duality from Selmer duality** (tex L5068–5075): the duality
field is supplied by `DualityFromSelmer.duality` (the other team's `switchAdjunctionFromDuality_proof`
and `localizationDualityInput_of_adjunction`). PROVED. -/
def QuasiNonquadStep.ofSelmerDuality {ι : A →+* F} {ρ : A →+* k} {S S' : TwoTermStage ι}
    (R : QuasiRelaxedLocalization k) (SF : QuasiSwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k)))
    (SS : QuasiSwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k)))
    (hk0 : finrank k ((selCx SF.Dstr).toCC.homology 1) = finrank k ((selCx SS.Dstr).toCC.homology 1))
    (D : DualityFromSelmer R) (hdet : finPlane k (Fin 2 → k) (Fin 2 → k) ≤ R.U)
    (φ : (selCx SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S)
    (φ' : (selCx SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S') : QuasiNonquadStep ρ S S' :=
  ⟨R, SF, SS, hk0, D.ε, D.σ, D.J, D.hε, D.hσ, D.hJ2, D.duality, hdet, φ, φ'⟩

/-- **The homology-level quadratic switch data** (tex L5003–5122): the cohomology-level analogue of
`SelmerQuadSwitch` over quasi sides — finiteness only of the two side `H¹`s, the strict
identification `eK`, and the involutions on the four cohomology groups with their compatibilities
with the actual switch maps (`β`, `γ`, `λ` defined from the quasi sides). -/
structure QuasiQuadSwitch (k : Type) [Field k] (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) where
  R : QuasiRelaxedLocalization k
  SF : QuasiSwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))
  SS : QuasiSwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))
  fV : FiniteDimensional k ((selCx SF.Dside).toCC.homology 1)
  fV' : FiniteDimensional k ((selCx SS.Dside).toCC.homology 1)
  eK : (selCx SS.Dstr).toCC.homology 1 ≃ₗ[k] (selCx SF.Dstr).toCC.homology 1
  σK : (selCx SF.Dstr).toCC.homology 1 →ₗ[k] (selCx SF.Dstr).toCC.homology 1
  σV : (selCx SF.Dside).toCC.homology 1 →ₗ[k] (selCx SF.Dside).toCC.homology 1
  σV' : (selCx SS.Dside).toCC.homology 1 →ₗ[k] (selCx SS.Dside).toCC.homology 1
  σr : (selCx R.D).toCC.homology 1 →ₗ[k] (selCx R.D).toCC.homology 1
  hK : σK ∘ₗ σK = LinearMap.id
  hV : σV ∘ₗ σV = LinearMap.id
  hV' : σV' ∘ₗ σV' = LinearMap.id
  hr : σr ∘ₗ σr = LinearMap.id
  hα' : H1 (changeMap SF.Dside SF.fs) ∘ₗ σK = σV ∘ₗ H1 (changeMap SF.Dside SF.fs)
  hβ' : SF.βF ∘ₗ σV = J ∘ₗ SF.βF
  hγ' : H1 (changeMap R.D SF.f₁) ∘ₗ σV = σr ∘ₗ H1 (changeMap R.D SF.f₁)
  hα'' : (H1 (changeMap SS.Dside SS.fs) ∘ₗ eK.symm.toLinearMap) ∘ₗ σK =
    σV' ∘ₗ (H1 (changeMap SS.Dside SS.fs) ∘ₗ eK.symm.toLinearMap)
  hβ'' : SS.βS ∘ₗ σV' = (-J) ∘ₗ SS.βS
  hγ'' : H1 (changeMap R.D SS.f₁) ∘ₗ σV' = σr ∘ₗ H1 (changeMap R.D SS.f₁)
  hl : R.lamQ ∘ₗ σr = localInv J ∘ₗ R.lamQ

variable {J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)}

theorem QuasiQuadSwitch.alphaS_inj (X : QuasiQuadSwitch k J) :
    Function.Injective (H1 (changeMap X.SS.Dside X.SS.fs) ∘ₗ X.eK.symm.toLinearMap) :=
  X.SS.h1_exact.1.comp X.eK.symm.injective

theorem QuasiQuadSwitch.alphaS_range (X : QuasiQuadSwitch k J) :
    LinearMap.range (H1 (changeMap X.SS.Dside X.SS.fs) ∘ₗ X.eK.symm.toLinearMap) =
      LinearMap.ker X.SS.βS :=
  (LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range X.eK.symm)).trans
    X.SS.range_alpha_S

/-- **Mixed-sign `QuadMixedDims` from homology-level data** (tex L5003–5122): all exactness inputs of
`quadMixedDimsOfInputs` PROVED from the quasi sides; duality (`hU`, GLUE) and `DetectingPrime`
(GLUE) in the type. -/
noncomputable def QuasiQuadSwitch.toQuadMixedDims (X : QuasiQuadSwitch k J) (h2 : (2 : k) ≠ 0)
    (ε : k) (hε : ε ≠ 0) (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k) (hp : J ep = ep)
    (hm : J em = -em) (he : e₂ ep em ≠ 0)
    (hU : ∀ u, u ∈ X.R.U ↔ ∀ w ∈ X.R.U, localPair ε J u w = 0)
    (cp cm : (selCx X.SF.Dside).toCC.homology 1) (hcp : X.σV cp = cp) (hcm : X.σV cm = -cm)
    (hdet : DetectingPrime X.σV (X.R.lamQ ∘ₗ H1 (changeMap X.R.D X.SF.f₁)) cp cm) :
    QuadMixedDims (k := k) (finrank k ↥(signPart X.σV (1 : k))) (finrank k ↥(signPart X.σV (-1 : k)))
      (finrank k ↥(signPart X.σV' (1 : k))) (finrank k ↥(signPart X.σV' (-1 : k))) :=
  haveI := X.fV
  haveI := X.fV'
  quadMixedDimsOfInputs h2 ε hε J hJ2 ep em hp hm he
    (H1 (changeMap X.SF.Dside X.SF.fs)) X.SF.βF (H1 (changeMap X.R.D X.SF.f₁))
    (H1 (changeMap X.SS.Dside X.SS.fs) ∘ₗ X.eK.symm.toLinearMap) X.SS.βS
    (H1 (changeMap X.R.D X.SS.f₁)) X.R.lamQ X.σK X.σV X.σV' X.σr X.hK X.hV X.hV' X.hr
    X.hα' X.hβ' X.hγ' X.hα'' X.hβ'' X.hγ'' X.hl
    X.SF.h1_exact.1 X.SF.range_alpha_F
    (X.SF.range_gamma (LinearMap.snd k _ _) (fun _ => mem_finPlane)) X.SF.lam_gamma_F
    X.alphaS_inj X.alphaS_range
    (X.SS.range_gamma (LinearMap.fst k _ _) (fun _ => mem_singPlane)) X.SS.lam_gamma_S
    (fun u => by rw [X.R.range_lamQ]; exact hU u) cp cm hcp hcm hdet _ _ _ _ rfl rfl rfl rfl

/-- **Single-sign `QuadSingleDims` from homology-level data** (tex L5123–5136). -/
noncomputable def QuasiQuadSwitch.toQuadSingleDims (X : QuasiQuadSwitch k J) (h2 : (2 : k) ≠ 0)
    (ε : k) (hε : ε ≠ 0) (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k) (hp : J ep = ep)
    (hm : J em = -em) (he : e₂ ep em ≠ 0)
    (hU : ∀ u, u ∈ X.R.U ↔ ∀ w ∈ X.R.U, localPair ε J u w = 0)
    (cp : (selCx X.SF.Dside).toCC.homology 1) (hcp : X.σV cp = cp)
    (hdet : DetectingPrimePlus X.σV (X.R.lamQ ∘ₗ H1 (changeMap X.R.D X.SF.f₁)) cp)
    (hs1 : 1 < finrank k ↥(signPart X.σV (1 : k)))
    (hs0 : 0 = finrank k ↥(signPart X.σV (-1 : k))) :
    QuadSingleDims (k := k) (finrank k ↥(signPart X.σV (1 : k)))
      (finrank k ↥(signPart X.σV' (1 : k))) (finrank k ↥(signPart X.σV' (-1 : k))) :=
  haveI := X.fV
  haveI := X.fV'
  quadSingleDimsOfInputs h2 ε hε J hJ2 ep em hp hm he
    (H1 (changeMap X.SF.Dside X.SF.fs)) X.SF.βF (H1 (changeMap X.R.D X.SF.f₁))
    (H1 (changeMap X.SS.Dside X.SS.fs) ∘ₗ X.eK.symm.toLinearMap) X.SS.βS
    (H1 (changeMap X.R.D X.SS.f₁)) X.R.lamQ X.σK X.σV X.σV' X.σr X.hK X.hV X.hV' X.hr
    X.hα' X.hβ' X.hγ' X.hα'' X.hβ'' X.hγ'' X.hl
    X.SF.h1_exact.1 X.SF.range_alpha_F
    (X.SF.range_gamma (LinearMap.snd k _ _) (fun _ => mem_finPlane)) X.SF.lam_gamma_F
    X.alphaS_inj X.alphaS_range
    (X.SS.range_gamma (LinearMap.fst k _ _) (fun _ => mem_singPlane)) X.SS.lam_gamma_S
    (fun u => by rw [X.R.range_lamQ]; exact hU u) cp hcp hdet _ _ _ hs1 rfl hs0 rfl rfl

/-- **A homology-level mixed-sign step** between stages `S`, `S'` with fibre involutions
`σS`, `σS'`: the quadratic data, the switch data `X`, duality in the `localPair` form (GLUE),
detecting classes (GLUE `DetectingPrime`), and equivariant fibre isomorphisms. -/
structure QuasiMixedStep {ι : A →+* F} (ρ : A →+* k) (S S' : TwoTermStage ι)
    (σS : fiberH1 ρ S →ₗ[k] fiberH1 ρ S) (σS' : fiberH1 ρ S' →ₗ[k] fiberH1 ρ S') where
  h2 : (2 : k) ≠ 0
  ε : k
  hε : ε ≠ 0
  J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)
  hJ2 : J ∘ₗ J = LinearMap.id
  ep : Fin 2 → k
  em : Fin 2 → k
  hp : J ep = ep
  hm : J em = -em
  he : e₂ ep em ≠ 0
  X : QuasiQuadSwitch k J
  hU : ∀ u, u ∈ X.R.U ↔ ∀ w ∈ X.R.U, localPair ε J u w = 0
  cp : (selCx X.SF.Dside).toCC.homology 1
  cm : (selCx X.SF.Dside).toCC.homology 1
  hcp : X.σV cp = cp
  hcm : X.σV cm = -cm
  hdet : DetectingPrime X.σV (X.R.lamQ ∘ₗ H1 (changeMap X.R.D X.SF.f₁)) cp cm
  φ : (selCx X.SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S
  hφ : φ.toLinearMap ∘ₗ X.σV = σS ∘ₗ φ.toLinearMap
  φ' : (selCx X.SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S'
  hφ' : φ'.toLinearMap ∘ₗ X.σV' = σS' ∘ₗ φ'.toLinearMap

/-- **A homology-level single-sign step**. -/
structure QuasiSingleStep {ι : A →+* F} (ρ : A →+* k) (S S' : TwoTermStage ι)
    (σS' : fiberH1 ρ S' →ₗ[k] fiberH1 ρ S') where
  h2 : (2 : k) ≠ 0
  ε : k
  hε : ε ≠ 0
  J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)
  hJ2 : J ∘ₗ J = LinearMap.id
  ep : Fin 2 → k
  em : Fin 2 → k
  hp : J ep = ep
  hm : J em = -em
  he : e₂ ep em ≠ 0
  X : QuasiQuadSwitch k J
  hU : ∀ u, u ∈ X.R.U ↔ ∀ w ∈ X.R.U, localPair ε J u w = 0
  cp : (selCx X.SF.Dside).toCC.homology 1
  hcp : X.σV cp = cp
  hdet : DetectingPrimePlus X.σV (X.R.lamQ ∘ₗ H1 (changeMap X.R.D X.SF.f₁)) cp
  hs1 : 1 < finrank k ↥(signPart X.σV (1 : k))
  hs0 : 0 = finrank k ↥(signPart X.σV (-1 : k))
  φ : (selCx X.SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S
  φ' : (selCx X.SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S'
  hφ' : φ'.toLinearMap ∘ₗ X.σV' = σS' ∘ₗ φ'.toLinearMap ∨
    φ'.toLinearMap ∘ₗ X.σV' = (-σS') ∘ₗ φ'.toLinearMap

end Steps

/-! ### Galois switching data with homology-level steps -/

section Galois

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- **Galois height-one switching data** (tex L4976–5195) over a fixed configuration family `Φ`
(e.g. `galoisSwitchFamily`, fibres the genuine `galoisSelData`), for the actual coordinate `u`: as
`GenuineSwitchData` (stages are the fibre models, the start carries the actual class, functional
and coordinate, the switches follow the configuration sequence), but every switch step is a
homology-level bundle whose side complexes ARE the configurations' fibres (`hF`, `hS`). -/
structure GaloisSwitchData (Φ : SwitchFamily k A) (ι : A →+* F) (ρ : A →+* k) (u : F) where
  stage : Φ.Config → TwoTermStage ι
  model : ∀ c, HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex ρ (stage c))
  hz0 : ((model Φ.actual).hom.f 1).hom Φ.zAct = fun i => ρ ((stage Φ.actual).z i)
  hw0 : ∀ y, Φ.lamAct y =
    (fun i => ρ ((stage Φ.actual).w i)) ⬝ᵥ (((model Φ.actual).hom.f 2).hom y : Fin _ → k)
  hu0 : (stage Φ.actual).u = u
  σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c)
  h2 : Φ.quadratic ρ → (2 : k) ≠ 0
  hσ : Φ.quadratic ρ → ∀ c, σ c ∘ₗ σ c = LinearMap.id
  primitive : ∀ c, Reach Φ.next Φ.actual c → ∃ i, ρ ((stage c).z i) ≠ 0
  switch_mixed : ∀ c, Reach Φ.next Φ.actual c → (¬ Φ.quadratic ρ ∨
      (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k)))) →
    1 < (stage c).fiberDim ρ →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      (Φ.quadratic ρ → ∃ M : QuasiMixedStep ρ (stage c) (stage (Φ.next c p)) (σ c)
          (σ (Φ.next c p)), M.X.SF.Dside = Φ.fibre c ∧ M.X.SS.Dside = Φ.fibre (Φ.next c p)) ∧
      (¬ Φ.quadratic ρ → ∃ N : QuasiNonquadStep ρ (stage c) (stage (Φ.next c p)),
          N.SF.Dside = Φ.fibre c ∧ N.SS.Dside = Φ.fibre (Φ.next c p))
  switch_single : ∀ c, Reach Φ.next Φ.actual c → Φ.quadratic ρ →
    ¬ (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k))) →
    1 < (stage c).fiberDim ρ →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ M : QuasiSingleStep ρ (stage c) (stage (Φ.next c p)) (σ (Φ.next c p)),
        M.X.SF.Dside = Φ.fibre c ∧ M.X.SS.Dside = Φ.fibre (Φ.next c p)

variable {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- **Every stage fibre dimension is the genuine `H¹`-dimension of its configuration**. PROVED. -/
theorem GaloisSwitchData.fiberDim_eq (G : GaloisSwitchData Φ ι ρ u) (c : Φ.Config) :
    (G.stage c).fiberDim ρ = finrank k ((selCx (Φ.fibre c)).toCC.homology 1) :=
  fiberDim_eq_h1 k A F ι ρ (G.stage c) (Φ.fibre c) ⟨G.model c⟩

/-- **The collapse forces the genuine fibre** (truth check): if the actual stage has fibre dimension
`1`, the genuine `H¹` of the actual configuration has dimension `1`. PROVED. -/
theorem GaloisSwitchData.collapse_forces (G : GaloisSwitchData Φ ι ρ u)
    (h1 : (G.stage Φ.actual).fiberDim ρ = 1) :
    finrank k ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) = 1 := by
  rw [← G.fiberDim_eq Φ.actual, h1]

/-- **The height-one switching data from Galois switching data** (tex L4976–5195): UniformSwitch's
`HeightOneSwitchData` on the configurations, with `sp, sm` the sign dimensions of the stage
involutions; `sign_sum` from the involution splitting of the fibres; the nonquadratic dimensions
from `QuasiNonquadStep.toNonquadDims`; the quadratic ones from `QuasiQuadSwitch.toQuadMixedDims` /
`toQuadSingleDims` transported along the equivariant fibre isomorphisms. PROVED. -/
noncomputable def GaloisSwitchData.toHeightOneSwitchData (G : GaloisSwitchData Φ ι ρ u) :
    HeightOneSwitchData ι ρ where
  Stage := {c // Reach Φ.next Φ.actual c}
  stage s := G.stage s.1
  quadratic := Φ.quadratic ρ
  sp s := finrank k ↥(signPart (G.σ s.1) (1 : k))
  sm s := finrank k ↥(signPart (G.σ s.1) (-1 : k))
  sign_sum q s := by
    have := fiberH1_finite ρ (G.stage s.1)
    rw [← finrank_h1_twoTermFiberComplex ρ (G.stage s.1),
      (involutionSplitting_proof k _ (G.σ s.1) (G.h2 q) (G.hσ q s.1)).2.2 this,
      signPart_one_eq_plusPart, signPart_neg_one_eq_minusPart]
  primitive s := G.primitive s.1 s.2
  switch_mixed s h1 h2 := by
    obtain ⟨p, hc, hq, hn⟩ := G.switch_mixed s.1 s.2 h1 h2
    refine ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, hc, fun q => ?_, fun nq => ?_⟩
    · obtain ⟨M, -, -⟩ := hq q
      exact ⟨QuadMixedDims.cast' (M.X.toQuadMixedDims M.h2 M.ε M.hε M.hJ2 M.ep M.em M.hp M.hm M.he
        M.hU M.cp M.cm M.hcp M.hcm M.hdet)
        (finrank_signPart_of_equiv M.φ M.hφ 1).symm (finrank_signPart_of_equiv M.φ M.hφ (-1)).symm
        (finrank_signPart_of_equiv M.φ' M.hφ' 1).symm
        (finrank_signPart_of_equiv M.φ' M.hφ' (-1)).symm⟩
    · obtain ⟨N, -, -⟩ := hn nq
      exact ⟨N.toNonquadDims⟩
  switch_single s q h1 h2 := by
    obtain ⟨p, hc, M, -, -⟩ := G.switch_single s.1 s.2 q h1 h2
    refine ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, finrank k ↥(signPart M.X.σV' (1 : k)),
      finrank k ↥(signPart M.X.σV' (-1 : k)), hc, ⟨QuadSingleDims.cast'
        (M.X.toQuadSingleDims M.h2 M.ε M.hε M.hJ2 M.ep M.em M.hp M.hm M.he M.hU M.cp M.hcp M.hdet
          M.hs1 M.hs0) ?_ rfl rfl⟩, ?_⟩
    · have hV := M.X.fV
      rw [fiberDim_eq_of_h1Equiv ρ _ M.φ,
        (involutionSplitting_proof k _ M.X.σV M.h2 M.X.hV).2.2 hV,
        signPart_one_eq_plusPart, ← signPart_neg_one_eq_minusPart, ← M.hs0, add_zero]
    · rcases M.hφ' with h | h
      · exact Or.inl ⟨(finrank_signPart_of_equiv M.φ' h 1).symm,
          (finrank_signPart_of_equiv M.φ' h (-1)).symm⟩
      · refine Or.inr ⟨?_, ?_⟩
        · change finrank k ↥(signPart (G.σ (Φ.next s.1 p)) (1 : k)) = _
          rw [finrank_signPart_of_equiv M.φ' h (-1), signPart_neg_eq, neg_neg]
        · change finrank k ↥(signPart (G.σ (Φ.next s.1 p)) (-1 : k)) = _
          rw [finrank_signPart_of_equiv M.φ' h 1, signPart_neg_eq]

/-- **Regularity from Galois switching data** (tex L4976–5195): `u ∈ ι(A)`, through UniformSwitch's
`regular_of_switchData` (RC16's `regular_of_switchProcess`) at the actual configuration.
Classification: PROVED (from the inputs of `GaloisSwitchData`). -/
theorem regular_of_galoisSwitchData' [IsLocalRing A] (hι : Function.Injective ι)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (G : GaloisSwitchData Φ ι ρ u) :
    ∃ a : A, ι a = u := by
  obtain ⟨a, ha⟩ := regular_of_switchData hι hρ G.toHeightOneSwitchData ⟨Φ.actual, Reach.start⟩
  exact ⟨a, ha.trans G.hu0⟩

end Galois

/-! ### The literal (degree-one) bundles are special cases; non-vacuity (LESSON 2) -/

section Literal

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

theorem RelaxedLocalization.toQuasi_lamQ (R : RelaxedLocalization k) : R.toQuasi.lamQ = R.lam :=
  rfl

theorem SwitchSide.toQuasi_βF {R : RelaxedLocalization k}
    (S : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))) : S.toQuasi.βF = S.βF := by
  ext1 v
  exact congrArg (fun f => LinearMap.fst k _ _ (f v)) S.lam_gamma_F

theorem SwitchSide.toQuasi_βS {R : RelaxedLocalization k}
    (S : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))) : S.toQuasi.βS = S.βS := by
  ext1 v
  exact congrArg (fun f => LinearMap.snd k _ _ (f v)) S.lam_gamma_S

/-- A literal `SelmerQuadSwitch` (cochain-level finiteness) gives the homology-level
`QuasiQuadSwitch`. PROVED. -/
def SelmerQuadSwitch.toQuasi {J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)} (X : SelmerQuadSwitch k J) :
    QuasiQuadSwitch k J where
  R := X.R.toQuasi
  SF := X.SF.toQuasi
  SS := X.SS.toQuasi
  fV := X.fin_V
  fV' := X.fin_V'
  eK := X.eK
  σK := X.σK
  σV := X.σV
  σV' := X.σV'
  σr := X.σr
  hK := X.hK
  hV := X.hV
  hV' := X.hV'
  hr := X.hr
  hα' := X.hα'
  hβ' := by rw [SwitchSide.toQuasi_βF]; exact X.hβ'
  hγ' := X.hγ'
  hα'' := X.hα''
  hβ'' := by rw [SwitchSide.toQuasi_βS]; exact X.hβ''
  hγ'' := X.hγ''
  hl := X.hl

/-- A literal nonquadratic model step gives a homology-level one. PROVED. -/
def NonquadModelStep.toQuasi {ι : A →+* F} {ρ : A →+* k} {S S' : TwoTermStage ι}
    (N : NonquadModelStep ρ S S') : QuasiNonquadStep ρ S S' :=
  ⟨N.R.toQuasi, N.SF.toQuasi, N.SS.toQuasi, N.I.hk0, N.ε, N.σ, N.J, N.hε, N.hσ, N.hJ2, N.hdual,
    N.hdet, N.φ, N.φ'⟩

/-- A literal mixed model step gives a homology-level one. PROVED. -/
def MixedModelStep.toQuasi {ι : A →+* F} {ρ : A →+* k} {S S' : TwoTermStage ι}
    {σS : fiberH1 ρ S →ₗ[k] fiberH1 ρ S} {σS' : fiberH1 ρ S' →ₗ[k] fiberH1 ρ S'}
    (M : MixedModelStep ρ S S' σS σS') : QuasiMixedStep ρ S S' σS σS' where
  h2 := M.Y.h2
  ε := M.Y.ε
  hε := M.Y.hε
  J := M.Y.J
  hJ2 := M.Y.hJ2
  ep := M.Y.ep
  em := M.Y.em
  hp := M.Y.hp
  hm := M.Y.hm
  he := M.Y.he
  X := M.Y.X.toQuasi
  hU := M.Y.hU
  cp := M.Y.cp
  cm := M.Y.cm
  hcp := M.Y.hcp
  hcm := M.Y.hcm
  hdet := M.Y.hdet
  φ := M.φ
  hφ := M.hφ
  φ' := M.φ'
  hφ' := M.hφ'

/-- A literal single-sign model step gives a homology-level one. PROVED. -/
def SingleModelStep.toQuasi {ι : A →+* F} {ρ : A →+* k} {S S' : TwoTermStage ι}
    {σS' : fiberH1 ρ S' →ₗ[k] fiberH1 ρ S'}
    (M : SingleModelStep ρ S S' σS') : QuasiSingleStep ρ S S' σS' where
  h2 := M.Y.h2
  ε := M.Y.ε
  hε := M.Y.hε
  J := M.Y.J
  hJ2 := M.Y.hJ2
  ep := M.Y.ep
  em := M.Y.em
  hp := M.Y.hp
  hm := M.Y.hm
  he := M.Y.he
  X := M.Y.X.toQuasi
  hU := M.Y.hU
  cp := M.Y.cp
  hcp := M.Y.hcp
  hdet := M.Y.hdet
  hs1 := M.Y.hs1
  hs0 := M.Y.hs0
  φ := M.φ
  φ' := M.φ'
  hφ' := M.hφ'

/-- **Genuine switching data are Galois switching data**: every `GenuineSwitchData` (literal
degree-one steps) gives a `GaloisSwitchData` over the same family, so the new structure is no more
demanding on literal data. PROVED. -/
def GenuineSwitchData.toGalois {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}
    (G : GenuineSwitchData Φ ι ρ u) : GaloisSwitchData Φ ι ρ u where
  stage := G.stage
  model := G.model
  hz0 := G.hz0
  hw0 := G.hw0
  hu0 := G.hu0
  σ := G.σ
  h2 := G.h2
  hσ := G.hσ
  primitive := G.primitive
  switch_mixed c hc h1 h2 := by
    obtain ⟨p, hcs, hq, hn⟩ := G.switch_mixed c hc h1 h2
    refine ⟨p, hcs, fun q => ?_, fun nq => ?_⟩
    · obtain ⟨M⟩ := hq q
      exact ⟨M.M.toQuasi, M.hF, M.hS⟩
    · obtain ⟨N⟩ := hn nq
      exact ⟨N.N.toQuasi, N.hF, N.hS⟩
  switch_single c hc q h1 h2 := by
    obtain ⟨p, hcs, ⟨M⟩⟩ := G.switch_single c hc q h1 h2
    exact ⟨p, hcs, M.M.toQuasi, M.hF, M.hS⟩

end Literal

section NonVacuity

/-- **Non-vacuity of the homology-level nonquadratic step**: the 3 → 1 example of `SwitchData.lean`
(quasi sides of `QuasiSide.lean`'s `exQuasiRel`, shared strict condition, duality, detection). -/
noncomputable def exQuasiNonquadStep (u u' : ℚ) :
    QuasiNonquadStep (RingHom.id ℚ) (exStage3 u) (exStage1 u') :=
  (exNonquadModelStep u u').toQuasi

/-- Its `NonquadDims` is a genuine drop `3 → 1`. -/
theorem exQuasiNonquadStep_drop (u u' : ℚ) :
    (exStage1 u').fiberDim (RingHom.id ℚ) + 2 = (exStage3 u).fiberDim (RingHom.id ℚ) :=
  (exQuasiNonquadStep u u').toNonquadDims.drop

/-- **Non-vacuity of the homology-level mixed step** (both signs, genuine involutions). -/
noncomputable def exQuasiMixedStep (u u' : ℚ) := (exMixedModelStep u u').toQuasi

/-- **Non-vacuity of the homology-level single-sign step**. -/
noncomputable def exQuasiSingleStep := exSingleModelStep.toQuasi

/-- **Non-vacuity of `GaloisSwitchData`** (configuration-fixed family with forced fibre
dimension one, from `GenuineSwitch.lean`'s example), with regularity derived. -/
noncomputable def exGaloisSwitchData := exGenuineSwitchData.toGalois

theorem exGaloisSwitch_regular : ∃ a : ℚ, RingHom.id ℚ a = 1 :=
  regular_of_galoisSwitchData' Function.injective_id (fun x hx => by simpa using hx)
    exGaloisSwitchData

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
