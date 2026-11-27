import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuityModelQuad
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GaloisInvolution

/-!
# RC53 SwitchInputs: non-vacuity of the diagram involution

non-vacuity for `GaloisInvolution.lean`'s model structure `DiagramInvolution R SF SS` (a hypothesis of
`DiagramInvolution.toSelmerQuadSwitch`, tex L5009–5086): a genuine instance over `ℚ` with
non-trivial involutions, on the mixed-sign example `exRel`, `exSideF`, `exSideS` of
`NonVacuity.lean`.

* `exSelEndoRel : SelEndo exRelD`: the identity on the global complex `G`, `(x, y) ↦ (J₀x, −J₀y)` on
  the relaxed condition `U = F ⊕ S`, `−J₀` on the full local complex `L = S`.
* `exDiagramInvolution : DiagramInvolution exRel exSideF exSideS`: with `J₀` on `U_F = F`, `0` on
  the strict condition `U_str = 0`, and `−J₀` on `U_S = S`.
* `exDiagram_σV`, `exDiagram_σV'`, `exDiagram_σr`, `exDiagram_σK`: its four involutions on `H¹` are
  those of NonVacuityQuad's `exQuadSwitchA` (the identity on the strict cohomology), so the switch it
  produces carries both signs (as used by `exQuadMixedStep`).
* `exDiagramSwitch : SelmerQuadSwitch ℚ J₀L`: `toSelmerQuadSwitch` applied to it, the remaining local
  clauses `hβ', hβ'', hl` and `hα''` checked.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

section DiagramExample

/-- The Selmer involution of the relaxed data of the mixed example. -/
def exSelEndoRel : SelEndo exRelD where
  g := zHom fun _ => LinearMap.id
  lam := zHom fun n => -flipM (dimAt 2 n)
  mu := zHom fun n => (flipM (dimAt 2 n)).prodMap (-flipM (dimAt 2 n))
  hres i a := by
    change (0 : V1 i →ₗ[ℚ] V2 i) a = (-flipM (dimAt 2 i)) ((0 : V1 i →ₗ[ℚ] V2 i) a)
    erw [zero_apply', map_zero]
  hι i u := by
    change LinearMap.snd ℚ (V2 i) (V2 i) (((flipM (dimAt 2 i)).prodMap (-flipM (dimAt 2 i))) u) =
      (-flipM (dimAt 2 i)) (LinearMap.snd ℚ (V2 i) (V2 i) u)
    rfl

theorem exSelEndoRel_isInvolution : exSelEndoRel.IsInvolution := by
  refine ⟨fun i a => rfl, fun i x => negflip_negflip _ x, fun i u => ?_⟩
  change ((flipM (dimAt 2 i)).prodMap (-flipM (dimAt 2 i)))
    (((flipM (dimAt 2 i)).prodMap (-flipM (dimAt 2 i))) u) = u
  exact Prod.ext (flipM_flipM _ _) (negflip_negflip _ _)

/-- **A genuine diagram involution** (non-vacuity for `DiagramInvolution`, tex L5009–5086): on the
mixed example, `J₀` on the finite condition, `0` on the strict condition, `−J₀` on the singular
condition, all compatible with the inclusions into the relaxed condition. -/
def exDiagramInvolution : DiagramInvolution exRel exSideF exSideS where
  X := exSelEndoRel
  hX := exSelEndoRel_isInvolution
  μF := zHom fun n => flipM (dimAt 2 n)
  hμF i u := by
    change LinearMap.inl ℚ (V2 i) (V2 i) (flipM (dimAt 2 i) u) =
      ((flipM (dimAt 2 i)).prodMap (-flipM (dimAt 2 i))) (LinearMap.inl ℚ (V2 i) (V2 i) u)
    refine Prod.ext rfl ?_
    change (0 : V2 i) = (-flipM (dimAt 2 i)) 0
    simp
  hμF2 i u := flipM_flipM _ u
  μFs := zHom fun _ => 0
  hμFs i u := by
    change (0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 i) ((0 : (Fin 0 → ℚ) →ₗ[ℚ] (Fin 0 → ℚ)) u) =
      flipM (dimAt 2 i) ((0 : (Fin 0 → ℚ) →ₗ[ℚ] V2 i) u)
    erw [zero_apply', map_zero]
  hμFs2 i u := funext fun j => j.elim0
  μS := zHom fun n => -flipM (dimAt 2 n)
  hμS i u := by
    change LinearMap.inr ℚ (V2 i) (V2 i) ((-flipM (dimAt 2 i)) u) =
      ((flipM (dimAt 2 i)).prodMap (-flipM (dimAt 2 i))) (LinearMap.inr ℚ (V2 i) (V2 i) u)
    refine Prod.ext ?_ rfl
    change (0 : V2 i) = flipM (dimAt 2 i) 0
    simp
  hμS2 i u := negflip_negflip _ u

/-- The finite-side involution of the diagram is NonVacuityQuad's `σVA`. PROVED. -/
theorem exDiagram_σV : exDiagramInvolution.σV = σVA := by
  unfold DiagramInvolution.σV σVA
  apply H1_congr
  intro x
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  rw [SelEndo.sigma_apply]
  change (a, flipM (dimAt 2 1) u, (-flipM (dimAt 2 0)) l) =
    (a, flipM (dimAt 2 1) u + (0 : V1 1 →ₗ[ℚ] V2 1) a, (-flipM (dimAt 2 0)) l)
  erw [zero_apply', add_zero]

/-- The singular-side involution of the diagram is NonVacuityQuad's `σV'A`. PROVED. -/
theorem exDiagram_σV' : exDiagramInvolution.σV' = σV'A := by
  unfold DiagramInvolution.σV' σV'A
  apply H1_congr
  intro x
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  rw [SelEndo.sigma_apply]
  change (a, (-flipM (dimAt 2 1)) u, (-flipM (dimAt 2 0)) l) =
    (a, (-flipM (dimAt 2 1)) u + (0 : V1 1 →ₗ[ℚ] V2 1) a, (-flipM (dimAt 2 0)) l)
  erw [zero_apply', add_zero]

/-- The relaxed involution of the diagram is NonVacuityQuad's `σrA`. PROVED. -/
theorem exDiagram_σr : exDiagramInvolution.σr = σrA := by
  unfold DiagramInvolution.σr σrA
  apply H1_congr
  intro x
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  rw [SelEndo.sigma_apply]
  change (a, ((flipM (dimAt 2 1)).prodMap (-flipM (dimAt 2 1))) u, (-flipM (dimAt 2 0)) l) =
    (a, ((flipM (dimAt 2 1)).prodMap (-flipM (dimAt 2 1))) u + (0 : V1 1 →ₗ[ℚ] V2 1 × V2 1) a,
      (-flipM (dimAt 2 0)) l)
  erw [zero_apply', add_zero]

/-- The strict involution of the diagram is the identity (the strict condition and `L⁰` vanish).
PROVED. -/
theorem exDiagram_σK : exDiagramInvolution.σK = LinearMap.id := by
  unfold DiagramInvolution.σK
  apply H1_eq_id
  intro x
  obtain ⟨⟨a, u, l⟩, hx⟩ := x
  rw [SelEndo.sigma_apply]
  have h1 : Subsingleton (exSideF.Dstr.U.X 1) := by
    change Subsingleton (Fin 0 → ℚ); infer_instance
  have h2 : Subsingleton (exSideF.Dstr.L.X (1 - 1)) := by
    change Subsingleton (Fin (dimAt 2 (1 - 1)) → ℚ); exact subsingleton_dimAt 2 (by decide)
  exact Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

/-- **The `SelmerQuadSwitch` of the diagram involution** (tex L5009–5086): `toSelmerQuadSwitch`
applied to `exDiagramInvolution`, with `J = J₀` and the local clauses checked. -/
def exDiagramSwitch : SelmerQuadSwitch ℚ J₀L :=
  exDiagramInvolution.toSelmerQuadSwitch J₀L
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 1 1) → ℚ))
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 0) → ℚ))
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
    (inferInstance : FiniteDimensional ℚ (Fin (dimAt 2 1) → ℚ))
    exSelmerQuadSwitch.eK
    (by
      rw [exDiagram_σK, exDiagram_σV']
      exact LinearMap.ext fun v =>
        (LinearMap.congr_fun fixSA (exSelmerQuadSwitch.eK.symm v)).symm)
    (by rw [exDiagram_σV]; exact βFA_equiv)
    (by
      rw [exDiagram_σV']
      ext1 v
      simp only [LinearMap.comp_apply, exSideS_βS_zero, map_zero])
    (by rw [exDiagram_σr]; exact lamA_equiv)

/-- The diagram's switch has the involutions of `exQuadSwitchA` (both signs on the finite side, as
used by `exQuadMixedStep`). PROVED. -/
theorem exDiagramSwitch_involutions :
    exDiagramSwitch.σV = exQuadSwitchA.σV ∧ exDiagramSwitch.σV' = exQuadSwitchA.σV' ∧
      exDiagramSwitch.σr = exQuadSwitchA.σr ∧ exDiagramSwitch.σK = exQuadSwitchA.σK :=
  ⟨exDiagram_σV, exDiagram_σV', exDiagram_σr, exDiagram_σK⟩

end DiagramExample

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
