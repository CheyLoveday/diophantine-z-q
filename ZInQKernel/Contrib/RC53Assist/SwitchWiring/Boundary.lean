import ZInQKernel.Contrib.RC53Assist.InnerLimitMoving.Consumers
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.InnerLimitWiring

/-!
# Boundary of literal side-to-family realization

Equality of Selmer data preserves the image of the local-condition inclusion.
For the single-place split presentation, the finite and singular inclusion
images are different. A singular successor therefore cannot serve as the
finite side of a further switch in the current family interface.

Sources: tex L4391–4451, L4997–5003, L5027–5086.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.SwitchWiring

open CategoryTheory Filter
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Contrib.RC53Assist.InnerLimitMoving
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane singPlane mem_finPlane mem_singPlane)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open scoped Matrix

/-- Kind: proved theorem. Literal equality of Selmer data with the same
full local complex preserves the image of each local-condition inclusion;
tex L4391–4451, L5040–5054. -/
theorem fixedLocalRange {k : Type} [Field k] {G G' U U' L : GCx k}
    {r : GHom G L} {r' : GHom G' L} {i : GHom U L} {i' : GHom U' L}
    (h : (⟨G, U, L, r, i⟩ : SelData k) = ⟨G', U', L, r', i'⟩) :
    LinearMap.range (i.f 1 1 rfl) = LinearMap.range (i'.f 1 1 rfl) := by
  rw [SelData.mk.injEq] at h
  obtain ⟨hG, hU, hL, hr, hi⟩ := h
  subst hU
  have he : i = i' := eq_of_heq hi
  rw [he]

/-- Kind: proved theorem. A finite single-place inner-limit Selmer datum
never equals a singular single-place inner-limit Selmer datum, even when
the global retained complexes or restrictions differ;
tex L4834–4907, L5040–5054, L5072–5086. -/
theorem finite_singular_ne {k : Type} [Field k] {G G' : GCx k}
    (r : GHom G (splitLocalComplex k)) (r' : GHom G' (splitLocalComplex k)) :
    (finiteLimitSide G r).Dside ≠ (singularLimitSide G' r').Dside := by
  intro h
  have hf := literalSideData G r (finPlane k (Vec2 k) (Vec2 k)) (Vec2 k)
    (LinearMap.snd k _ _) LinearMap.snd_surjective (fun _ => mem_finPlane.symm)
  have hs := literalSideData G' r' (singPlane k (Vec2 k) (Vec2 k)) (Vec2 k)
    (LinearMap.fst k _ _) LinearMap.fst_surjective (fun _ => mem_singPlane.symm)
  change (finiteLiteralLimitSide G r).Dside = (singularLiteralLimitSide G' r').Dside at h
  unfold finiteLiteralLimitSide singularLiteralLimitSide at h
  rw [hf, hs] at h
  have hr := fixedLocalRange h
  change LinearMap.range (finPlane k (Vec2 k) (Vec2 k)).subtype =
    LinearMap.range (singPlane k (Vec2 k) (Vec2 k)).subtype at hr
  rw [Submodule.range_subtype, Submodule.range_subtype] at hr
  have hx : ((![1, 0] : Vec2 k), (0 : Vec2 k)) ∈ finPlane k (Vec2 k) (Vec2 k) :=
    mem_finPlane.mpr rfl
  have hy : ((![1, 0] : Vec2 k), (0 : Vec2 k)) ∈ singPlane k (Vec2 k) (Vec2 k) := hr ▸ hx
  have hz := mem_singPlane.mp hy
  have he := congrFun hz 0
  simp at he

section FamilyBoundary

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F]
  {ι : Localization.AtPrime P →+* F} {u : F}
  {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}

/-- Kind: proved theorem. A successor realized as a singular side must
already be terminal for the current literal family interface. Otherwise
its required next finite side would equal that singular datum;
tex L4997–5003, L5027–5086. -/
theorem successor_dimension_le_one (X : InnerLimitSwitchInputs P Φ ι u)
    {c : Φ.Config} {p : Φ.Prime} (hc : Reach Φ.next Φ.actual c)
    (Y : InnerLimitStepData P (X.stage c) (X.stage (Φ.next c p)))
    (hS : Y.toStep.SS.Dside = Φ.fibre (Φ.next c p)) :
    (X.stage (Φ.next c p)).fiberDim (resAt P) ≤ 1 := by
  by_contra! h1
  obtain ⟨p', hcs, Z, hF, hS'⟩ := X.step (Φ.next c p) (Reach.step p hc) h1
  have he : (finiteLimitSide (fibreLimitGlobal Z.U Z.hU P Z.C)
      (Z.D.resLimit Z.hU P)).Dside =
      (singularLimitSide (fibreLimitGlobal Y.U Y.hU P Y.C)
        (Y.D.resLimit Y.hU P)).Dside := hF.trans hS.symm
  exact finite_singular_ne (Z.D.resLimit Z.hU P) (Y.D.resLimit Y.hU P) he

/-- Kind: proved theorem. Every reachable stage of the current literal
inner-limit family interface has fibre dimension at most three: one
nonquadratic switch drops the dimension by two and its successor is
terminal; tex L4997–5003, L5027–5086. -/
theorem reachable_dimension_le_three (X : InnerLimitSwitchInputs P Φ ι u)
    {c : Φ.Config} (hc : Reach Φ.next Φ.actual c) :
    (X.stage c).fiberDim (resAt P) ≤ 3 := by
  by_cases h1 : 1 < (X.stage c).fiberDim (resAt P)
  · obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    have hn := successor_dimension_le_one X hc Y hS
    have hd := Y.toStep.toNonquadDims.drop
    omega
  · omega

/-- Kind: proved theorem. A genuine starting fibre of dimension greater
than three has no inputs to the current literal family consumer. This
obstruction concerns the interface, not the arithmetic residue or
detection producers; tex L4976–5003, L5027–5086. -/
theorem no_inputs_of_large_actual_fibre
    (h : 3 < Module.finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1)) :
    ¬ Nonempty (InnerLimitSwitchInputs P Φ ι u) := by
  rintro ⟨X⟩
  have hb := reachable_dimension_le_three X Reach.start
  have he := X.toGalois.fiberDim_eq Φ.actual
  change (X.stage Φ.actual).fiberDim (resAt P) =
    Module.finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) at he
  omega

end FamilyBoundary

end ZInQ.Contrib.RC53Assist.SwitchWiring
