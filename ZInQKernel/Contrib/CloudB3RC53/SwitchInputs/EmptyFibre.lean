import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericAtFibre

/-!
# RC53 SwitchInputs: the chain's fibre at the empty configuration is the fibre Selmer data

The field-generic chain at `V_𝔭` (`GenericAtFibre.lean`) uses the configuration conditions
`fibreConds D`: the unramified conditions `urSubK` (subcomplexes of the fibre local complexes) at
every place outside the configuration. At the empty configuration its fibre is
`galoisSelData … (condAt (galCond urSubK) (galCond singCond) ∅)`, which agrees degree by degree
with lane RC28's `fibreUr = fibreSelData W 𝔭 α (fibreUrConditions W 𝔭 α)`
(`urSubK_S_eq_range`) but is presented differently (subcomplexes versus RC28's cocycle conditions
`ofCondAt`). This file proves that the two Selmer complexes are isomorphic.

* `condHomOfRange` (PROVED): for local conditions `Δ`, `Δ'` whose condition maps are injective
  with the same image in every degree at every place, the induced morphism of condition complexes
  `Δ.U v → Δ'.U v` (a chain map commuting with the condition maps).
* `selIsoOfRange` (PROVED): then the Selmer complexes are isomorphic,
  `C_Δ ≅ C_{Δ'}` (lane RC26's `condMap` both ways).
* `condAt_empty` (PROVED): the conditions of the empty configuration are the base conditions.
* **`emptyFibreIso` (PROVED)**: the chain's fibre at the empty configuration is isomorphic to
  RC28's `fibreUr W 𝔭 α`, as cochain complexes.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.SelmerDuality NumberField IsDedekindDomain ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

/-! ### Local conditions with the same images -/

section Range

variable {k : Type} [Field k] {GS : Type} [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type} {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  (Δ Δ' : LocalConditions k GS Gv loc M)
  (hinj' : ∀ v n, Function.Injective ((Δ'.i v).f n n rfl))
  (hrange : ∀ v n, LinearMap.range ((Δ.i v).f n n rfl) = LinearMap.range ((Δ'.i v).f n n rfl))

/-- The components of `condHomOfRange`: `u ↦ (Δ'.i)⁻¹ (Δ.i u)`. -/
def condFunOfRange (v : ι) (n : ℤ) : (Δ.U v).X n →ₗ[k] (Δ'.U v).X n :=
  (LinearEquiv.ofInjective _ (hinj' v n)).symm.toLinearMap ∘ₗ
    ((Δ.i v).f n n rfl).codRestrict (LinearMap.range ((Δ'.i v).f n n rfl))
      (fun u => hrange v n ▸ LinearMap.mem_range_self _ u)

omit [IsTopologicalGroup GS] in
theorem condFunOfRange_spec (v : ι) (n : ℤ) (u : (Δ.U v).X n) :
    (Δ'.i v).f n n rfl (condFunOfRange Δ Δ' hinj' hrange v n u) = (Δ.i v).f n n rfl u := by
  unfold condFunOfRange
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (hinj' v n)).apply_symm_apply _)

/-- **The morphism of condition complexes of two local conditions with the same images**: a
chain map `Δ.U v → Δ'.U v` with `Δ'.i ∘ F = Δ.i`. PROVED. -/
def condHomOfRange (v : ι) : GHom (Δ.U v) (Δ'.U v) where
  f i j h := by subst h; exact condFunOfRange Δ Δ' hinj' hrange v i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    apply hinj' v i₁
    change (Δ'.i v).f i₁ i₁ rfl (condFunOfRange Δ Δ' hinj' hrange v i₁ ((Δ.U v).d i i₁ h₁ x)) =
      (Δ'.i v).f i₁ i₁ rfl ((Δ'.U v).d i i₁ h₂ (condFunOfRange Δ Δ' hinj' hrange v i x))
    rw [condFunOfRange_spec, (Δ'.i v).comm i i₁ i i₁ rfl h₂ h₂ rfl, condFunOfRange_spec,
      (Δ.i v).comm i i₁ i i₁ rfl h₁ h₂ rfl]

omit [IsTopologicalGroup GS] in
theorem condHomOfRange_spec (v : ι) (n : ℤ) (u : (Δ.U v).X n) :
    (Δ'.i v).f n n rfl ((condHomOfRange Δ Δ' hinj' hrange v).f n n rfl u) =
      (Δ.i v).f n n rfl u :=
  condFunOfRange_spec Δ Δ' hinj' hrange v n u

variable (hinj : ∀ v n, Function.Injective ((Δ.i v).f n n rfl))

/-- **Local conditions with injective condition maps and the same images have isomorphic Selmer
complexes**: `C_Δ ≅ C_{Δ'}`, by `condMap` along `condHomOfRange` in both directions. PROVED. -/
def selIsoOfRange :
    (selCx (selData k GS Gv loc M Δ)).toCC ≅ (selCx (selData k GS Gv loc M Δ')).toCC where
  hom := GHom.toCC (condMap Δ Δ' (condHomOfRange Δ Δ' hinj' hrange)
    (condHomOfRange_spec Δ Δ' hinj' hrange))
  inv := GHom.toCC (condMap Δ' Δ (condHomOfRange Δ' Δ hinj (fun v n => (hrange v n).symm))
    (condHomOfRange_spec Δ' Δ hinj (fun v n => (hrange v n).symm)))
  hom_inv_id := by
    ext n c
    obtain ⟨a, u, x⟩ := c
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext v
    apply hinj v n
    change (Δ.i v).f n n rfl ((condHomOfRange Δ' Δ hinj (fun v n => (hrange v n).symm) v).f n n rfl
      ((condHomOfRange Δ Δ' hinj' hrange v).f n n rfl (u v))) = (Δ.i v).f n n rfl (u v)
    rw [condHomOfRange_spec, condHomOfRange_spec]
  inv_hom_id := by
    ext n c
    obtain ⟨a, u, x⟩ := c
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext v
    apply hinj' v n
    change (Δ'.i v).f n n rfl ((condHomOfRange Δ Δ' hinj' hrange v).f n n rfl
      ((condHomOfRange Δ' Δ hinj (fun v n => (hrange v n).symm) v).f n n rfl (u v))) =
        (Δ'.i v).f n n rfl (u v)
    rw [condHomOfRange_spec, condHomOfRange_spec]

end Range

/-! ### The empty configuration -/

section Empty

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [Field k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

/-- **The conditions of the empty configuration are the base conditions.** PROVED. -/
theorem condAt_empty (Δ₀ Δd : GaloisLocalConditions K S k M) :
    condAt K S k M Δ₀ Δd ∅ = Δ₀ := by
  have h : (fun v => condPair K S k M Δ₀ Δd ∅ v) = fun v => ⟨Δ₀.U v, Δ₀.i v⟩ := by
    funext v
    unfold condPair
    exact ite_eq_right (Finset.notMem_empty v)
  have key : ∀ f : ∀ v : Places K S, Σ U : GCx k, GHom U (localCx k (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M v),
      f = (fun v => ⟨Δ₀.U v, Δ₀.i v⟩) →
        (⟨fun v => (f v).1, fun v => (f v).2⟩ : GaloisLocalConditions K S k M) = Δ₀ := by
    rintro f rfl
    rfl
  exact key _ h

end Empty

section Fibre

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
  (α : GKS K S →* Lambdaˣ) [IsContChar α]

/-- **The chain's fibre at the empty configuration is RC28's fibre Selmer data** (tex 3479–3498):
for every tame datum `D`, the Selmer complex of
`condAt (galCond urSubK) (galCond singCond) ∅` (the fibre of the field-generic chain at `V_𝔭` at
the empty configuration) is isomorphic to that of `fibreUr W 𝔭 α =
fibreSelData W 𝔭 α (fibreUrConditions W 𝔭 α)`. PROVED (`condAt_empty`, `urSubK_S_eq_range`, RC28's
`fibreUr_injective`, `selIsoOfRange`). -/
def emptyFibreIso (D : PlaceTameK K S) :
    (selCx (galoisSelData K S (ResAt P) (VP K S W P α)
      (condAt K S (ResAt P) (VP K S W P α) (galCond K S (VP K S W P α) (fibreConds W P α D).A₀)
        (galCond K S (VP K S W P α) (fibreConds W P α D).Ad) ∅))).toCC ≅
      (selCx (fibreUr W P α)).toCC := by
  rw [condAt_empty]
  exact selIsoOfRange (galCond K S (VP K S W P α) (urSubK W P α)) (fibreUrConditions W P α)
    (fun v n => fibreUr_injective W P α v n)
    (fun v n => by
      change LinearMap.range ((urSubK W P α v).incl.f n n rfl) = _
      rw [← urSubK_S_eq_range]
      exact Submodule.range_subtype _)
    (fun v n => by
      change Function.Injective ((urSubK W P α v).incl.f n n rfl)
      exact Subtype.val_injective)

end Fibre

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
