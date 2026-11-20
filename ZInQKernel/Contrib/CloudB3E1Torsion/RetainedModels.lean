import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18RetainedChain

/-!
# Retained models of the full support from the chain data

Manuscript `diophantine_zq.tex`, tex 4185–4193 and 4391–4406.

Lane RC32's statement `RetainedModelsExist Cx pidx n G U` asks for two things:
* a `U`-large set `G′ ⊆ G`;
* at every stage of `G′`, a retract of the full-support complex `Cx s (chainT pidx n)` onto a
  finite free model with bases of fixed index types `Fin (r 0), …, Fin (r 3)`.

As stated it quantifies over arbitrary complexes, so on its own it cannot hold. With the chain
data on `G` it does: the chain carries, at every stage, the cone model of the full support as a
retract (`(cmState cd n le_rfl).R`), with bases (`coneFree`) whose index types do not depend on
the stage.

* `fourFreeReindex` (definition): bases transported along equivalences of the index types.
* `coneRetainedModel` (definition): the cone model of the full support as a `RetainedModel`,
  with index types `Fin m₀`, `Fin |cD₁|`, `Fin |cD₂|`, `Fin m₂`.
* **`retainedModelsExist_of_chain`** (PROVED): chain data on `G` with `G` `U`-large gives
  `RetainedModelsExist Cx pidx n G U`, with `G′ = G` and fixed ranks
  `(m₀, |cD₁|, |cD₂|, m₂)`.

**`not_retainedMapsToCochains`** (PROVED) concerns lane RC32's other statement,
`RetainedMapsToCochains XΛ Y₁ Y₂ b₁ b₂ c U` (tex 4438–4439, 4449–4450). It does not hold as stated:
for `XΛ = 0` and `Y₁ = Y₂ = Λ` in degree zero there is no retract, whatever `c` and `U` are. A
correct statement needs hypotheses tying `XΛ` and the models to the stage complexes. The tree
does not record those: the original cochains over `Λ` whose stage reductions are the stage
complexes, and the stage retracts carried through the limit.

These retained models are the cone models themselves. With them, `htildeE_of_retained` reduces to
its isomorphism case. Lane RC31's graded models (`exists_gradedModel`) are a different choice of
retained model; the leaf accepts any choice.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Limits (SplitInclusion)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx)

/-- **Bases transported along equivalences of the index types.** Kind: definition. -/
def fourFreeReindex {A : Type} [CommRing A] {Y : GCx A} {ι0 ι1 ι2 ι3 κ0 κ1 κ2 κ3 : Type}
    (b : FourFree Y ι0 ι1 ι2 ι3) (e0 : ι0 ≃ κ0) (e1 : ι1 ≃ κ1) (e2 : ι2 ≃ κ2) (e3 : ι3 ≃ κ3) :
    FourFree Y κ0 κ1 κ2 κ3 where
  e0 := b.e0.trans (LinearEquiv.funCongrLeft A A e0.symm)
  e1 := b.e1.trans (LinearEquiv.funCongrLeft A A e1.symm)
  e2 := b.e2.trans (LinearEquiv.funCongrLeft A A e2.symm)
  e3 := b.e3.trans (LinearEquiv.funCongrLeft A A e3.symm)
  lo := b.lo
  hi := b.hi

section Chain

variable {A : Type} [CommRing A] {ι : Type} [DecidableEq ι] {C : Finset ι → GCx A}
  {E : ∀ (T : Finset ι) (p : ι), SplitInclusion (C T) (C (insert p T))} {m0 m1 m2 : ℕ}
  {ps : ℕ → ι} {n : ℕ}

/-- **The cone model of the full support as a retained model** (tex 4185–4193), with bases
indexed by `Fin`. Kind: definition. -/
def coneRetainedModel (cd : CMChainData C E m0 m1 m2 ps n) :
    RetainedModel (C (chainT ps n)) (Fin m0) (Fin (Fintype.card (cD1 m0 m1 n)))
      (Fin (Fintype.card (cD2 m1 m2 n))) (Fin m2) where
  Y := (cmState cd n le_rfl).D.toGCx
  R := (cmState cd n le_rfl).R
  b := fourFreeReindex (coneFree cd) (Equiv.refl _) (Fintype.equivFin _) (Fintype.equivFin _)
    (Equiv.refl _)

end Chain

/-- **`RetainedModelsExist` from the chain data** (tex 4391–4406): chain data at the stages of a
`U`-large set `G` give retained models of the full support with ranks
`(m₀, |cD₁|, |cD₂|, m₂)` fixed along `U` (on `G′ = G`). Kind: PROVED. -/
theorem retainedModelsExist_of_chain {ι : Type} [DecidableEq ι]
    {Cx : ∀ s, Finset ι → GCx (StageRing s)}
    {Ex : ∀ s (T : Finset ι) (p : ι), SplitInclusion (Cx s T) (Cx s (insert p T))}
    {m0 m1 m2 : ℕ} {pidx : ℕ → ι} {n : ℕ} {G : Set ℕ} {U : Ultrafilter ℕ}
    (cd : ∀ s, s ∈ G → CMChainData (Cx s) (Ex s) m0 m1 m2 pidx n)
    (hG : ∀ᶠ s in (U : Filter ℕ), s ∈ G) : RetainedModelsExist Cx pidx n G U :=
  ⟨![m0, Fintype.card (cD1 m0 m1 n), Fintype.card (cD2 m1 m2 n), m2], G, subset_rfl, hG,
    ⟨fun s hs => coneRetainedModel (cd s hs)⟩⟩

/-! ### `RetainedMapsToCochains` does not hold as stated -/

section MapsToCochains

open ZInQ.Manuscript.RC.Limits (matCx GRetract)

/-- The rank function of `Λ` in degree zero. Kind: definition. -/
def rankPt : ℤ → ℕ := fun k => if k = 0 then 1 else 0

/-- The zero complex over `Λ`. Kind: definition. -/
def zeroCx : GCx LamI :=
  matCx (fun _ => 0) (fun _ _ _ => 0) (fun _ _ _ _ _ => Matrix.zero_mul _)

/-- The complex `Λ` in degree zero. Kind: definition. -/
def ptCx : GCx LamI :=
  matCx rankPt (fun _ _ _ => 0) (fun _ _ _ _ _ => Matrix.zero_mul _)

/-- Its standard bases. Kind: definition. -/
def ptFree : FourFree ptCx (Fin (rankPt 0)) (Fin (rankPt 1)) (Fin (rankPt 2)) (Fin (rankPt 3)) :=
  FourFree.ofMatCx rankPt (fun _ _ _ => 0) (fun _ _ _ _ _ => Matrix.zero_mul _) rfl rfl

/-- **The zero complex has no retract onto `Λ` in degree zero.** Kind: PROVED. -/
theorem not_retract_zero_pt (R : GRetract zeroCx ptCx) : False := by
  have h := R.p_i 0 (fun _ => (1 : LamI))
  have h0 : R.i.f 0 0 rfl (fun _ => (1 : LamI)) = 0 := by
    change (_ : Fin 0 → LamI) = 0
    exact funext fun i => i.elim0
  rw [h0, map_zero] at h
  have := congrFun h ⟨0, by simp [rankPt]⟩
  exact one_ne_zero this.symm

/-- **`RetainedMapsToCochains` fails without hypotheses tying the complexes to the stages**: for
the zero complex `XΛ = 0`, the models `Y₁ = Y₂ = Λ` in degree zero (with their standard bases), any
stage data and any ultrafilter, the statement is false. Kind: PROVED. -/
theorem not_retainedMapsToCochains
    (c : ℕ → HEMat LamI (Fin (rankPt 0)) (Fin (rankPt 1)) (Fin (rankPt 2)) (Fin (rankPt 3))
      (Fin (rankPt 0)) (Fin (rankPt 1)) (Fin (rankPt 2)) (Fin (rankPt 3)))
    (U : Ultrafilter ℕ) : ¬ RetainedMapsToCochains zeroCx ptCx ptCx ptFree ptFree c U := by
  rintro ⟨R₁, -, -⟩
  exact not_retract_zero_pt R₁

end MapsToCochains

end ZInQ.Contrib.CloudB3E1Torsion
