import Research.DerivativeSwitch.NativeBoundaryTrace

/-!
# Opposite-boundary evaluation in the retained model

A closed degree-two functional pulls back along the inclusion of the retained
model. Its value on the projected connecting cochain equals its value before
projection. For the native cone product this value is the local trace of the
opposite cup, evaluated against the localized conjugate class.
-/

namespace Research.DerivativeSwitch.RetainedBoundaryRows

open CategoryTheory HomologicalComplex NativeSelmerCone NativeBoundaryTrace

universe u
variable {R : Type u} [CommRing R]

section Transfer

variable {C M : Complex (R := R)}

/-- A degree-two row is pulled back along the inclusion, not the projection. -/
def modelRow (i : M ⟶ C) (row : C.X 1 →ₗ[R] R) : M.X 1 →ₗ[R] R :=
  row.comp (i.f 1).hom

theorem modelRow_closed (i : M ⟶ C) (row : C.X 1 →ₗ[R] R)
    (hrow : ∀ b : C.X 0, row (C.d 0 1 b) = 0) (b : M.X 0) :
    modelRow i row (M.d 0 1 b) = 0 := by
  have h := congrArg (fun f : M.X 0 ⟶ C.X 1 => f b) (i.comm 0 1)
  change C.d 0 1 (i.f 0 b) = i.f 1 (M.d 0 1 b) at h
  change row (i.f 1 (M.d 0 1 b)) = 0
  rw [← h, hrow]

/-- Compression and pullback preserve evaluation on the actual cycle. -/
theorem modelRow_projected_cycle (p : C ⟶ M) (i : M ⟶ C)
    (H : Homotopy (p ≫ i) (𝟙 C)) (row : C.X 1 →ₗ[R] R)
    (hrow : ∀ b : C.X 0, row (C.d 0 1 b) = 0) (w : C.X 1)
    (hw : C.d 1 2 w = 0) : modelRow i row (p.f 1 w) = row w := by
  have h := H.comm 1
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 1 2 from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl)] at h
  have hcycle : i.f 1 (p.f 1 w) = C.d 0 1 (H.hom 1 0 w) + w := by
    simpa [ModuleCat.comp_apply, hw] using
      congrArg (fun f : C.X 1 ⟶ C.X 1 => f w) h
  change row (i.f 1 (p.f 1 w)) = row w
  rw [hcycle, map_add, hrow, zero_add]

end Transfer

section Pairing

variable {G U L GP UP P A T : Complex (R := R)}
    (loc : G ⟶ L) (inc : U ⟶ L) (locP : GP ⟶ P) (incP : UP ⟶ P)
    (psi : A ⟶ T) (D : CupData L P T)
    (cupG : G.X 2 →ₗ[R] GP.X 1 →ₗ[R] A.X 3)
    (hG : G.X 2 →ₗ[R] GP.X 1 →ₗ[R] T.X 2)
    (hU : U.X 2 →ₗ[R] UP.X 1 →ₗ[R] T.X 2)
    (trace : (fibre psi).X 2 →ₗ[R] R)

/-- The row is constructed by evaluating the full degree-(2,1) product
against the partner cochain and then applying the compact-support trace. -/
def pairedRow (y : (selmer locP incP).X 0) : (selmer loc inc).X 1 →ₗ[R] R :=
  let gu := LinearMap.fst R ((pair G U).X 2) (L.X 1)
  let g := (LinearMap.fst R (G.X 2) (U.X 2)).comp gu
  let u := (LinearMap.snd R (G.X 2) (U.X 2)).comp gu
  let l := LinearMap.snd R ((pair G U).X 2) (L.X 1)
  trace.comp (((cupG.flip y.1.1).comp g).prod
    ((D.cup11.flip (incP.f 1 y.1.2)).comp l +
      (D.cup20.flip y.2).comp ((loc.f 2).hom.comp g) -
      (hG.flip y.1.1).comp g + (hU.flip y.1.2).comp u))

theorem pairedRow_apply (y : (selmer locP incP).X 0) (w : (selmer loc inc).X 1) :
    pairedRow loc inc locP incP psi D cupG hG hU trace y w =
      trace (coneProduct loc inc locP incP psi D cupG hG hU w y) := rfl

variable
    (htrace : ∀ w : (fibre psi).X 1, trace ((fibre psi).d 1 2 w) = 0)
    (coneCup11 : (selmer loc inc).X 0 →ₗ[R] (selmer locP incP).X 0 →ₗ[R] (fibre psi).X 1)
    (coneCup12 : (selmer loc inc).X 0 →ₗ[R] (selmer locP incP).X 1 →ₗ[R] (fibre psi).X 2)
    (leibniz : ∀ w y, (fibre psi).d 1 2 (coneCup11 w y) =
      coneProduct loc inc locP incP psi D cupG hG hU ((selmer loc inc).d 0 1 w) y -
        coneCup12 w ((selmer locP incP).d 0 1 y))

include htrace in
/-- The pre-inverse boundary evaluation on arbitrary partner cochains.
The defect factors through the partner differential, so the identity can
be transported before taking the inner limit or constructing a right inverse. -/
theorem boundary_row_defect (l : L.X 1) (hl : L.d 1 2 l = 0)
    (y : (selmer locP incP).X 0) :
    pairedRow loc inc locP incP psi D cupG hG hU trace y
        (pureLocal (selmerMap loc inc) 1 l) =
      localTrace psi trace (D.cup11 l (locP.f 1 y.1.1)) +
        localTrace psi trace (D.cup11 l ((selmer locP incP).d 0 1 y).2) := by
  rw [pairedRow_apply, cone_pure_boundary]
  change localTrace psi trace (D.cup11 l (incP.f 1 y.1.2)) = _
  have h : incP.f 1 y.1.2 =
      locP.f 1 y.1.1 + P.d 0 1 y.2 + ((selmer locP incP).d 0 1 y).2 := by
    change incP.f 1 y.1.2 = locP.f 1 y.1.1 + P.d 0 1 y.2 +
      (-locP.f 1 y.1.1 + incP.f 1 y.1.2 - P.d 0 1 y.2)
    abel
  rw [h, map_add, map_add, map_add, map_add,
    traced_right_boundary D (localTrace psi trace)
      (localTrace_kills_boundaries psi trace htrace) l y.2 hl, add_zero]

include htrace coneCup11 coneCup12 leibniz in
/-- The degree-(1,1) Leibniz identity before trace gives a closed row
whenever the partner is closed. -/
theorem pairedRow_closed (y : (selmer locP incP).X 0) (hy : (selmer locP incP).d 0 1 y = 0)
    (b : (selmer loc inc).X 0) :
    pairedRow loc inc locP incP psi D cupG hG hU trace y ((selmer loc inc).d 0 1 b) = 0 := by
  have hb := leibniz b y
  rw [hy, map_zero, sub_zero] at hb
  rw [pairedRow_apply, ← hb, htrace]

include htrace coneCup11 coneCup12 leibniz in
/-- Evaluate the pulled-back row on the projected opposite connecting
cochain, using the degree-(1,1) Leibniz identity for the canonical product. -/
theorem projected_boundary_row
    {C M : Complex (R := R)}
    (j : selmer locP incP ⟶ C) (k : C ⟶ selmer locP incP) (q : C ⟶ raise GP)
    (hj : j ≫ q = globalProjection locP incP)
    (hk : Homotopy (k ≫ j) (𝟙 C))
    (z : C.X 0) (hz : C.d 0 1 z = 0)
    (p : selmer loc inc ⟶ M) (i : M ⟶ selmer loc inc)
    (H : Homotopy (p ≫ i) (𝟙 (selmer loc inc)))
    (l : L.X 1) (hl : L.d 1 2 l = 0) :
    modelRow i (pairedRow loc inc locP incP psi D cupG hG hU trace (k.f 0 z))
        (p.f 1 (pureLocal (selmerMap loc inc) 1 l)) =
      localTrace psi trace (D.cup11 l (locP.f 1 (q.f 0 z))) := by
  have hy : (selmer locP incP).d 0 1 (k.f 0 z) = 0 := by
    have hk' := congrArg (fun f : C.X 0 ⟶ (selmer locP incP).X 1 => f z) (k.comm 0 1)
    simpa [ModuleCat.comp_apply, hz] using hk'
  have hrow := pairedRow_closed loc inc locP incP psi D cupG hG hU trace htrace
    coneCup11 coneCup12 leibniz (k.f 0 z) hy
  rw [modelRow_projected_cycle p i H _ hrow _ (pureLocal_closed _ l hl)]
  rw [pairedRow_apply]
  exact pure_boundary_evaluation loc inc locP incP psi D cupG hG hU trace htrace
    j k q hj hk z hz l hl

end Pairing

end Research.DerivativeSwitch.RetainedBoundaryRows
