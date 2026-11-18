import Research.DerivativeSwitch.NativeSelmerCone

/-!
# Pure-boundary evaluation from native cones, a trace and a partner homotopy

The conclusion is derived from the degree-(2,1), parameter-zero cone product,
the actual cone-cycle equation, Leibniz and a right homotopy inverse. There is
no `boundary_adjoint` or equality of localized partners among the inputs.

Cup maps and their compatibility/isotropy homotopies are supplied. The product
formula is constructed here; identification with the arithmetic cup and PD,
and passage through the manuscript's retained models, are still applications.
Primal and conjugate local complexes have distinct types throughout. Fibre
indices 0, 1, 2 denote ordinary cone degrees 1, 2, 3 respectively; the
underlying global/local cochain indices in every cup map are unchanged.
-/

namespace Research.DerivativeSwitch.NativeBoundaryTrace

open CategoryTheory
open NativeSelmerCone

universe u
variable {R : Type u} [CommRing R]

noncomputable section

/-- Only the local Leibniz identity needed for a closed left degree-one
cochain. In particular no duality or boundary-evaluation equation is a field. -/
structure CupData (L M T : Complex (R := R)) where
  cup10 : L.X 1 →ₗ[R] M.X 0 →ₗ[R] T.X 1
  cup11 : L.X 1 →ₗ[R] M.X 1 →ₗ[R] T.X 2
  cup20 : L.X 2 →ₗ[R] M.X 0 →ₗ[R] T.X 2
  leibniz10 : ∀ l q,
    T.d 1 2 (cup10 l q) = cup20 (L.d 1 2 l) q - cup11 l (M.d 0 1 q)

section Trace

variable {A T : Complex (R := R)} (psi : A ⟶ T)
    (trace : (fibre psi).X 2 →ₗ[R] R)

/-- Restrict the SAME compact-support trace to its pure local summand. -/
def localTrace : T.X 2 →ₗ[R] R := trace.comp (pureLocal psi 2)

/-- A chain trace on the native compact-support differential kills local
boundaries. This is proved from the differential's sign, not assumed again. -/
theorem localTrace_kills_boundaries
    (htrace : ∀ w : (fibre psi).X 1, trace ((fibre psi).d 1 2 w) = 0)
    (x : T.X 1) : localTrace psi trace (T.d 1 2 x) = 0 := by
  have h := htrace (pureLocal psi 1 (-x))
  change trace (A.d 2 3 0, psi.f 2 0 - T.d 1 2 (-x)) = 0 at h
  simpa [localTrace, pureLocal, map_neg] using h

end Trace

section LocalCup

variable {L M T : Complex (R := R)} (D : CupData L M T)
    (tau : T.X 2 →ₗ[R] R) (htau : ∀ x, tau (T.d 1 2 x) = 0)

theorem closed_cup_differential (l : L.X 1) (q : M.X 0) (hl : L.d 1 2 l = 0) :
    D.cup11 l (M.d 0 1 q) = -T.d 1 2 (D.cup10 l q) := by
  have h := D.leibniz10 l q
  rw [hl, map_zero, LinearMap.zero_apply, zero_sub] at h
  exact neg_eq_iff_eq_neg.mp h.symm

/-- The second Leibniz identity is needed only when a trace square is supplied
up to homotopy: it proves that the local cup being evaluated is a cycle. -/
theorem cup_cycles_closed
    (cup21 : L.X 2 →ₗ[R] M.X 1 →ₗ[R] T.X 3)
    (cup12 : L.X 1 →ₗ[R] M.X 2 →ₗ[R] T.X 3)
    (hleibniz11 : ∀ l m, T.d 2 3 (D.cup11 l m) =
      cup21 (L.d 1 2 l) m - cup12 l (M.d 1 2 m))
    (l : L.X 1) (m : M.X 1) (hl : L.d 1 2 l = 0) (hm : M.d 1 2 m = 0) :
    T.d 2 3 (D.cup11 l m) = 0 := by
  rw [hleibniz11, hl, hm]
  simp

include htau in
theorem traced_right_boundary (l : L.X 1) (q : M.X 0) (hl : L.d 1 2 l = 0) :
    tau (D.cup11 l (M.d 0 1 q)) = 0 := by
  have h := D.leibniz10 l q
  rw [hl, map_zero, LinearMap.zero_apply, zero_sub] at h
  have ht := htau (D.cup10 l q)
  rw [h, map_neg] at ht
  exact neg_eq_zero.mp ht

include htau in
theorem traced_change_right (l : L.X 1) (m : M.X 1) (q : M.X 0)
    (hl : L.d 1 2 l = 0) :
    tau (D.cup11 l (m + M.d 0 1 q)) = tau (D.cup11 l m) := by
  rw [map_add, map_add, traced_right_boundary D tau htau l q hl, add_zero]

end LocalCup

section ConeProduct

variable {G U L GP UP M A T : Complex (R := R)}
    (loc : G ⟶ L) (inc : U ⟶ L) (locP : GP ⟶ M) (incP : UP ⟶ M)
    (psi : A ⟶ T) (D : CupData L M T)
    (cupG : G.X 2 →ₗ[R] GP.X 1 →ₗ[R] A.X 3)
    (hG : G.X 2 →ₗ[R] GP.X 1 →ₗ[R] T.X 2)
    (hU : U.X 2 →ₗ[R] UP.X 1 →ₗ[R] T.X 2)

/-- The displayed canonical degree-(2,1), r=0 cone-product formula.
The global and isotropy homotopy terms are retained before specialization. -/
def coneProduct (w : (selmer loc inc).X 1) (y : (selmer locP incP).X 0) :
    (fibre psi).X 2 :=
  (cupG w.1.1 y.1.1,
   D.cup11 w.2 (incP.f 1 y.1.2) +
     D.cup20 (loc.f 2 w.1.1) y.2 - hG w.1.1 y.1.1 + hU w.1.2 y.1.2)

theorem cone_pure_boundary (l : L.X 1) (y : (selmer locP incP).X 0) :
    coneProduct loc inc locP incP psi D cupG hG hU
        (pureLocal (selmerMap loc inc) 1 l) y =
      pureLocal psi 2 (D.cup11 l (incP.f 1 y.1.2)) := by
  change (cupG 0 y.1.1,
    D.cup11 l (incP.f 1 y.1.2) + D.cup20 (loc.f 2 0) y.2 -
      hG 0 y.1.1 + hU 0 y.1.2) = (0, D.cup11 l (incP.f 1 y.1.2))
  simp

/-- An exact compact-support BOUNDARY WITNESS, before applying any trace.
Its proof supplies the sum of the cycle and partner-homotopy cup corrections.
No inverse of 2/t, finite precision argument, or boundary-adjunction input is
used. `hj` is a projection square and `hk` an actual chain homotopy. -/
theorem pure_boundary_boundary_witness
    {C : Complex (R := R)}
    (j : selmer locP incP ⟶ C) (k : C ⟶ selmer locP incP) (q : C ⟶ raise GP)
    (hj : j ≫ q = globalProjection locP incP)
    (hk : Homotopy (k ≫ j) (𝟙 C))
    (z : C.X 0) (hz : C.d 0 1 z = 0)
    (l : L.X 1) (hl : L.d 1 2 l = 0) :
    ∃ b : T.X 1,
      coneProduct loc inc locP incP psi D cupG hG hU
        (pureLocal (selmerMap loc inc) 1 l) (k.f 0 z) =
      pureLocal psi 2 (D.cup11 l (locP.f 1 (q.f 0 z))) +
        (fibre psi).d 1 2 (pureLocal psi 1 b) := by
  have hy : (selmer locP incP).d 0 1 (k.f 0 z) = 0 := by
    have h := congrArg (fun a : C.X 0 ⟶ (selmer locP incP).X 1 => a z) (k.comm 0 1)
    simpa [ModuleCat.comp_apply, hz] using h
  have hcycle := selmer_cycle_equation locP incP (k.f 0 z) hy
  let H := OrthogonalComparison.inverse_preserves_local_homotopy
    j k (globalProjection locP incP) q hj hk (raiseMap locP)
  have hpartner := homotopy_cycle_boundary H z hz
  change locP.f 1 (k.f 0 z).1.1 =
    locP.f 1 (q.f 0 z) + M.d 0 1 (H.hom 0 (-1) z) at hpartner
  have hcup : D.cup11 l (incP.f 1 (k.f 0 z).1.2) =
      D.cup11 l (locP.f 1 (q.f 0 z)) -
        T.d 1 2 (D.cup10 l (H.hom 0 (-1) z)) - T.d 1 2 (D.cup10 l (k.f 0 z).2) := by
    calc
      _ = D.cup11 l (locP.f 1 (k.f 0 z).1.1) +
          D.cup11 l (M.d 0 1 (k.f 0 z).2) := by rw [hcycle, map_add]
      _ = (D.cup11 l (locP.f 1 (q.f 0 z)) +
          D.cup11 l (M.d 0 1 (H.hom 0 (-1) z))) +
          D.cup11 l (M.d 0 1 (k.f 0 z).2) := by rw [hpartner, map_add]
      _ = _ := by
        rw [closed_cup_differential D l _ hl, closed_cup_differential D l _ hl]
        abel
  refine ⟨D.cup10 l (H.hom 0 (-1) z) + D.cup10 l (k.f 0 z).2, ?_⟩
  rw [cone_pure_boundary]
  apply Prod.ext
  · change 0 = 0 + A.d 2 3 0
    simp
  · change D.cup11 l (incP.f 1 (k.f 0 z).1.2) =
      D.cup11 l (locP.f 1 (q.f 0 z)) +
        (psi.f 2 0 - T.d 1 2 (D.cup10 l (H.hom 0 (-1) z) + D.cup10 l (k.f 0 z).2))
    rw [hcup, map_zero, map_add]
    abel

/-- The boundary-adjunction evaluation is a CONSEQUENCE of the exact cone
boundary witness and one compact-support chain trace. -/
theorem pure_boundary_evaluation
    (trace : (fibre psi).X 2 →ₗ[R] R)
    (htrace : ∀ w : (fibre psi).X 1, trace ((fibre psi).d 1 2 w) = 0)
    {C : Complex (R := R)}
    (j : selmer locP incP ⟶ C) (k : C ⟶ selmer locP incP) (q : C ⟶ raise GP)
    (hj : j ≫ q = globalProjection locP incP)
    (hk : Homotopy (k ≫ j) (𝟙 C))
    (z : C.X 0) (hz : C.d 0 1 z = 0)
    (l : L.X 1) (hl : L.d 1 2 l = 0) :
    trace (coneProduct loc inc locP incP psi D cupG hG hU
      (pureLocal (selmerMap loc inc) 1 l) (k.f 0 z)) =
      localTrace psi trace (D.cup11 l (locP.f 1 (q.f 0 z))) := by
  obtain ⟨b, hb⟩ := pure_boundary_boundary_witness loc inc locP incP psi D cupG hG hU
    j k q hj hk z hz l hl
  rw [hb, map_add, htrace, add_zero]
  rfl

/-- A separately supplied trace RESTRICTION SQUARE identifies the already
derived evaluation with the arithmetic invariant map. It concerns all local
target cochains, not paired functionals or the desired normalization. -/
theorem pure_boundary_evaluation_of_trace_square
    (trace : (fibre psi).X 2 →ₗ[R] R)
    (htrace : ∀ w : (fibre psi).X 1, trace ((fibre psi).d 1 2 w) = 0)
    (inv : T.X 2 →ₗ[R] R) (kappa : R)
    (hsquare : ∀ t, localTrace psi trace t = kappa * inv t)
    {C : Complex (R := R)}
    (j : selmer locP incP ⟶ C) (k : C ⟶ selmer locP incP) (q : C ⟶ raise GP)
    (hj : j ≫ q = globalProjection locP incP)
    (hk : Homotopy (k ≫ j) (𝟙 C))
    (z : C.X 0) (hz : C.d 0 1 z = 0)
    (l : L.X 1) (hl : L.d 1 2 l = 0) :
    trace (coneProduct loc inc locP incP psi D cupG hG hU
      (pureLocal (selmerMap loc inc) 1 l) (k.f 0 z)) =
      kappa * inv (D.cup11 l (locP.f 1 (q.f 0 z))) := by
  rw [pure_boundary_evaluation loc inc locP incP psi D cupG hG hU
    trace htrace j k q hj hk z hz l hl, hsquare]

/-- A retained trace square need commute only UP TO ITS CHAIN HOMOTOPY.
The homotopy's degree-two defect factors through the local differential.
The (1,1) Leibniz identity and genuine projection/localization chain maps
kill that defect on the cup of the two actual cycles. -/
theorem pure_boundary_evaluation_of_trace_homotopy
    (trace : (fibre psi).X 2 →ₗ[R] R)
    (htrace : ∀ w : (fibre psi).X 1, trace ((fibre psi).d 1 2 w) = 0)
    (inv : T.X 2 →ₗ[R] R) (kappa : R) (sigma : T.X 3 →ₗ[R] R)
    (hsquare : ∀ t, localTrace psi trace t = kappa * inv t + sigma (T.d 2 3 t))
    (cup21 : L.X 2 →ₗ[R] M.X 1 →ₗ[R] T.X 3)
    (cup12 : L.X 1 →ₗ[R] M.X 2 →ₗ[R] T.X 3)
    (hleibniz11 : ∀ l m, T.d 2 3 (D.cup11 l m) =
      cup21 (L.d 1 2 l) m - cup12 l (M.d 1 2 m))
    {C : Complex (R := R)}
    (j : selmer locP incP ⟶ C) (k : C ⟶ selmer locP incP) (q : C ⟶ raise GP)
    (hj : j ≫ q = globalProjection locP incP)
    (hk : Homotopy (k ≫ j) (𝟙 C))
    (z : C.X 0) (hz : C.d 0 1 z = 0)
    (l : L.X 1) (hl : L.d 1 2 l = 0) :
    trace (coneProduct loc inc locP incP psi D cupG hG hU
      (pureLocal (selmerMap loc inc) 1 l) (k.f 0 z)) =
      kappa * inv (D.cup11 l (locP.f 1 (q.f 0 z))) := by
  have hm : M.d 1 2 (locP.f 1 (q.f 0 z)) = 0 := by
    have h := congrArg (fun a : C.X 0 ⟶ (raise M).X 1 => a z)
      ((q ≫ raiseMap locP).comm 0 1)
    change M.d 1 2 (locP.f 1 (q.f 0 z)) = locP.f 2 (q.f 1 (C.d 0 1 z)) at h
    simpa [hz] using h
  rw [pure_boundary_evaluation loc inc locP incP psi D cupG hG hU
    trace htrace j k q hj hk z hz l hl, hsquare,
    cup_cycles_closed D cup21 cup12 hleibniz11 l _ hl hm, map_zero, add_zero]

end ConeProduct

end

end Research.DerivativeSwitch.NativeBoundaryTrace
