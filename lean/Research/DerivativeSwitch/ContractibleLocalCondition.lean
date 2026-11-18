import Research.DerivativeSwitch.NativeSelmerCone

/-!
# Removing a contractible full local condition

The zero-to-full comparison is the inclusion of Selmer mapping fibres.
Its inverse subtracts the image of the local contracting homotopy from
the boundary cochain. Both maps preserve the global cochain literally.
-/

namespace Research.DerivativeSwitch.ContractibleLocalCondition

open CategoryTheory HomologicalComplex NativeSelmerCone

universe u
variable {R : Type u} [CommRing R]
variable {G U W L : Complex (R := R)}

noncomputable section

variable (loc : G ⟶ L) (inc : U ⟶ L) (full : W ⟶ L)

/-- Keep the shared conditions and add the full local summand. -/
def extendedCondition : pair U W ⟶ L :=
  (pairFst U W ≫ inc) + (pairSnd U W ≫ full)

private abbrev C := selmer loc inc
private abbrev Cfull := selmer loc (extendedCondition inc full)

private lemma differential (n : ℤ) (z : (C loc inc).X n) :
    (C loc inc).d n (n + 1) z =
      ((G.d (n + 1) (n + 1 + 1) z.1.1, U.d (n + 1) (n + 1 + 1) z.1.2),
        -loc.f (n + 1) z.1.1 + inc.f (n + 1) z.1.2 - L.d n (n + 1) z.2) := by
  rw [fibre_d, pair_d]
  rfl

private lemma differentialFull (n : ℤ) (z : (Cfull loc inc full).X n) :
    (Cfull loc inc full).d n (n + 1) z =
      ((G.d (n + 1) (n + 1 + 1) z.1.1,
          (U.d (n + 1) (n + 1 + 1) z.1.2.1, W.d (n + 1) (n + 1 + 1) z.1.2.2)),
        -loc.f (n + 1) z.1.1 + (inc.f (n + 1) z.1.2.1 + full.f (n + 1) z.1.2.2) -
          L.d n (n + 1) z.2) := by
  rw [fibre_d, pair_d, pair_d]
  rfl

private def includeAt (n : ℤ) : (C loc inc).X n →ₗ[R] (Cfull loc inc full).X n :=
  let gu := LinearMap.fst R ((pair G U).X (n + 1)) (L.X n)
  let g := (LinearMap.fst R _ _).comp gu
  let u := (LinearMap.snd R _ _).comp gu
  (g.prod (u.prod 0)).prod (LinearMap.snd R _ _)

@[simp] private lemma includeAt_apply (n : ℤ) (z : (C loc inc).X n) :
    includeAt loc inc full n z = ((z.1.1, (z.1.2, 0)), z.2) := rfl

/-- The orthogonal-to-conjugate comparison at a zero/full discrepancy. -/
def addCondition : C loc inc ⟶ Cfull loc inc full :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (includeAt loc inc full n)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (Cfull loc inc full).d n (n + 1) (includeAt loc inc full n z) =
      includeAt loc inc full (n + 1) ((C loc inc).d n (n + 1) z)
    rw [includeAt_apply, differentialFull, differential, includeAt_apply]
    simp)

private lemma contraction_apply (s : Homotopy (𝟙 W) 0) (n : ℤ) (w : W.X (n + 1)) :
    w = s.hom (n + 1 + 1) (n + 1) (W.d (n + 1) (n + 1 + 1) w) +
      W.d n (n + 1) (s.hom (n + 1) n w) := by
  have h := s.comm (n + 1)
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (n + 1) (n + 1 + 1) from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)] at h
  simpa using congrArg (fun f : W.X (n + 1) ⟶ W.X (n + 1) => f w) h

private def retractAt (s : Homotopy (𝟙 W) 0) (n : ℤ) :
    (Cfull loc inc full).X n →ₗ[R] (C loc inc).X n :=
  let src := (pair G (pair U W)).X (n + 1)
  let guw := LinearMap.fst R src (L.X n)
  let g := (LinearMap.fst R _ _).comp guw
  let uw := (LinearMap.snd R _ _).comp guw
  let u := (LinearMap.fst R _ _).comp uw
  let w := (LinearMap.snd R _ _).comp uw
  (g.prod u).prod (LinearMap.snd R src (L.X n) -
    (full.f n).hom.comp ((s.hom (n + 1) n).hom.comp w))

@[simp] private lemma retractAt_apply (s : Homotopy (𝟙 W) 0) (n : ℤ)
    (z : (Cfull loc inc full).X n) :
    retractAt loc inc full s n z =
      ((z.1.1, z.1.2.1), z.2 - full.f n (s.hom (n + 1) n z.1.2.2)) := rfl

/-- The chain-level inverse uses the actual local contraction. -/
def retract (s : Homotopy (𝟙 W) 0) : Cfull loc inc full ⟶ C loc inc :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (retractAt loc inc full s n)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (C loc inc).d n (n + 1) (retractAt loc inc full s n z) =
      retractAt loc inc full s (n + 1) ((Cfull loc inc full).d n (n + 1) z)
    rw [retractAt_apply, differential, differentialFull, retractAt_apply]
    apply Prod.ext
    · rfl
    change -loc.f (n + 1) z.1.1 + inc.f (n + 1) z.1.2.1 -
         (L.d n (n + 1)).hom (z.2 - full.f n (s.hom (n + 1) n z.1.2.2)) =
       -loc.f (n + 1) z.1.1 + (inc.f (n + 1) z.1.2.1 + full.f (n + 1) z.1.2.2) -
         L.d n (n + 1) z.2 -
           full.f (n + 1) (s.hom (n + 1 + 1) (n + 1) (W.d (n + 1) (n + 1 + 1) z.1.2.2))
    have hf := congrArg (fun f : W.X n ⟶ L.X (n + 1) => f (s.hom (n + 1) n z.1.2.2))
      (full.comm n (n + 1))
    simp only [ModuleCat.comp_apply] at hf
    have hs := congrArg (fun w : W.X (n + 1) => full.f (n + 1) w)
      (contraction_apply s n z.1.2.2)
    simp only [map_add] at hs
    have heq := (eq_sub_iff_add_eq).2 ((add_comm _ _).trans hs.symm)
    rw [map_sub, hf]
    rw [heq]
    abel)

theorem addCondition_global :
    addCondition loc inc full ≫ globalProjection loc (extendedCondition inc full) =
      globalProjection loc inc := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

theorem retract_global (s : Homotopy (𝟙 W) 0) :
    retract loc inc full s ≫ globalProjection loc inc =
      globalProjection loc (extendedCondition inc full) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

/-- The boundary of a lift from the added degree-one local condition. This
also applies to noncontractible finite and singular planes. -/
theorem added_condition_boundary (w : W.X 1) (hw : W.d 1 2 w = 0) :
    (Cfull loc inc full).d 0 1 ((0, (0, w)), 0) =
      (addCondition loc inc full).f 1 (pureLocal (selmerMap loc inc) 1 (full.f 1 w)) := by
  have hd := differentialFull loc inc full 0 ((0, (0, w)), 0)
  change (Cfull loc inc full).d 0 1 _ = _ at hd
  rw [hd]
  change ((G.d 1 2 0, (U.d 1 2 0, W.d 1 2 w)),
      -loc.f 1 0 + (inc.f 1 0 + full.f 1 w) - L.d 0 1 0) =
    ((0, (0, 0)), full.f 1 w)
  simp [hw]

private def homotopyAt (s : Homotopy (𝟙 W) 0) (i j : ℤ) :
    (Cfull loc inc full).X i →ₗ[R] (Cfull loc inc full).X j :=
  let guw := LinearMap.fst R ((pair G (pair U W)).X (i + 1)) (L.X i)
  let uw := (LinearMap.snd R _ _).comp guw
  let w := (LinearMap.snd R _ _).comp uw
  ((0 : (Cfull loc inc full).X i →ₗ[R] G.X (j + 1)).prod
    ((0 : (Cfull loc inc full).X i →ₗ[R] U.X (j + 1)).prod
      (-(s.hom (i + 1) (j + 1)).hom.comp w))).prod 0

private lemma homotopyAt_apply (s : Homotopy (𝟙 W) 0) (i j : ℤ)
    (z : (Cfull loc inc full).X i) : homotopyAt loc inc full s i j z =
      ((0, (0, -s.hom (i + 1) (j + 1) z.1.2.2)), 0) := rfl

/-- An explicit equivalence preserving the global term. The homotopy on the
full cone is minus the local contraction in its condition summand. -/
def comparison (s : Homotopy (𝟙 W) 0) :
    HomotopyEquiv (C loc inc) (Cfull loc inc full) where
  hom := addCondition loc inc full
  inv := retract loc inc full s
  homotopyHomInvId := Homotopy.ofEq (by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((z.1.1, z.1.2), z.2 - full.f n (s.hom (n + 1) n 0)) = z
    simp)
  homotopyInvHomId := {
    hom := fun i j => ModuleCat.ofHom (homotopyAt loc inc full s i j)
    zero := fun i j h => by
      have hj : ¬ (ComplexShape.up ℤ).Rel (j + 1) (i + 1) := by
        change ¬ (j + 1 + 1 = i + 1)
        change ¬ (j + 1 = i) at h
        omega
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change homotopyAt loc inc full s i j z = 0
      rw [homotopyAt_apply, s.zero _ _ hj]
      simp
    comm := fun n => by
      obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (m + 1) (m + 1 + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel m (m + 1) from rfl)]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change ((z.1.1, (z.1.2.1, 0)), z.2 - full.f (m + 1)
          (s.hom (m + 1 + 1) (m + 1) z.1.2.2)) =
        homotopyAt loc inc full s (m + 1 + 1) (m + 1)
            ((Cfull loc inc full).d (m + 1) (m + 1 + 1) z) +
          (Cfull loc inc full).d m (m + 1)
            (homotopyAt loc inc full s (m + 1) m z) + z
      rw [differentialFull, homotopyAt_apply, homotopyAt_apply, differentialFull]
      have hs := contraction_apply s (m + 1) z.1.2.2
      apply Prod.ext
      · change (z.1.1, (z.1.2.1, (0 : W.X (m + 1 + 1)))) = _
        simp [← neg_add, ← hs, Prod.add_def]
      · let sw := s.hom (m + 1 + 1) (m + 1) z.1.2.2
        change z.2 - full.f (m + 1) sw =
          0 + (-loc.f (m + 1) 0 + (inc.f (m + 1) 0 + full.f (m + 1) (-sw)) -
            L.d m (m + 1) 0) + z.2
        simp only [map_zero, neg_zero, zero_add, sub_zero, map_neg]
        abel }

end

end Research.DerivativeSwitch.ContractibleLocalCondition
