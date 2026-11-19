import Research.DerivativeSwitch.ContinuousSelmer
import Research.DerivativeSwitch.CompactSupportTrace
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Normalizing the continuous Selmer trace by local invariants

The inputs are maps on the actual second cohomology groups and the
reciprocity relation for restriction. The theorem constructs a chain
trace on the continuous compact-support cone with their sum as its
restriction on local cycles. This is the cochain construction, with
arithmetic local invariants and reciprocity supplied separately.
-/

namespace Research.DerivativeSwitch.ContinuousSelmerTrace

open CategoryTheory HomologicalComplex NativeSelmerCone ContinuousSelmer NativeBoundaryTrace
open scoped BigOperators

universe u
variable {R : Type u} [CommRing R]

private theorem exists_cycleLift (C : Complex (R := R)) (x : C.X 2) (hx : C.d 2 3 x = 0) :
    ∃ c : C.cycles 2, C.iCycles 2 c = x := by
  let f : ModuleCat.of R R ⟶ C.X 2 := ModuleCat.ofHom ((LinearMap.id : R →ₗ[R] R).smulRight x)
  have hf : f ≫ C.d 2 3 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (C.d 2 3).hom (a • x) = 0
    rw [map_smul, hx, smul_zero]
  have hnext : (ComplexShape.up ℤ).next 2 = 3 := (ComplexShape.up ℤ).next_eq'
    (show (ComplexShape.up ℤ).Rel 2 3 from rfl)
  let lift := C.liftCycles f 3 hnext hf
  refine ⟨lift (1 : R), ?_⟩
  have h := congrArg (fun g : ModuleCat.of R R ⟶ C.X 2 => g (1 : R))
    (C.liftCycles_i f 3 hnext hf)
  change C.iCycles 2 (lift (1 : R)) = (1 : R) • x at h
  rwa [one_smul] at h

variable [TopologicalSpace R] [Module.Injective R R]
variable {G ι : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Fintype ι]
  {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)]

variable (X : TopRep.{u} R G) (r : ∀ v, H v →ₜ* G)

/-- The restriction of a chain trace to local cycles is the sum of the
given evaluations on their cohomology classes. -/
def IsNormalized (inv : ∀ v, (localCochains X r v).homology 2 →ₗ[R] R)
    (trace : (compactSupport X r).X 2 →ₗ[R] R) : Prop :=
  ∀ z : (v : ι) → (localCochains X r v).cycles 2,
    localTrace (-(localization X r)) trace
        (fun v => (localCochains X r v).iCycles 2 (z v)) =
      ∑ v, inv v ((localCochains X r v).homologyπ 2 (z v))

/-- Arithmetic reciprocity on `H²` gives a normalized chain trace for the
single compact-support target shared by both local conditions. -/
theorem exists_normalized_trace
    (inv : ∀ v, (localCochains X r v).homology 2 →ₗ[R] R)
    (reciprocity : ∀ a : (cochains X).homology 2,
      ∑ v, inv v (homologyMap (restrict X (r v)) 2 a) = 0) :
    ∃ trace : (compactSupport X r).X 2 →ₗ[R] R,
      (∀ b : (compactSupport X r).X 1, trace ((compactSupport X r).d 1 2 b) = 0) ∧
      IsNormalized X r inv trace := by
  classical
  let L := localCochains X r
  have extInv (v : ι) : ∃ f : (L v).X 2 →ₗ[R] R,
      ∀ x : (L v).cycles 2, f ((L v).iCycles 2 x) = inv v ((L v).homologyπ 2 x) := by
    let j := (L v).iCycles 2
    have hj : Function.Injective j := (ModuleCat.mono_iff_injective j).mp inferInstance
    exact Module.Injective.out j.hom hj ((inv v).comp ((L v).homologyπ 2).hom)
  choose nu hnu using extInv
  let sumInv : (product L).X 2 →ₗ[R] R := ∑ v, (nu v).comp (LinearMap.proj v)
  have sum_apply (x : (product L).X 2) : sumInv x = ∑ v, nu v (x v) := by
    simp [sumInv, LinearMap.sum_apply]
  have hlocal (x : (product L).X 1) : sumInv ((product L).d 1 2 x) = 0 := by
    rw [sum_apply]
    apply Finset.sum_eq_zero
    intro v _
    have hd := product_d L 1 x v
    change (product L).d 1 2 x v = (L v).d 1 2 (x v) at hd
    rw [hd]
    have h1 := congrArg (fun f : (L v).X 1 ⟶ (L v).X 2 => f (x v)) ((L v).toCycles_i 1 2)
    have h2 := congrArg (fun f : (L v).X 1 ⟶ (L v).homology 2 => f (x v))
      ((L v).toCycles_comp_homologyπ 1 2)
    simp only [ModuleCat.comp_apply] at h1
    change (L v).homologyπ 2 ((L v).toCycles 1 2 (x v)) = 0 at h2
    rw [← h1, hnu, h2, map_zero]
  have hrec (x : (cochains X).X 2) (hx : (cochains X).d 2 3 x = 0) :
      sumInv ((-(localization X r)).f 2 x) = 0 := by
    obtain ⟨a, rfl⟩ := exists_cycleLift (cochains X) x hx
    change sumInv (-((localization X r).f 2 ((cochains X).iCycles 2 a))) = 0
    rw [map_neg, sum_apply, neg_eq_zero]
    rw [← reciprocity ((cochains X).homologyπ 2 a)]
    apply Finset.sum_congr rfl
    intro v _
    rw [localization_component]
    let f := restrict X (r v)
    have hi := congrArg (fun e : (cochains X).cycles 2 ⟶ (L v).X 2 => e a) (cyclesMap_i f 2)
    have hp := congrArg (fun e : (cochains X).cycles 2 ⟶ (L v).homology 2 => e a)
      (homologyπ_naturality f 2)
    simp only [ModuleCat.comp_apply] at hi hp
    change nu v (f.f 2 ((cochains X).iCycles 2 a)) = inv v (homologyMap f 2 ((cochains X).homologyπ 2 a))
    rw [← hi, hnu, hp]
  obtain ⟨trace, kills, normalized⟩ := CompactSupportTrace.exists_trace_of_reciprocity
    (-(localization X r)) sumInv hlocal hrec
  refine ⟨trace, kills, fun z => ?_⟩
  rw [normalized, sum_apply]
  exact Finset.sum_congr rfl fun v _ => hnu v (z v)

omit [Module.Injective R R] in
/-- With global degree-three exactness, the local normalization determines
the trace on all compact-support cohomology classes. -/
theorem normalized_trace_eq_on_cycles
    (inv : ∀ v, (localCochains X r v).homology 2 →ₗ[R] R)
    (hglobal : ∀ a : (cochains X).X 3, (cochains X).d 3 4 a = 0 →
      ∃ b : (cochains X).X 2, (cochains X).d 2 3 b = a)
    (trace trace' : (compactSupport X r).X 2 →ₗ[R] R)
    (kills : ∀ b : (compactSupport X r).X 1, trace ((compactSupport X r).d 1 2 b) = 0)
    (kills' : ∀ b : (compactSupport X r).X 1, trace' ((compactSupport X r).d 1 2 b) = 0)
    (normalized : IsNormalized X r inv trace) (normalized' : IsNormalized X r inv trace')
    (z : (compactSupport X r).X 2) (hz : (compactSupport X r).d 2 3 z = 0) :
    trace z = trace' z := by
  apply CompactSupportTrace.trace_eq_on_cycles (-(localization X r)) hglobal trace trace' kills kills' _ z hz
  intro t ht
  have hlocal (v : ι) : (localCochains X r v).d 2 3 (t v) = 0 := by
    exact (product_d (localCochains X r) 2 t v).symm.trans (congrFun ht v)
  choose c hc using fun v => exists_cycleLift (localCochains X r v) (t v) (hlocal v)
  rw [← funext hc, normalized c, normalized' c]

end Research.DerivativeSwitch.ContinuousSelmerTrace
