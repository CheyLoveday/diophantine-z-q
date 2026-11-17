import Research.DerivativeSwitch.NativeBoundaryTrace
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Compact-support trace from the sum of local invariants

Reciprocity on global degree-two cycles lets the sum of local invariants
factor through the global differential. Extending this factor to degree
three constructs a representative of the compact-support trace.
-/

namespace Research.DerivativeSwitch.CompactSupportTrace

open CategoryTheory
open NativeSelmerCone NativeBoundaryTrace

universe u
variable {R : Type u} [CommRing R]
variable {A T : Complex (R := R)} (res : A ⟶ T)

/-- Given local cochain representatives of the invariants, construct a trace
whose restriction is strictly the sum of those representatives. Reciprocity
is needed only on global cycles. -/
theorem exists_trace_of_reciprocity [Module.Injective R R]
    (inv : T.X 2 →ₗ[R] R) (hlocal : ∀ x, inv (T.d 1 2 x) = 0)
    (hrec : ∀ x, A.d 2 3 x = 0 → inv (res.f 2 x) = 0) :
    ∃ trace : (fibre res).X 2 →ₗ[R] R,
      (∀ x : (fibre res).X 1, trace ((fibre res).d 1 2 x) = 0) ∧
      localTrace res trace = inv := by
  let d := (A.d 2 3).hom
  let eval := inv.comp (res.f 2).hom
  let descend := (LinearMap.ker d).liftQ eval
    (fun x hx => LinearMap.mem_ker.mpr (hrec x (LinearMap.mem_ker.mp hx)))
  let onImage := descend.comp d.quotKerEquivRange.symm.toLinearMap
  obtain ⟨correction, hc⟩ := Module.Injective.out (LinearMap.range d).subtype
    Subtype.val_injective onImage
  have hcorr (x : A.X 2) : correction (A.d 2 3 x) = inv (res.f 2 x) := by
    have h := hc ⟨d x, LinearMap.mem_range_self d x⟩
    change correction (d x) =
      descend (d.quotKerEquivRange.symm ⟨d x, LinearMap.mem_range_self d x⟩) at h
    rwa [LinearMap.quotKerEquivRange_symm_apply_image] at h
  let trace : (fibre res).X 2 →ₗ[R] R :=
    inv.comp (LinearMap.snd R _ _) - correction.comp (LinearMap.fst R _ _)
  refine ⟨trace, ?_, ?_⟩
  · intro x
    change inv (res.f 2 x.1 - T.d 1 2 x.2) - correction (A.d 2 3 x.1) = 0
    rw [map_sub, hlocal, sub_zero, hcorr, sub_self]
  · ext t
    change inv t - correction 0 = inv t
    rw [map_zero, sub_zero]

/-- When global degree-three cohomology vanishes, two chain traces inducing
the same sum of local invariants agree on all compact-support cycles. -/
theorem trace_eq_on_cycles
    (hglobal : ∀ a : A.X 3, A.d 3 4 a = 0 → ∃ b : A.X 2, A.d 2 3 b = a)
    (trace trace' : (fibre res).X 2 →ₗ[R] R)
    (htrace : ∀ x : (fibre res).X 1, trace ((fibre res).d 1 2 x) = 0)
    (htrace' : ∀ x : (fibre res).X 1, trace' ((fibre res).d 1 2 x) = 0)
    (hlocal : ∀ t : T.X 2, T.d 2 3 t = 0 → localTrace res trace t = localTrace res trace' t)
    (z : (fibre res).X 2) (hz : (fibre res).d 2 3 z = 0) :
    trace z = trace' z := by
  change (A.d 3 4 z.1, res.f 3 z.1 - T.d 2 3 z.2) = (0, 0) at hz
  obtain ⟨b, hb⟩ := hglobal z.1 (congrArg Prod.fst hz)
  let w : (fibre res).X 1 := (b, 0)
  let t := z.2 - res.f 2 b
  have ht : T.d 2 3 t = 0 := by
    have hcycle : res.f 3 z.1 - T.d 2 3 z.2 = 0 := congrArg Prod.snd hz
    have hcomm : T.d 2 3 (res.f 2 b) = res.f 3 (A.d 2 3 b) := by
      simpa only [ModuleCat.comp_apply] using congrArg
        (fun f : A.X 2 ⟶ T.X 3 => f b) (res.comm 2 3)
    change (T.d 2 3).hom (z.2 - res.f 2 b) = 0
    rw [map_sub]
    change T.d 2 3 z.2 - T.d 2 3 (res.f 2 b) = 0
    rw [hcomm, hb, sub_eq_zero]
    exact (sub_eq_zero.mp hcycle).symm
  have hz' : z = pureLocal res 2 t + (fibre res).d 1 2 w := by
    apply Prod.ext
    · change z.1 = (0 : A.X 3) + A.d 2 3 b
      rw [zero_add, hb]
    · change z.2 = (z.2 - res.f 2 b) + (res.f 2 b - T.d 1 2 0)
      simp
  rw [hz', map_add, map_add, htrace, htrace', add_zero, add_zero]
  exact hlocal t ht

end Research.DerivativeSwitch.CompactSupportTrace
