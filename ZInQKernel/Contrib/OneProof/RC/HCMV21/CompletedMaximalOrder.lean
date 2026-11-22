import ZInQKernel.Contrib.OneProof.RC.Adelic.FullPatch

/-! Global maximality implies maximality of the completed level-one
order. Patch a putative larger local order at just one prime. -/

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler Adelic

variable {a b : ℚ}

/-- A maximal rational quaternion order is maximal after completion.
The intersection used in lattice patching is a subring because all
the prescribed local lattices are subalgebras. -/
theorem completion_maximal_of_order_maximal (R : Order a b)
    (hmax : ∀ S : Order a b, R.ring ≤ S.ring → S.ring ≤ R.ring)
    (p : Adelic.Prime) : IsMaximalLocalOrder p.val (R.completion p.val) := by
  classical
  have hR := localLattice_full p R.full
  rw [← R.completion_toSubmodule] at hR
  refine ⟨Module.Finite.of_fg hR.fg, hR.span_eq_top, ?_⟩
  intro S hS hspan hRS
  let U (v : Adelic.Prime) : Subalgebra ℤ_[v.val] (Bp v.val a b) :=
    if h : v = p then h.symm ▸ S else R.completion v.val
  have hUp : U p = S := by simp [U]
  have hU_ne (v : Adelic.Prime) (h : v ≠ p) : U v = R.completion v.val := dite_eq_right h
  have hfinite : {v : Adelic.Prime | (U v).toSubmodule ≠ localLattice v.val R.lattice}.Finite :=
    (Set.finite_singleton p).subset fun v hv => by
      by_contra h
      exact hv (by rw [hU_ne v h, Order.completion_toSubmodule])
  obtain ⟨hf, hloc⟩ := patch R.full (fun v => (U v).toSubmodule) (fun v => by
    by_cases h : v = p
    · subst v
      rw [hUp]
      exact ⟨Module.Finite.iff_fg.mp hS, hspan⟩
    · rw [hU_ne v h, Order.completion_toSubmodule]
      exact localLattice_full v R.full) hfinite
  let T : Order a b := {
    ring := {
      carrier := {x | ∀ v, toLocal v.val x ∈ U v}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := fun hx hy v => by rw [map_add]; exact (U v).add_mem (hx v) (hy v)
      neg_mem' := fun hx v => by rw [map_neg]; exact (U v).neg_mem (hx v)
      mul_mem' := fun hx hy v => by rw [map_mul]; exact (U v).mul_mem (hx v) (hy v) }
    full := hf }
  have hRT : R.ring ≤ T.ring := by
    intro x hx v
    have hx' : toLocal v.val x ∈ R.completion v.val :=
      Algebra.subset_adjoin (Set.mem_image_of_mem _ hx)
    by_cases h : v = p
    · subst v
      rw [hUp]
      exact hRS hx'
    · rwa [hU_ne v h]
  have hTR : T.ring ≤ R.ring := hmax T hRT
  have hL : T.lattice = R.lattice := le_antisymm hTR hRT
  have hloc' : localLattice p.val T.lattice = S.toSubmodule := (hloc p).trans (congrArg _ hUp)
  rw [hL, ← Order.completion_toSubmodule] at hloc'
  exact hloc'.symm.le

end ZInQ.Manuscript.RC.HCMV21
