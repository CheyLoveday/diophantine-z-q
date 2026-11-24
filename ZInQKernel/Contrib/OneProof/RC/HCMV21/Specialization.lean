import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Module.Torsion.Basic

namespace ZInQ.Manuscript.RC.HCMV21

/-- If the composite with the dual is multiplication by `n`, the full isogeny
kernel lies in the `n`-torsion, on either fibre. -/
theorem ker_le_torsion_of_dual_comp {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (g : B →+ A) (n : ℤ) (h : ∀ x, g (f x) = n • x) :
    f.ker ≤ AddSubgroup.torsionBy A n := by
  intro x hx
  change n • x = 0
  rw [← h, AddMonoidHom.mem_ker.mp hx, map_zero]

/-- For a commuting square of prime-to-residue-characteristic torsion groups,
if the two vertical specialization maps are isomorphisms, specialization is
also an isomorphism on the isogeny kernels inside those torsion groups. -/
def specializeKernel {A B A' B' : Type*} [AddGroup A] [AddGroup B]
    [AddGroup A'] [AddGroup B'] (f : A →+ B) (f' : A' →+ B') (rA : A ≃+ A')
    (rB : B ≃+ B') (h : ∀ x, f' (rA x) = rB (f x)) : f.ker ≃+ f'.ker where
  toFun x := ⟨rA x.1, by rw [AddMonoidHom.mem_ker, h, x.2, map_zero]⟩
  invFun y := ⟨rA.symm y.1, by
    apply AddMonoidHom.mem_ker.mpr
    apply rB.injective
    rw [← h, AddEquiv.apply_symm_apply, y.2, map_zero]⟩
  left_inv x := Subtype.ext (AddEquiv.symm_apply_apply _ _)
  right_inv y := Subtype.ext (AddEquiv.apply_symm_apply _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)

end ZInQ.Manuscript.RC.HCMV21
