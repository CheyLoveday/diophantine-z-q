import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Specialization of finite-group matrix representations to ℂ

Adjoin the entries of the given representation to the coefficient field. A maximal
ideal of the resulting finite-type algebra has residue field finite over the
coefficient field by Zariski's lemma. Its embedding into ℂ extends the prescribed
embedding of the coefficient field; no embedding of the original field is needed.
-/

namespace DeligneSerre

/-- A matrix representation over a field containing `K` whose traces and determinants
are prescribed in `K` gives a complex representation of the same finite group. The
`K`-algebra structure on `ℂ` specifies the embedding used for the prescribed values. -/
theorem exists_complex_representation_of_trace_det
    {K L H n : Type*} [Field K] [Field L] [Algebra K L] [Algebra K ℂ]
    [Group H] [Finite H] [Fintype n] [DecidableEq n]
    (ρ : H →* Matrix.GeneralLinearGroup n L) (t d : H → K)
    (ht : ∀ h, Matrix.trace (↑(ρ h) : Matrix n n L) = algebraMap K L (t h))
    (hd : ∀ h, Matrix.det (↑(ρ h) : Matrix n n L) = algebraMap K L (d h)) :
    ∃ σ : H →* Matrix.GeneralLinearGroup n ℂ, ∀ h,
      Matrix.trace (↑(σ h) : Matrix n n ℂ) = algebraMap K ℂ (t h) ∧
      Matrix.det (↑(σ h) : Matrix n n ℂ) = algebraMap K ℂ (d h) := by
  let entries : H × n × n → L := fun (h, i, j) => (ρ h : Matrix n n L) i j
  let A : Subalgebra K L := Algebra.adjoin K (Set.range entries)
  let M : H → Matrix n n A := fun h i j =>
    ⟨entries (h, i, j), Algebra.subset_adjoin ⟨(h, i, j), rfl⟩⟩
  let ι : A →+* L := A.val.toRingHom
  have hM (h : H) : ι.mapMatrix (M h) = (ρ h : Matrix n n L) := rfl
  have hinj : Function.Injective (ι.mapMatrix : Matrix n n A →+* Matrix n n L) := by
    intro X Y hXY
    exact Matrix.ext fun i j => Subtype.ext (congrArg (fun Z : Matrix n n L => Z i j) hXY)
  let ρA : H →* Matrix n n A :=
    { toFun := M
      map_one' := hinj (by rw [hM, map_one, map_one]; rfl)
      map_mul' := fun x y => hinj (by
        rw [hM, (ι.mapMatrix : Matrix n n A →+* Matrix n n L).map_mul,
          hM x, hM y, ρ.map_mul]
        rfl) }
  have htA (h : H) : (M h).trace = algebraMap K A (t h) := by
    apply Subtype.ext
    change ι (M h).trace = algebraMap K L (t h)
    rw [AddMonoidHom.map_trace ι, show (M h).map ι = (ρ h : Matrix n n L) from hM h]
    exact ht h
  have hdA (h : H) : (M h).det = algebraMap K A (d h) := by
    apply Subtype.ext
    change ι (M h).det = algebraMap K L (d h)
    rw [ι.map_det, hM]
    exact hd h
  let : Algebra.FiniteType K A := Algebra.FiniteType.adjoin_of_finite (Set.finite_range entries)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  let e : (A ⧸ m) →ₐ[K] ℂ := IsAlgClosed.lift
  let f : A →ₐ[K] ℂ := e.comp (Ideal.Quotient.mkₐ K m)
  -- The homomorphism from `H` already includes the inverse matrices, at `h⁻¹`.
  let σ := (f.toRingHom.mapMatrix.toMonoidHom.comp ρA).toHomUnits
  refine ⟨σ, fun h => ⟨?_, ?_⟩⟩
  · change ((M h).map f).trace = algebraMap K ℂ (t h)
    rw [← AddMonoidHom.map_trace f, htA, f.commutes]
  · change (f.mapMatrix (M h)).det = algebraMap K ℂ (d h)
    rw [← f.map_det, hdA, f.commutes]

end DeligneSerre
