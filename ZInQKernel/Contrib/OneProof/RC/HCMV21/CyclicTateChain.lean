import ZInQKernel.Contrib.OneProof.RC.HCMV21.TateHomLattice
import ZInQKernel.Contrib.OneProof.RC.HCMV21.SplitCoset

/-! Put the actual Tate preimage of a cyclic level subgroup in the
standard split chain. This uses no restriction on the parity of the
level prime. -/

namespace ZInQ.Manuscript.RC.HCMV21

open PkgI3.AbVar
open scoped CategoryTheory.MonObj Matrix

variable {k : Type} [Field k] {A : PkgI3.AbVar k}
  (p : ℕ) [Fact p.Prime]

/-- A generator of exact order `p^n` lifts to a primitive Tate vector.
The integral level preimage is the line it generates together with
`p^n` times the whole Tate lattice. -/
theorem tateLevelPreimage_of_cyclic_generator
    (hp : (p : k) ≠ 0) (n : ℕ) (hn : 0 < n)
    (P : A.Pt (AlgebraicClosure k)) (hP : orderOf P = p ^ n) :
    ∃ x : A.T p, (¬ ∃ z : A.T p, x = (p : ℤ_[p]) • z) ∧
      ∀ y : A.T p, y ∈ tateLevelPreimage A p n (Subgroup.zpowers P) ↔
        ∃ (a : ℤ_[p]) (z : A.T p), y = a • x + (p : ℤ_[p]) ^ n • z := by
  have hpP : P ^ p ^ n = 1 := hP ▸ pow_orderOf_eq_one P
  have htor : p ^ n • Additive.ofMul P = 0 := congrArg Additive.ofMul hpP
  obtain ⟨x, hx⟩ := ZInQ.Contrib.TateLatticeTorsion.exists_tateCoord_of_torsion
    (surjective_nsmul_of_ne_zero A p hp) htor
  refine ⟨x, ?_, fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨z, hz⟩
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have he : x.1 (e + 1) = z.1 e := by
      rw [hz, Nat.cast_smul_eq_nsmul ℤ_[p]]
      exact z.2.2 e
    have ht := PkgI3.Tate.pow_smul_eq_zero z.2 e
    rw [← he, hx] at ht
    have hpow : P ^ (p ^ e) = 1 := congrArg
      (fun t : Additive (A.Pt (AlgebraicClosure k)) => Additive.toMul t) ht
    have hdiv := orderOf_dvd_of_pow_eq_one hpow
    rw [hP] at hdiv
    exact (not_le_of_gt (pow_lt_pow_right₀ (Fact.out : p.Prime).one_lt (Nat.lt_succ_self e)))
      (Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _) hdiv)
  · intro hy
    have hfin : IsOfFinOrder P := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos _, hpP⟩
    obtain ⟨m, hm⟩ := hfin.mem_powers_iff_mem_zpowers.mpr hy
    have hm' : y.1 n = m • x.1 n := by
      rw [hx]
      exact (congrArg Additive.ofMul hm).symm
    have hz : (y - m • x).1 n = 0 := by
      change y.1 n - m • x.1 n = 0
      rw [hm', sub_self]
    obtain ⟨z, hz⟩ := (PkgI3.Tate.coord_eq_zero_iff _ _).mp hz
    refine ⟨m, z, ?_⟩
    rw [Nat.cast_smul_eq_nsmul ℤ_[p], ← hz]
    abel
  · rintro ⟨a, z, rfl⟩
    have hz : (((p : ℤ_[p]) ^ n) • z).1 n = 0 :=
      (PkgI3.Tate.coord_eq_zero_iff _ _).mpr ⟨z, rfl⟩
    change Additive.toMul ((a • x).1 n + (((p : ℤ_[p]) ^ n) • z).1 n) ∈ Subgroup.zpowers P
    rw [hz, add_zero, PkgI3.Tate.smul_apply, hx]
    exact (Subgroup.zpowers P).pow_mem (Subgroup.mem_zpowers P) _

private theorem exists_linearEquiv_of_primitive (x : Fin 2 → ℤ_[p])
    (hx : ¬ ∃ y : Fin 2 → ℤ_[p], x = (p : ℤ_[p]) • y) :
    ∃ f : (Fin 2 → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]),
      f (Pi.single 0 1) = x := by
  classical
  have hu : IsUnit (x 0) ∨ IsUnit (x 1) := by
    by_contra! h
    have hdiv (i : Fin 2) : ∃ z : ℤ_[p], x i = (p : ℤ_[p]) * z := by
      have hi : ¬ IsUnit (x i) := by
        fin_cases i
        · exact h.1
        · exact h.2
      have hm : x i ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
        (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hi)
      rw [PadicInt.maximalIdeal_eq_span_p] at hm
      exact Ideal.mem_span_singleton.mp hm
    choose y hy using hdiv
    exact hx ⟨y, funext hy⟩
  let b := Pi.basisFun ℤ_[p] (Fin 2)
  let d (i j : Fin 2) : ℤ_[p] := if j = i then 1 else 0
  have hmk (i : Fin 2) (hdet : IsUnit (Matrix.det !![x 0, d i 0; x 1, d i 1])) :
      ∃ f : (Fin 2 → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]), f (Pi.single 0 1) = x := by
    let M : Matrix (Fin 2) (Fin 2) ℤ_[p] := !![x 0, d i 0; x 1, d i 1]
    let l := Matrix.toLin b b M
    have hl : IsUnit (LinearMap.toMatrix b b l).det := by
      rw [show LinearMap.toMatrix b b l = M from LinearMap.toMatrix_toLin b b M]
      exact hdet
    refine ⟨LinearEquiv.ofIsUnitDet hl, ?_⟩
    change l (Pi.single 0 1) = x
    rw [show Pi.single 0 (1 : ℤ_[p]) = b 0 from (Pi.basisFun_apply _ _ _).symm]
    dsimp only [l]
    rw [Matrix.toLin_self]
    have hm (j : Fin 2) : M j 0 = x j := by fin_cases j <;> rfl
    simp only [Fin.sum_univ_two, hm, b, Pi.basisFun_apply]
    funext j
    fin_cases j <;> simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases hu with h | h
  · exact hmk 1 (by simpa [Matrix.det_fin_two_of, d] using h)
  · exact hmk 0 (by simpa [Matrix.det_fin_two_of, d] using h.neg)

/-- The actual cyclic subgroup determines the standard integral split
chain. Exchanging the two basis vectors gives the other placement
used when recording the label. -/
theorem exists_tateLevelPreimage_standard
    (hp : (p : k) ≠ 0) (n : ℕ) (hn : 0 < n)
    (P : A.Pt (AlgebraicClosure k)) (hP : orderOf P = p ^ n)
    (b : Module.Basis (Fin 2) ℤ_[p] (A.T p)) :
    ∃ e : A.T p ≃ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]),
      ∀ y, y ∈ tateLevelPreimage A p n (Subgroup.zpowers P) ↔
        e y ∈ splitLevelLattice p 0 n := by
  obtain ⟨x, hprim, hspan⟩ := tateLevelPreimage_of_cyclic_generator p hp n hn P hP
  obtain ⟨f, hf⟩ := exists_linearEquiv_of_primitive p (b.equivFun x) (by
    rintro ⟨v, hv⟩
    apply hprim
    refine ⟨b.equivFun.symm v, b.equivFun.injective ?_⟩
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact hv)
  let e := b.equivFun.trans f.symm
  have hx : e x = Pi.single 0 1 := f.symm_apply_eq.mpr hf.symm
  refine ⟨e, fun y => (hspan y).trans ?_⟩
  constructor
  · rintro ⟨a, z, rfl⟩
    refine ⟨by simp, (e z) 1, ?_⟩
    change e (a • x + (p : ℤ_[p]) ^ n • z) 1 = (p : ℤ_[p]) ^ n * e z 1
    simp [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx]
  · rintro ⟨_, c, hc⟩
    refine ⟨e y 0, e.symm ![0, c], e.injective ?_⟩
    rw [map_add, map_smul, map_smul, hx, LinearEquiv.apply_symm_apply]
    funext j
    fin_cases j <;> simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc]

end ZInQ.Manuscript.RC.HCMV21
