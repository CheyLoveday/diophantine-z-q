import ZInQKernel.Contrib.OneProof.CharPolyLattice

/-! degpoly-proof scratch, part C: for `ψ` with finite kernel on `A(ℂ)`, `#ker ψ(ℂ) = det_ℤ(M_ψ|_Λ) > 0`. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace DegPolyScratch

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.LeafPush2 (CPts IsUniformization)
open ZInQ.Contrib.OneProof.CharPolyLattice

variable {K : Type} [Field K] [Algebra K ℂ] {A : PkgI3.AbVar K} {g : ℕ}
  {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
  {Φ : (Fin g → ℂ) → CPts A (algebraMap K ℂ)}

theorem unif_nsmul (hA : IsUniformization (algebraMap K ℂ) Λ Φ) (n : ℕ) (z : Fin g → ℂ) :
    Φ (n • z) = Φ z ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    exact (hA.2.1 0).2 (zero_mem _)
  | succ n ih => rw [succ_nsmul, hA.1, ih, pow_succ]

/-- **`#ker ψ(ℂ) = det_ℤ(M_ψ|_Λ)` and `det > 0`, when the kernel is finite.** -/
theorem card_ker_eq_det (hA : IsUniformization (algebraMap K ℂ) Λ Φ) (ψ : PkgI3.AbVar.End A)
    (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hM : ∀ z, Φ (M z) = Φ z ≫ ψ.hom)
    (hMlat : ∀ lam : Λ, M lam ∈ Λ) (hfin : Finite (PkgI3.AbVar.ptMap (L := ℂ) ψ).ker) :
    haveI := ZLattice.module_finite ℝ Λ
    haveI := ZLattice.module_free ℝ Λ
    ((Nat.card (PkgI3.AbVar.ptMap (L := ℂ) ψ).ker : ℕ) : ℤ) = LinearMap.det (latEnd Λ M hMlat) ∧
      0 < LinearMap.det (latEnd Λ M hMlat) := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  set KC := (PkgI3.AbVar.ptMap (L := ℂ) ψ).ker with hKC
  set X := latEnd Λ M hMlat with hX
  have hmem : ∀ z, M z ∈ Λ → (Φ z : PkgI3.AbVar.Pt ℂ A) ∈ KC := by
    intro z hz
    refine MonoidHom.mem_ker.mpr ?_
    change Φ z ≫ ψ.hom = 1
    rw [← hM]
    exact (hA.2.1 _).2 hz
  -- `M` is injective
  have hMinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    set N := Nat.card KC with hNdef
    have hN : 0 < N := Nat.card_pos
    have key : ∀ w, M w = 0 → N • w ∈ Λ := by
      intro w hw
      have hw' : Φ w ∈ KC := hmem w (by rw [hw]; exact zero_mem _)
      have h1 : (⟨Φ w, hw'⟩ : KC) ^ N = 1 := pow_card_eq_one'
      rw [← hA.2.1, unif_nsmul hA]
      exact congrArg Subtype.val h1
    apply HDec.G0Galois.eq_zero_of_real_smul_mem Λ z
    intro t
    have h2 := key (((t / N : ℝ) : ℂ) • z) (by rw [map_smul, hz, smul_zero])
    convert h2 using 1
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Complex.coe_smul]
    congr 1
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp
  have hMsurj : Function.Surjective M := LinearMap.injective_iff_surjective.mp hMinj
  set Me := LinearEquiv.ofBijective M ⟨hMinj, hMsurj⟩ with hMe
  have hMe_apply : ∀ z, M (Me.symm z) = z := fun z => Me.apply_symm_apply z
  have hXinj : Function.Injective X := fun a b h =>
    Subtype.ext (hMinj (congrArg Subtype.val h))
  -- the map `Λ → ker`, `m ↦ Φ(M⁻¹ m)`
  have hmemf : ∀ m : Λ, (Φ (Me.symm m) : PkgI3.AbVar.Pt ℂ A) ∈ KC := fun m =>
    hmem _ (by rw [hMe_apply]; exact m.2)
  let f : Λ →+ Additive KC :=
    { toFun := fun m => Additive.ofMul ⟨Φ (Me.symm m), hmemf m⟩
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change Φ (Me.symm ((0 : Λ) : Fin g → ℂ)) = 1
        rw [Submodule.coe_zero, map_zero]
        exact (hA.2.1 0).2 (zero_mem _)
      map_add' := fun m n' => by
        apply Additive.toMul.injective
        apply Subtype.ext
        change Φ (Me.symm ((m + n' : Λ) : Fin g → ℂ)) = Φ (Me.symm m) * Φ (Me.symm n')
        rw [Submodule.coe_add, map_add, hA.1] }
  have hfsurj : Function.Surjective f := by
    intro P
    obtain ⟨z, hz⟩ := hA.2.2.1 (Additive.toMul P).1
    have hzΛ : M z ∈ Λ := by
      rw [← hA.2.1, hM, hz]
      exact (Additive.toMul P).2
    refine ⟨⟨M z, hzΛ⟩, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change Φ (Me.symm (M z)) = _
    have : Me.symm (M z) = z := Me.symm_apply_apply z
    rw [this, hz]
  have hker : f.ker = (LinearMap.range X).toAddSubgroup := by
    ext m
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
    constructor
    · intro h
      have h1 : Φ (Me.symm m) = 1 := congrArg Subtype.val (congrArg Additive.toMul h)
      rw [hA.2.1] at h1
      exact ⟨⟨_, h1⟩, Subtype.ext (hMe_apply m)⟩
    · rintro ⟨n', rfl⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      change Φ (Me.symm (M n')) = 1
      have : Me.symm (M n') = n' := Me.symm_apply_apply _
      rw [this]
      exact (hA.2.1 _).2 n'.2
  have hidx : Nat.card (Λ ⧸ LinearMap.range X) = Nat.card KC := by
    calc Nat.card (Λ ⧸ LinearMap.range X) = Nat.card (Λ ⧸ (LinearMap.range X).toAddSubgroup) := rfl
      _ = Nat.card (Λ ⧸ f.ker) := by rw [hker]
      _ = Nat.card (Additive KC) :=
        Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv
      _ = Nat.card KC := rfl
  have hdet := Submodule.natAbs_det_equiv (LinearMap.range X) (LinearEquiv.ofInjective X hXinj)
  have hdet2 : (LinearMap.det X).natAbs = Nat.card (Λ ⧸ LinearMap.range X) := by
    convert hdet using 3
    exact LinearMap.ext fun _ => rfl
  rw [hidx] at hdet2
  clear hdet
  have hdet := hdet2
  -- the sign: `det_ℤ X = det_ℝ M = |det_ℂ M|²`
  have hpos : 0 ≤ LinearMap.det X := by
    let bE := Module.Free.chooseBasis ℤ Λ
    let bR := bE.ofZLatticeBasis ℝ Λ
    have h1 : ((LinearMap.det X : ℤ) : ℝ) = LinearMap.det (M.restrictScalars ℝ) := by
      rw [← LinearMap.det_toMatrix bE, ← LinearMap.det_toMatrix bR]
      have hm := (Int.castRingHom ℝ).map_det (LinearMap.toMatrix bE bE X)
      rw [eq_intCast] at hm
      rw [hm]
      congr 1
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
        LinearMap.toMatrix_apply, Module.Basis.ofZLatticeBasis_apply, LinearMap.restrictScalars_apply]
      change _ = bR.repr ((X (bE j) : Λ) : Fin g → ℂ) i
      rw [Module.Basis.ofZLatticeBasis_repr_apply]
      rfl
    have h2 : LinearMap.det (M.restrictScalars ℝ) = Complex.normSq (LinearMap.det M) := by
      rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
    have h3 : (0 : ℝ) ≤ ((LinearMap.det X : ℤ) : ℝ) := by
      rw [h1, h2]; exact Complex.normSq_nonneg _
    exact_mod_cast h3
  have hne : LinearMap.det X ≠ 0 := by
    intro h0
    rw [h0, Int.natAbs_zero] at hdet
    exact (Nat.card_pos (α := KC)).ne' hdet.symm
  refine ⟨?_, lt_of_le_of_ne hpos (Ne.symm hne)⟩
  rw [← hdet, Int.natAbs_of_nonneg hpos]

end DegPolyScratch
