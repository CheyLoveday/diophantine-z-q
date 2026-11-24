import ZInQKernel.Contrib.OneProof.RC.HCMV21.PrimeToGeometry
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! Integral Tate coordinates away from the detector. Saturation of
geometric morphisms and equality of ranks give the level-one comparison.
Finite accuracy in those coordinates then imposes the actual level. -/

namespace ZInQ.Manuscript.RC.HCMV21

open PkgI3.AbVar
open scoped BigOperators Matrix CategoryTheory.MonObj

private theorem padic_exists_nat_add_pow_mul {p : ℕ} [Fact p.Prime] (n : ℕ)
    (x : ℤ_[p]) : ∃ (m : ℕ) (y : ℤ_[p]), x = m + (p : ℤ_[p]) ^ n * y := by
  let m := (PadicInt.toZModPow n x).val
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hmem : x - (m : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast]
    rw [show (m : ZMod (p ^ n)) = PadicInt.toZModPow n x from ZMod.natCast_zmod_val _,
      sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨m, y, by rw [← hy]; ring⟩

/-- Integral maps already approximate their completed span modulo any
power of the prime. -/
theorem exists_add_pow_smul_of_mem_span {p : ℕ} [Fact p.Prime] {H M : Type*}
    [AddCommGroup H] [AddCommGroup M] [Module ℤ_[p] M] (f : H →+ M)
    (n : ℕ) {x : M} (hx : x ∈ Submodule.span ℤ_[p] (Set.range f)) :
    ∃ h : H, ∃ y : M, x = f h + (p : ℤ_[p]) ^ n • y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    exact ⟨h, 0, by simp⟩
  | zero => exact ⟨0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, z, rfl⟩ := hx
    obtain ⟨b, w, rfl⟩ := hy
    exact ⟨a + b, z + w, by rw [map_add, smul_add]; abel⟩
  | smul c x _ hx =>
    obtain ⟨a, z, rfl⟩ := hx
    obtain ⟨m, y, hy⟩ := padic_exists_nat_add_pow_mul n c
    refine ⟨m • a, y • f a + c • z, ?_⟩
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_add, smul_add, ← add_assoc]
    congr 1
    · rw [smul_smul, ← add_smul, ← hy]
    · exact smul_comm c ((p : ℤ_[p]) ^ n) z

/-- Integral Tate saturation and equal ranks suffice for the full
integral comparison. The hypothesis on `d` is the dimension of the
Tate Hom module, which is four for two rank-two Tate modules. -/
theorem span_homT_eq_top_of_basis {k : Type} [Field k] {A B : PkgI3.AbVar k}
    (p d : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0)
    (e : Module.Basis (Fin d) ℤ (Hom A B))
    (b : Module.Basis (Fin d) ℤ_[p] (A.T p →ₗ[ℤ_[p]] B.T p)) :
    Submodule.span ℤ_[p] (Set.range (tateHom p A B)) = ⊤ := by
  classical
  let M : Matrix (Fin d) (Fin d) ℤ_[p] := fun i j => b.repr (homT (e j)) i
  let Mbar : Matrix (Fin d) (Fin d) (ZMod p) := M.map PadicInt.toZMod
  have hMbar : Function.Injective Mbar.mulVec := by
    apply (injective_iff_map_eq_zero Mbar.mulVecLin).mpr
    intro v hv
    let a (i : Fin d) : ℕ := (v i).val
    have ha (i : Fin d) : (a i : ZMod p) = v i := ZMod.natCast_zmod_val _
    let f : Hom A B := ∑ j, a j • e j
    have hMf (i : Fin d) : b.repr (homT f) i = (M.mulVec fun j => (a j : ℤ_[p])) i := by
      change b.repr (tateHom p A B (∑ j, a j • e j)) i = _
      simp only [map_sum, map_nsmul, Finsupp.finsetSum_apply, Finsupp.coe_nsmul, Pi.smul_apply,
        Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      change a j • M i j = M i j * (a j : ℤ_[p])
      rw [← Nat.cast_smul_eq_nsmul ℤ_[p], smul_eq_mul, mul_comm]
    have hdiv (i : Fin d) : ∃ z : ℤ_[p], b.repr (homT f) i = (p : ℤ_[p]) * z := by
      have hred : PadicInt.toZMod (b.repr (homT f) i) = 0 := by
        rw [hMf, RingHom.map_mulVec]
        have he : (fun j => PadicInt.toZMod (a j : ℤ_[p])) = v := by
          funext j
          rw [map_natCast, ha]
        change Mbar.mulVec (fun j => PadicInt.toZMod (a j : ℤ_[p])) i = 0
        rw [he]
        exact congrFun hv i
      have hz : b.repr (homT f) i ∈ Ideal.span {(p : ℤ_[p])} := by
        rwa [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact Ideal.mem_span_singleton.mp hz
    choose z hz using hdiv
    let ψ := b.equivFun.symm z
    have hf : homT (ℓ := p) f = (p : ℤ_[p]) • ψ := by
      apply b.equivFun.injective
      funext i
      rw [map_smul, Pi.smul_apply, LinearEquiv.apply_symm_apply]
      exact hz i
    obtain ⟨g, hg⟩ := exists_eq_nsmul_of_primeTo_homT_dvd f p 1 hp (fun x => by
      refine ⟨ψ x, ?_⟩
      rw [hf, pow_one, LinearMap.smul_apply])
    ext i
    have hgi := congrArg (fun h => e.repr h i) hg
    have hrep : e.repr f i = (a i : ℤ) := by
      simp [f, Finsupp.single_apply, eq_comm]
    rw [hrep, pow_one, map_nsmul, Finsupp.coe_nsmul, Pi.smul_apply,
      ← Nat.cast_smul_eq_nsmul ℤ, smul_eq_mul] at hgi
    have hzi := congrArg (Int.castRingHom (ZMod p)) hgi
    change v i = 0
    simpa [ha] using hzi
  have hdet : IsUnit M.det := by
    have hbar := (Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hMbar)
    by_contra h
    have hmax : M.det ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
    have hz : PadicInt.toZMod M.det = 0 := RingHom.mem_ker.mp
      (by simpa only [PadicInt.ker_toZMod] using hmax)
    rw [PadicInt.toZMod.map_det] at hz
    exact hbar.ne_zero hz
  apply top_unique
  intro φ _
  obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hdet) (b.equivFun φ)
  have heq : φ = ∑ j, v j • homT (ℓ := p) (e j) := by
    apply b.equivFun.injective
    funext i
    have hi := congrFun hv i
    simpa [M, Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm] using hi.symm
  rw [heq]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨e j, rfl⟩)

section Level

variable {k : Type} [Field k] {A B : PkgI3.AbVar k}
  (p n : ℕ) [Fact p.Prime]

/-- The actual level preimage regarded as an integral submodule. The
scalar action on its defining torsion coordinate factors through
`ℤ/p^nℤ`. -/
def tateLevelSubmodule (C : Subgroup (B.Pt (AlgebraicClosure k))) :
    Submodule ℤ_[p] (B.T p) where
  carrier := tateLevelPreimage B p n C
  zero_mem' := C.one_mem
  add_mem' hx hy := C.mul_mem hx hy
  smul_mem' r _ hx := C.pow_mem hx (PadicInt.toZModPow n r).val

private theorem tateLevelSubmodule_mem_pow_smul
    (D : Subgroup (B.Pt (AlgebraicClosure k))) (x : B.T p) :
    (p : ℤ_[p]) ^ n • x ∈ tateLevelSubmodule p n D := by
  change Additive.toMul (((p : ℤ_[p]) ^ n • x).1 n) ∈ D
  rw [(PkgI3.Tate.coord_eq_zero_iff _ _).mpr ⟨x, rfl⟩]
  exact D.one_mem

/-- The completed enhanced Hom lattice consists of all the integral
Tate maps preserving the preimages of the actual level subgroups.
The level condition survives completion because it can be tested
on the single torsion coordinate at exponent `n`. -/
theorem span_levelHom_eq_tateLevelMaps
    (hp : (p : k) ≠ 0)
    (C : Subgroup (A.Pt (AlgebraicClosure k))) (D : Subgroup (B.Pt (AlgebraicClosure k)))
    (hC : ∀ P ∈ C, P ^ (p ^ n) = 1)
    (hfull : Submodule.span ℤ_[p] (Set.range (tateHom p A B)) = ⊤) :
    (Submodule.span ℤ_[p] (tateHom p A B '' (levelHom C D : Set (Hom A B))) :
      Set (A.T p →ₗ[ℤ_[p]] B.T p)) =
      {φ : A.T p →ₗ[ℤ_[p]] B.T p | Set.MapsTo (⇑φ) (tateLevelPreimage A p n C) (tateLevelPreimage B p n D)} := by
  let maps : Submodule ℤ_[p] (A.T p →ₗ[ℤ_[p]] B.T p) :=
    { carrier := {φ : A.T p →ₗ[ℤ_[p]] B.T p | Set.MapsTo (⇑φ) (tateLevelPreimage A p n C) (tateLevelPreimage B p n D)}
      zero_mem' := fun _ _ => (tateLevelSubmodule p n D).zero_mem
      add_mem' := fun hf hg x hx => (tateLevelSubmodule p n D).add_mem (hf hx) (hg hx)
      smul_mem' := fun r _ hf x hx => (tateLevelSubmodule p n D).smul_mem r (hf hx) }
  have htest (f : Hom A B) : f ∈ levelHom C D ↔ tateHom p A B f ∈ maps :=
    mem_levelHom_iff_tateLevelPreimage_mapsTo f p n C D hC
      (surjective_nsmul_of_ne_zero A p hp)
  let S := Submodule.span ℤ_[p] (tateHom p A B '' (levelHom C D : Set (Hom A B)))
  change (S : Set (A.T p →ₗ[ℤ_[p]] B.T p)) = (maps : Set (A.T p →ₗ[ℤ_[p]] B.T p))
  have hsub : S ≤ maps := Submodule.span_le.mpr fun _ ⟨f, hf, he⟩ => he ▸ (htest f).mp hf
  refine Set.Subset.antisymm hsub ?_
  intro φ hφ
  obtain ⟨f, ψ, h⟩ := exists_add_pow_smul_of_mem_span (tateHom p A B) n
    (x := φ) (by rw [hfull]; exact Submodule.mem_top)
  have hpow (g : A.T p →ₗ[ℤ_[p]] B.T p) : (p : ℤ_[p]) ^ n • g ∈ S := by
    have hmul (u : A.T p →ₗ[ℤ_[p]] B.T p)
        (hu : u ∈ Submodule.span ℤ_[p] (Set.range (tateHom p A B))) :
        (p : ℤ_[p]) ^ n • u ∈ S := by
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨v, rfl⟩ := hu
        have hv : (p : ℤ_[p]) ^ n • tateHom p A B v ∈ maps :=
          fun x _ => tateLevelSubmodule_mem_pow_smul p n D (homT v x)
        have hn : (p : ℤ_[p]) ^ n • tateHom p A B v = tateHom p A B (p ^ n • v) := by
          rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p], Nat.cast_pow]
        rw [hn] at hv ⊢
        exact Submodule.subset_span ⟨_, (htest _).mpr hv, rfl⟩
      | zero => rw [smul_zero]; exact S.zero_mem
      | add u v _ _ hu hv => rw [smul_add]; exact S.add_mem hu hv
      | smul c u _ hu => rw [smul_comm]; exact S.smul_mem c hu
    exact hmul g (by rw [hfull]; exact Submodule.mem_top)
  have hf : tateHom p A B f ∈ maps := by
    have hφ' : φ ∈ maps := hφ
    rw [h] at hφ'
    exact (maps.add_mem_iff_left (hsub (hpow ψ))).mp hφ'
  rw [h]
  exact S.add_mem (Submodule.subset_span ⟨_, (htest f).mpr hf, rfl⟩) (hpow ψ)

end Level

end ZInQ.Manuscript.RC.HCMV21
