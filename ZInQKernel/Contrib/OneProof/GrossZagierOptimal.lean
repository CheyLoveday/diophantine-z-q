import ZInQKernel.Contrib.OneProof.GrossZagierModuli
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_discriminant_ne_zero

/-!
# gz-optimal: the Gross–Zagier leaf for the optimal (strong Weil) parametrization only

Task gz-optimal (2026-11-16). Report: `docs/research/gz-optimal.md`; scratch and log: `scratch/gz-optimal/`.

Work in progress.
-/

noncomputable section

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp Filter Topology
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm)
open scoped WeierstrassCurve.Affine MatrixGroups

namespace ZInQ.GZOptimal

/-! ## §1. Additivity of `weierPt` for curves `y² = x³ + a₄x + a₆` -/

/-- `E` is given by an equation `y² = x³ + a₄x + a₆` (`a₁ = a₂ = a₃ = 0`). -/
def IsShortModel (E : WeierstrassCurve ℚ) : Prop := E.a₁ = 0 ∧ E.a₂ = 0 ∧ E.a₃ = 0

theorem short_cd (d : ℕ) : IsShortModel (shortCurve (-(d : ℚ) ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [shortCurve]

theorem fun_add_of_eq (L : PeriodPair) {W : WeierstrassCurve ℂ} (h : L.weierstrassCurve = W)
    (F : ℂ → W.toAffine.Point) (hF0 : ∀ z ∈ L.lattice, F z = 0)
    (hF1 : ∀ z ∉ L.lattice, ∃ hns, F z = .some (L.weierstrassP z) (L.derivWeierstrassP z / 2) hns)
    (z w : ℂ) : F (z + w) = F z + F w := by
  subst h
  have hD := L.discriminant_ne_zero
  have hF : F = L.toPoint hD := by
    funext u
    by_cases hu : u ∈ L.lattice
    · rw [hF0 u hu, L.toPoint_of_mem hD hu]
    · obtain ⟨hns, e⟩ := hF1 u hu
      rw [e, L.toPoint_of_notMem hD hu]
  rw [hF]
  exact (L.isUniformization_toPoint hD).1 z w

section Short

variable {E : WeierstrassCurve ℚ} (hE : IsShortModel E)
include hE

theorem bc_a₁ : (E⁄ℂ).a₁ = 0 := by simp [hE.1]
theorem bc_a₂ : (E⁄ℂ).a₂ = 0 := by simp [hE.2.1]
theorem bc_a₃ : (E⁄ℂ).a₃ = 0 := by simp [hE.2.2]
theorem bc_b₂ : (E⁄ℂ).b₂ = 0 := by
  rw [WeierstrassCurve.b₂, bc_a₁ hE, bc_a₂ hE]; ring

/-- For a period lattice of a short model `E`, the curve of `L` is `E⁄ℂ`. -/
theorem weierstrassCurve_eq {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L) :
    L.weierstrassCurve = E⁄ℂ := by
  obtain ⟨h2, h3⟩ := hL
  have a1 := bc_a₁ hE; have a2 := bc_a₂ hE; have a3 := bc_a₃ hE
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, a1, a2, a3] at h2 h3
  ext
  · rw [PeriodPair.weierstrassCurve_a₁, a1]
  · rw [PeriodPair.weierstrassCurve_a₂, a2]
  · rw [PeriodPair.weierstrassCurve_a₃, a3]
  · rw [PeriodPair.weierstrassCurve_a₄, h2]; ring
  · rw [PeriodPair.weierstrassCurve_a₆, h3]; ring

/-- **`weierPt E L` is additive** for a short model `E` (the uniformization theorem, vendored). -/
theorem weierPt_add' [E.IsElliptic] {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L)
    (z w : ℂ) :
    ZInQ.GZHL3.weierPt E L (z + w) = ZInQ.GZHL3.weierPt E L z + ZInQ.GZHL3.weierPt E L w := by
  refine fun_add_of_eq L (weierstrassCurve_eq hE hL) _ (fun u hu => ?_) (fun u hu => ?_) z w
  · exact ZInQ.GZHeegner.weierPt_eq_zero _ L hu
  · rw [ZInQ.GZHeegner.weierPt_eq_some _ hL hu]
    have hns := ZInQ.GZHL3.weierPt_some E hL hu
    simp only [bc_b₂ hE, bc_a₁ hE, bc_a₃ hE, zero_div, sub_zero, zero_mul] at hns ⊢
    exact ⟨hns, trivial⟩

/-- `weierPt E L` as an additive map `ℂ →+ E(ℂ)`. -/
def weierHom [E.IsElliptic] {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L) :
    ℂ →+ (E⁄ℂ).toAffine.Point :=
  AddMonoidHom.mk' (ZInQ.GZHL3.weierPt E L) (weierPt_add' hE hL)

theorem weierHom_apply [E.IsElliptic] {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L)
    (z : ℂ) : weierHom hE hL z = ZInQ.GZHL3.weierPt E L z := rfl

theorem weierPt_sum [E.IsElliptic] {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L)
    {ι : Type*} (s : Finset ι) (g : ι → ℂ) :
    ∑ i ∈ s, ZInQ.GZHL3.weierPt E L (g i) = ZInQ.GZHL3.weierPt E L (∑ i ∈ s, g i) := by
  simp only [← weierHom_apply hE hL, map_sum]

theorem weierPt_zsmul [E.IsElliptic] {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L)
    (n : ℤ) (z : ℂ) :
    n • ZInQ.GZHL3.weierPt E L z = ZInQ.GZHL3.weierPt E L ((n : ℂ) * z) := by
  rw [← weierHom_apply hE hL, ← weierHom_apply hE hL, ← map_zsmul, zsmul_eq_mul]

end Short

/-- `weierPt E L z = O` exactly for `z ∈ L`. -/
theorem weierPt_eq_zero_iff (E : WeierstrassCurve ℚ) [E.IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) (z : ℂ) :
    ZInQ.GZHL3.weierPt E L z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun h => ?_, ZInQ.GZHeegner.weierPt_eq_zero E L⟩
  by_contra hz
  rw [ZInQ.GZHeegner.weierPt_eq_some E hL hz] at h
  exact Affine.Point.some_ne_zero _ h

/-- **Torsion of a `K`-point read off from its complex parameter**: if `ι(P) = weierPt E L w`,
then `P` is torsion iff `k w ∈ L` for some `k ≥ 1`. -/
theorem isOfFinAddOrder_iff {E : WeierstrassCurve ℚ} [E.IsElliptic] (hE : IsShortModel E)
    {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice E L) {K : Type*} [Field K] [Algebra ℚ K]
    [DecidableEq K] (ι : K →ₐ[ℚ] ℂ) (P : (E⁄K).Point) {w : ℂ}
    (hP : Affine.Point.map ι P = ZInQ.GZHL3.weierPt E L w) :
    IsOfFinAddOrder P ↔ ∃ k : ℕ, 0 < k ∧ (k : ℂ) * w ∈ L.lattice := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  rw [← (Affine.Point.map_injective (W' := E) (f := ι)).eq_iff, map_nsmul, map_zero, hP,
    ← natCast_zsmul, weierPt_zsmul hE hL, weierPt_eq_zero_iff E hL]
  push_cast; rfl

/-! ## §2. Lattice lemmas -/

/-- Real relations between the periods of a `PeriodPair` are trivial. -/
theorem real_rel {L : PeriodPair} {a b : ℝ} (h : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = 0) :
    a = 0 ∧ b = 0 := by
  have h' : a • L.ω₁ + b • L.ω₂ = 0 := by simpa [Complex.real_smul] using h
  exact LinearIndependent.pair_iff.1 L.indep _ _ h'

/-- Integer relations between the periods of a `PeriodPair` are trivial. -/
theorem int_rel {L : PeriodPair} {a b : ℤ} (h : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = 0) :
    a = 0 ∧ b = 0 := by
  obtain ⟨ha, hb⟩ := real_rel (L := L) (a := a) (b := b) (by exact_mod_cast h)
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

theorem ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  intro h
  have := int_rel (L := L) (a := 1) (b := 0) (by simp [h])
  exact one_ne_zero this.1

/-- **A rational multiplier of a lattice is an integer**: `q ω₁ ∈ L` with `q ∈ ℚ` forces `q ∈ ℤ`. -/
theorem rat_mem_int {L : PeriodPair} {q : ℚ} (h : (q : ℂ) * L.ω₁ ∈ L.lattice) :
    ∃ n : ℤ, q = n := by
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 h
  have h1 := (real_rel (L := L) (a := (a : ℝ) - q) (b := b) (by push_cast; linear_combination hab)).1
  exact ⟨a, by exact_mod_cast (sub_eq_zero.1 h1).symm⟩

/-- **Finite index**: if `m L' ⊆ L` (`m ≠ 0`) for lattices `L, L'`, then `M L ⊆ m L'` for some
integer `M ≠ 0` (the determinant of the inclusion). -/
theorem exists_int_mul_mem (L L' : PeriodPair) {m : ℂ} (hm : m ≠ 0)
    (h : ∀ z ∈ L'.lattice, m * z ∈ L.lattice) :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ z ∈ L.lattice, ∃ w ∈ L'.lattice, (M : ℂ) * z = m * w := by
  obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.1 (h _ L'.ω₁_mem_lattice)
  obtain ⟨r, s, hrs⟩ := PeriodPair.mem_lattice.1 (h _ L'.ω₂_mem_lattice)
  refine ⟨p * s - q * r, fun hD => ?_, fun z hz => ?_⟩
  · have hD' : ((p : ℂ) * s - q * r) = 0 := by exact_mod_cast hD
    have e1 : m * ((s : ℂ) * L'.ω₁ + ((-q : ℤ) : ℂ) * L'.ω₂) = 0 := by
      push_cast; linear_combination (s : ℂ) * hpq.symm - (q : ℂ) * hrs.symm + L.ω₁ * hD'
    have e2 : m * (((-r : ℤ) : ℂ) * L'.ω₁ + (p : ℂ) * L'.ω₂) = 0 := by
      push_cast; linear_combination -(r : ℂ) * hpq.symm + (p : ℂ) * hrs.symm + L.ω₂ * hD'
    obtain ⟨hs, hq⟩ := int_rel ((mul_eq_zero.1 e1).resolve_left hm)
    obtain ⟨hr, hp⟩ := int_rel ((mul_eq_zero.1 e2).resolve_left hm)
    have hq' : q = 0 := by simpa using hq
    subst hs hq' hp
    have : m * L'.ω₁ = 0 := by rw [← hpq]; simp
    exact ω₁_ne_zero L' ((mul_eq_zero.1 this).resolve_left hm)
  · obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
    refine ⟨(a * s - b * r : ℤ) * L'.ω₁ + (b * p - a * q : ℤ) * L'.ω₂,
      PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩, ?_⟩
    push_cast
    linear_combination ((a : ℂ) * s - b * r) * hpq + ((b : ℂ) * p - a * q) * hrs

end ZInQ.GZOptimal
