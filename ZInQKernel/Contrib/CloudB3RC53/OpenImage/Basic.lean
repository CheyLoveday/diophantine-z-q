import ZInQKernel.Contrib.OneProof.RC.TateWiring.OpenImage
import ZInQKernel.Contrib.OneProof.RC.TateWiring.Kummer
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Interfaces

/-!
# The open-image input of the finite Heegner descent, over the genuine objects

Target: lane RC10's `ZInQ.Manuscript.RC.HeegnerAlgebra.OpenImageInput G V`
(`ZInQKernel/Contrib/OneProof/RC/HeegnerAlgebra/Interfaces.lean`), used by `H2_assembled`
(Proposition `ex:arith-finite-heegner`, step 1, `diophantine_zq.tex` L2881–2900): a group `G`
acting on `V`, `n ≥ 2`, `g ∈ G` acting as the scalar `u = 1 + 2^n`, an element `τ`, and a
subgroup `G_K` of index two.

Instantiated here with the genuine objects:
* `G = G_ℚ = Aut(ℚ̄/ℚ)` (`GalQ`), acting on `V = E[2^∞](ℚ̄)` (`TwoPowerTors E`, the `2`-primary
  torsion of `E(ℚ̄)`) by applying `σ` to the coordinates of points (the vendored Tau Ceti /
  Mathlib point map `Affine.Point.map σ`), a genuine `DistribMulAction`;
* `n, g` from lane RC17's `serre_scalar_torsion` (PROVED from Serre's print `SerreThm3` and
  non-CM): `g` acts on every point of `E[2^∞](ℚ̄)` as multiplication by `1 + 2^n`;
* `τ` an **actual complex conjugation**: for an embedding `ι : ℚ̄ → ℂ`, `ι ∘ τ = conj ∘ ι`
  (`exists_complexConj`, PROVED: the restriction of complex conjugation to the normal extension
  `ℚ̄`);
* `G_K` the stabilizer of `√k` (`K = ℚ(√k)`, `k ∈ ℚ` not a square), equivalently the fixing
  subgroup of `ℚ(√k)` (lane RC17's `quadField`), of index **exactly** two
  (`stabilizer_index_eq_two`, PROVED by Galois theory of `ℚ̄/ℚ`); for `k < 0` (`K` imaginary)
  complex conjugation does not lie in `G_K` (`complexConj_not_mem`).

`openImageInput` assembles the structure; its inputs are exactly `SerreThm3` (PRINT, stated by
lane RC9) and `HasNoCM E`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.OpenImage

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.TateWiring ZInQ.Manuscript.RC.HeegnerAlgebra
open scoped WeierstrassCurve

variable (E : WeierstrassCurve ℚ)

/-- **`E[2^∞](ℚ̄)`**: the points of `E(ℚ̄)` killed by a power of `2`. -/
abbrev TwoPowerTors : Type := AddCommGroup.primaryComponent (E⁄Qbar).toAffine.Point 2

variable {E}

theorem map_mem_twoPowerTors (σ : GalQ) {P : (E⁄Qbar).toAffine.Point}
    (hP : P ∈ AddCommGroup.primaryComponent (E⁄Qbar).toAffine.Point 2) :
    WeierstrassCurve.Affine.Point.map σ.toAlgHom P ∈
      AddCommGroup.primaryComponent (E⁄Qbar).toAffine.Point 2 := by
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp hP
  exact AddCommGroup.mem_primaryComponent.mpr ⟨k, by rw [← map_nsmul, hk, map_zero]⟩

/-- **The Galois action on `E[2^∞](ℚ̄)`**: `σ` acts on the coordinates of points. -/
instance instDistribMulActionTwoPowerTors : DistribMulAction GalQ (TwoPowerTors E) where
  smul σ P := ⟨WeierstrassCurve.Affine.Point.map σ.toAlgHom P, map_mem_twoPowerTors σ P.2⟩
  one_smul P := by
    apply Subtype.ext
    change WeierstrassCurve.Affine.Point.map (1 : GalQ).toAlgHom (P : (E⁄Qbar).toAffine.Point) = P
    rcases (P : (E⁄Qbar).toAffine.Point) with _ | ⟨x, y, h⟩
    · exact map_zero _
    · rw [WeierstrassCurve.Affine.Point.map_some]
      simp
  mul_smul σ τ P := Subtype.ext (WeierstrassCurve.Affine.Point.map_map τ.toAlgHom σ.toAlgHom _).symm
  smul_zero σ := Subtype.ext (map_zero _)
  smul_add σ P Q := Subtype.ext (map_add _ _ _)

/-- The action is the coordinatewise point map. -/
theorem coe_smul_twoPowerTors (σ : GalQ) (P : TwoPowerTors E) :
    ((σ • P : TwoPowerTors E) : (E⁄Qbar).toAffine.Point) =
      WeierstrassCurve.Affine.Point.map σ.toAlgHom (P : (E⁄Qbar).toAffine.Point) :=
  rfl

/-! ### An actual complex conjugation -/

/-- **An actual complex conjugation** in `G_ℚ`: for some `ℚ`-embedding `ι : ℚ̄ → ℂ`,
`ι(τ x) = conj(ι x)` for every `x ∈ ℚ̄` (PROVED: complex conjugation restricted to the normal
extension `ℚ̄`, embedded in `ℂ`). -/
theorem exists_complexConj :
    ∃ (ι : Qbar →ₐ[ℚ] ℂ) (τ : GalQ), ∀ x : Qbar, ι (τ x) = starRingEnd ℂ (ι x) := by
  let ι : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let _ : Algebra Qbar ℂ := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ Qbar ℂ :=
    IsScalarTower.of_algebraMap_eq fun r => (ι.commutes r).symm
  let conjQ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  refine ⟨ι, conjQ.restrictNormal Qbar, fun x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes conjQ Qbar x

/-- The chosen embedding `ι` and complex conjugation `τ`. -/
def iota : Qbar →ₐ[ℚ] ℂ := exists_complexConj.choose

/-- **The complex conjugation** `τ ∈ G_ℚ` attached to `iota`. -/
def complexConj : GalQ := exists_complexConj.choose_spec.choose

theorem iota_complexConj (x : Qbar) : iota (complexConj x) = starRingEnd ℂ (iota x) :=
  exists_complexConj.choose_spec.choose_spec x

/-! ### `G_K` for `K = ℚ(√k)` -/

/-- A square root of `k` in `ℚ̄`. -/
theorem exists_sqrt (k : ℚ) : ∃ s : Qbar, s ^ 2 = algebraMap ℚ Qbar k := by
  obtain ⟨z, hz⟩ := IsAlgClosed.isSquare (algebraMap ℚ Qbar k)
  exact ⟨z, by rw [hz, sq]⟩

/-- **`G_K`**, `K = ℚ(s)`: the automorphisms fixing `s` (equivalently fixing `ℚ(s)`,
`stabilizer_eq_fixingSubgroup`). -/
abbrev GK (s : Qbar) : Subgroup GalQ := MulAction.stabilizer GalQ s

theorem stabilizer_eq_fixingSubgroup (s : Qbar) : GK s = (quadField s).fixingSubgroup := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, quadField, mem_fixingSubgroup_adjoin_iff]
  simp [AlgEquiv.smul_def]

/-- **`[G_ℚ : G_K] = 2`** for `K = ℚ(√k)`, `k` not a square in `ℚ` (PROVED: some automorphism moves
`√k` by Galois theory of `ℚ̄/ℚ`, and every automorphism sends `√k` to `±√k`). -/
theorem stabilizer_index_eq_two {k : ℚ} (hk : ¬ IsSquare k) {s : Qbar}
    (hs : s ^ 2 = algebraMap ℚ Qbar k) : (GK s).index = 2 := by
  have hmove : ∃ a : GalQ, a s ≠ s := by
    by_contra h
    push Not at h
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) s).2 h
    apply hk
    refine ⟨r, (algebraMap ℚ Qbar).injective ?_⟩
    rw [← hs, ← hr, map_mul, sq]
  obtain ⟨a, ha⟩ := hmove
  have ha' : a s = -s := (apply_eq_or_eq_neg hs a).resolve_left ha
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact ha (map_zero _)
  have hneg : -s ≠ s := by
    intro h
    apply hs0
    have h2 : (2 : Qbar) * s = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [Subgroup.index_eq_two_iff]
  refine ⟨a, fun b => ?_⟩
  simp only [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  have hba : (b * a) s = -(b s) := by rw [AlgEquiv.mul_apply, ha', map_neg]
  rw [hba]
  rcases apply_eq_or_eq_neg hs b with hb | hb
  · rw [hb]
    exact Or.inr ⟨rfl, hneg⟩
  · rw [hb, neg_neg]
    exact Or.inl ⟨rfl, hneg⟩

/-- **For `K` imaginary, complex conjugation is not in `G_K`** (PROVED: `ι(√k)` is purely
imaginary). -/
theorem complexConj_not_mem {k : ℚ} (hk : k < 0) {s : Qbar} (hs : s ^ 2 = algebraMap ℚ Qbar k) :
    complexConj ∉ GK s := by
  rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  intro h
  have hz : (iota s) ^ 2 = (k : ℂ) := by
    rw [← map_pow, hs, AlgHom.commutes]; simp
  have hconj : starRingEnd ℂ (iota s) = iota s := by rw [← iota_complexConj, h]
  -- `ι s` is real, so its square is nonnegative, contradicting `k < 0`
  have him : (iota s).im = 0 := by
    have := congrArg Complex.im hconj
    simp only [Complex.conj_im] at this
    linarith
  have hre := congrArg Complex.re hz
  simp only [sq, Complex.mul_re, him, mul_zero, sub_zero] at hre
  have : (0 : ℝ) ≤ (iota s).re * (iota s).re := mul_self_nonneg _
  have hk' : (k : ℝ) < 0 := by exact_mod_cast hk
  rw [show ((k : ℂ)).re = (k : ℝ) by simp] at hre
  linarith

/-! ### The open-image input -/

variable (E) [E.IsElliptic]

/-- **RC10's `OpenImageInput` over the genuine objects** (tex L2881–2900): `G = G_ℚ` acting on
`E[2^∞](ℚ̄)`; `n ≥ 2` and `g` from RC17's `serre_scalar_torsion` (PROVED from Serre's print
`SerreThm3` and non-CM); `τ` the actual complex conjugation `complexConj`; `G_K` the stabilizer of
`√k`, of index two, for a non-square `k`. -/
def openImageInput (hS : SerreThm3) (hE : HasNoCM E) (k : ℚ) (hk : ¬ IsSquare k) :
    OpenImageInput GalQ (TwoPowerTors E) where
  n := (serre_scalar_torsion E hS hE).choose
  two_le := (serre_scalar_torsion E hS hE).choose_spec.1
  g := (serre_scalar_torsion E hS hE).choose_spec.2.choose
  scalar v := by
    obtain ⟨j, hj⟩ := AddCommGroup.mem_primaryComponent.mp v.2
    apply Subtype.ext
    rw [coe_smul_twoPowerTors, AddSubgroup.coe_zsmul]
    exact (serre_scalar_torsion E hS hE).choose_spec.2.choose_spec.1 j _ hj
  τ := complexConj
  GK := GK (exists_sqrt k).choose
  index_two := stabilizer_index_eq_two hk (exists_sqrt k).choose_spec

/-- The fields of `openImageInput` are the genuine objects: `τ` is complex conjugation for
`iota`, `G_K` is the stabilizer (= fixing subgroup of `ℚ(√k)`) of a square root of `k`, and for
`k < 0` complex conjugation is not in `G_K`. -/
theorem openImageInput_spec (hS : SerreThm3) (hE : HasNoCM E) (k : ℚ) (hk : ¬ IsSquare k) :
    (∀ x : Qbar, iota ((openImageInput E hS hE k hk).τ x) = starRingEnd ℂ (iota x)) ∧
    ∃ s : Qbar, s ^ 2 = algebraMap ℚ Qbar k ∧ (openImageInput E hS hE k hk).GK = GK s ∧
      GK s = (quadField s).fixingSubgroup ∧
      (k < 0 → (openImageInput E hS hE k hk).τ ∉ (openImageInput E hS hE k hk).GK) := by
  refine ⟨iota_complexConj, (exists_sqrt k).choose, (exists_sqrt k).choose_spec, rfl,
    stabilizer_eq_fixingSubgroup _, fun hk0 => complexConj_not_mem hk0 (exists_sqrt k).choose_spec⟩

/-- **(H2) over the genuine objects** (tex L2892–2900, RC10's `H2_assembled` applied to
`openImageInput`): for every normal `N ≤ G_ℚ` such that complex conjugation inverts `G_K` modulo
`N` (the ring-class situation), every point of `E[2^∞](ℚ̄)` fixed by `N` is killed by `2^{n+2}`. -/
theorem h2_genuine (hS : SerreThm3) (hE : HasNoCM E) (k : ℚ) (hk : ¬ IsSquare k)
    (N : Subgroup GalQ) [N.Normal]
    (hτ : ∀ x ∈ (openImageInput E hS hE k hk).GK,
      (openImageInput E hS hE k hk).τ * x * (openImageInput E hS hE k hk).τ⁻¹ * x ∈ N)
    (P : TwoPowerTors E) (hP : ∀ x ∈ N, x • P = P) :
    ((2 : ℤ) ^ ((openImageInput E hS hE k hk).n + 2)) • P = 0 := by
  refine H2_assembled (openImageInput E hS hE k hk) N hτ P hP ?_
  obtain ⟨j, hj⟩ := AddCommGroup.mem_primaryComponent.mp P.2
  refine ⟨j, Subtype.ext ?_⟩
  rw [AddSubgroup.coe_zsmul, AddSubgroup.coe_zero, show ((2 : ℤ) ^ j) = ((2 ^ j : ℕ) : ℤ) by
    push_cast; ring, natCast_zsmul]
  exact hj

end ZInQ.Contrib.CloudB3RC53.OpenImage
