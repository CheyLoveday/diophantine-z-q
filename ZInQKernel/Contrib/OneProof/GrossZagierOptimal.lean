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

/-! ## §3. The optimal parametrization and the statements -/

/-- **`Λ_f`, the period lattice of `2πi f(τ) dτ` on `X₀(N)`**: the subgroup of `ℂ` generated by the
periods `φ_f(γτ) − φ_f(τ) = 2πi ∫_τ^{γτ} f(z) dz`, `γ ∈ Γ₀(N)`, `τ ∈ ℍ` (`φ_f` the Eichler integral).
These are the integrals of `2πi f dτ` over the closed paths of `Y₀(N)` from `τ` to `γτ`; they give
`∫_γ 2πi f dτ` for every class `γ ∈ H₁(X₀(N), ℤ)` (Shimura 1971, §7.5; Diamond–Shurman §6.6;
UNVERIFIED locators). -/
def periodLattice {N : ℕ} [NeZero N] (f : Newform N 2) : Submodule ℤ ℂ :=
  Submodule.span ℤ {w | ∃ γ ∈ CongruenceSubgroup.Gamma0 N, ∃ τ : ℍ,
    w = ZInQ.GZHL3.eichler f (γ • τ) - ZInQ.GZHL3.eichler f τ}

/-- **`φ = (X, Y) : X₀(N) → E` is the strong Weil (optimal) parametrization.** The lift of `φ` to
`ℍ → ℂ ⊃ L` is `c φ_f`, `c ∈ ℚ` (i.e. `φ^*ω = c · 2πi f(τ) dτ` for the invariant differential
`ω = dx/(2y + a₁x + a₃)` of the model, whose period lattice is `L`), and `L = c Λ_f`.

`L = c Λ_f` says that `φ_* : H₁(X₀(N), ℤ) → H₁(E(ℂ), ℤ) = L` (`γ ↦ ∫_γ φ^*ω`) is surjective. For the
homomorphism `J₀(N) → E` induced by `φ` (Albanese), the cokernel of `H₁(J₀(N), ℤ) → H₁(E, ℤ)` is the
group of components of its kernel, so this is equivalent to **`J₀(N) → E` having connected kernel**,
equivalently (dually) to `E → J₀(N)` being injective: the definition of the strong Weil
parametrization (optimal quotient) of the strong Weil curve `E` (Mazur–Swinnerton-Dyer 1974, §1;
Stevens 1989, §1; Cremona 1997, §2.14; Gross–Zagier 1986, Ch. V; all UNVERIFIED). "Minimal degree"
is not stated: Mathlib has no degree of a map of curves, and for a fixed non-optimal `E` the
minimal-degree `φ` is not optimal. -/
def IsOptimalParam (N : ℕ) [NeZero N] (f : Newform N 2) (E : WeierstrassCurve ℚ) (X Y : ℍ → ℂ) :
    Prop :=
  ∃ (L : PeriodPair) (c : ℚ), ZInQ.GZHL3.IsPeriodLattice E L ∧
    L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ)) ∧
    ∀ τ : ℍ, ZInQ.GZModuli.modPt E X Y τ = ZInQ.GZHL3.weierPt E L (c * ZInQ.GZHL3.eichler f τ)

/-- **The Gross–Zagier formula for the strong Weil parametrization (moduli form, positive constant
forgotten; Gross–Zagier 1986, Thm I.6.3 and Ch. V Thm 2.1).** As `GZModuli.GrossZagierModuliAt E`
(gz-moduli), with two changes:

* `φ = (X, Y)` is moreover the **strong Weil (optimal) parametrization** (`IsOptimalParam`), so
  `E` is the strong Weil curve of `f`. Under either reading of Gross–Zagier Ch. V (formula stated for
  every modular parametrization, or only for the strong Weil curve with its strong parametrization)
  this case is printed.
* `y ∈ E(K)` satisfies `ι(y) = n · y_K` for an integer `n ≠ 0`, where `y_K = Σ_x φ(x)` is the sum
  over a complete set of Heegner points `x = (𝒪_K, 𝔫, [𝔞])`, `𝔫 = (N, (−β + √D)/2)`
  (`IsHeegnerPointReps`; for `σ ∈ Gal(H/K)` the `x^σ` run over them, so `y_K = Tr_{H/K} φ(x)`).
  Gross–Zagier state that `y_K ∈ E(K)` and give `L'(E/K, 1)` as a positive multiple of `ĥ(y_K)`;
  `y = n y_K` and `ĥ(n y_K) = n² ĥ(y_K)` give the statement for `y` (`n = 1` is gz-moduli's form).

Then `L'(E/K, 1) = (F G)'(1) = κ · ĥ(y)` for some real `κ > 0`, with `F`, `G` the entire
continuations of `L(f, s) = L(E, s)` and `L(f ⊗ χ_D, s)`.

Source: B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84
(1986), 225–320, Thm I.6.3 and Ch. V Thm 2.1 with `φ^*ω = c · 2πi f(τ) dτ`; locators, the constant
`‖ω‖²/(c² u² √|D|)` and the exact hypotheses on `φ` UNVERIFIED (no copy on this host). Weaker than
the print: the constant is replaced by `∃ κ > 0`; folded in: `L(E/K, s) = L(f, s) L(f ⊗ χ_D, s)`. -/
def GrossZagierModuliOptAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ X Y : ℍ → ℂ, ZInQ.GZModuli.IsModularParam N E X Y → IsOptimalParam N f E X Y →
    ∀ D β : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ (R : Type) [Fintype R] (τ : R → ℍ), ZInQ.GZModuli.IsHeegnerPointReps N D β τ →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ n : ℤ, n ≠ 0 →
    ∀ y : (E⁄K).Point, Affine.Point.map ι y = n • ∑ r, ZInQ.GZModuli.modPt E X Y (τ r) →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

/-- `GrossZagierModuliOptAt` for every elliptic curve over `ℚ`. -/
def GrossZagierModuliOpt : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], GrossZagierModuliOptAt E

/-- **The leaf of the `C_d` route**: `GrossZagierModuliOptAt E'` for every short model `E'` in the
isogeny class of `C_d : y² = x³ − d²x` (`aₙ(E') = aₙ(C_d)`), `d ≡ 5 (mod 8)` squarefree. A
restriction of `GrossZagierModuliOpt`. -/
def GrossZagierModuliOptCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
    ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic], IsShortModel E' →
      (∀ n : ℕ, n ≠ 0 → E'.LFunction n = (shortCurve (-(d : ℚ) ^ 2)).LFunction n) →
      GrossZagierModuliOptAt E'

theorem grossZagierModuliOptCd_of (h : GrossZagierModuliOpt) : GrossZagierModuliOptCd :=
  fun _ _ _ E' _ _ _ => h E'

/-- **(GLUE, a period computation) `C_d` is the strong Weil curve of its isogeny class**: for the
newform `f` of `C_d` and the period lattice `L` of `C_d`, `L = c₀ Λ_f` for a rational `c₀`.

Not proved. Checked numerically for `d = 5` (`N = 800`) and `d = 13` (`N = 5408`) with PARI's
`ellweilcurve` (`scratch/gz-optimal/py/optimal_cd.py`: `C_d` is the curve of its class with Smith
invariants `[1, 1]`, i.e. `L_{C_d} = L_f`), VERIFIED; for general `d` SPECULATIVE. For `d = 1` it is
false (`y² = x³ − x` is `32a2`, not optimal), so it depends on `d ≡ 5 (mod 8)`. gz-weil proved the
inclusion `c Λ_f ⊆ L` for some `c ∈ ℚ^×`; the content is the reverse inclusion. -/
def CdOptimal : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) →
    ∀ L : PeriodPair, ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L →
      ∃ c₀ : ℚ, L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c₀ : ℂ))

/-- **The strong Weil curve of a rational newform, with its period lattice (textbook; composite).**
For a weight-2 newform `f` of level `N`, trivial character and rational coefficients there is an
elliptic curve `E'/ℚ`, given by an equation `y² = x³ + a₄x + a₆`, with `aₙ(E') = aₙ(f)` for `n ≥ 1`,
whose period lattice is `L' = c Λ_f` for some `c ∈ ℚ`.

Content: the optimal quotient `E_f = J₀(N)/I_f J₀(N)` is an elliptic curve over `ℚ` with
`L(E_f, s) = L(f, s)` (Eichler–Shimura; Shimura 1971, Thm 7.14 and §7.5; Diamond–Shurman §6.6 and
Thm 8.8.1; UNVERIFIED); `φ : X₀(N) → E_f` is the strong Weil parametrization, so
`φ_* : H₁(X₀(N), ℤ) → H₁(E_f, ℤ)` is onto and the period lattice of `ω` is `{∫_γ φ^*ω} = c Λ_f` with
`φ^*ω = c · 2πi f dτ`; `c ∈ ℚ` since `φ` and `ω` are defined over `ℚ` and `f = q + …` (Manin 1972,
rational Manin constant; UNVERIFIED); every elliptic curve over `ℚ` has a model `y² = x³ + a₄x + a₆`
(Silverman, AEC, III.1), and `aₙ` does not depend on the model (Mathlib's `LFunction` uses the
minimal model). Composite: the print states these over `J₀(N)`; the analytic form `L' = c Λ_f` is
the period computation above. Compare gz-hl3's `GZHL3.StrongWeilCurve` (inclusion `c Λ_f ⊆ L'`,
rated composite); this is its sharpening to equality. -/
def StrongWeilOptimal : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → ∃ q : ℚ, coeff f n = q) →
    ∃ E' : WeierstrassCurve ℚ, E'.IsElliptic ∧ IsShortModel E' ∧
      (∀ n : ℕ, n ≠ 0 → coeff f n = (E'.LFunction n : ℂ)) ∧
      ∃ (L' : PeriodPair) (c : ℚ), ZInQ.GZHL3.IsPeriodLattice E' L' ∧
        L'.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ))

/-- `StrongWeilOptimal` restricted to the newforms of the curves `C_d`. -/
def StrongWeilOptimalCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) →
    ∃ E' : WeierstrassCurve ℚ, E'.IsElliptic ∧ IsShortModel E' ∧
      (∀ n : ℕ, n ≠ 0 → coeff f n = (E'.LFunction n : ℂ)) ∧
      ∃ (L' : PeriodPair) (c : ℚ), ZInQ.GZHL3.IsPeriodLattice E' L' ∧
        L'.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ))

theorem strongWeilOptimalCd_of (h : StrongWeilOptimal) : StrongWeilOptimalCd :=
  fun _ _ _ N _ f hχ hf => h N f hχ fun n hn => ⟨_, by rw [hf n hn]; rfl⟩

/-- **An analytic isogeny with rational multiplier is defined over `ℚ` (textbook; composite).** Let
`E, E'/ℚ` be elliptic curves with period lattices `L, L'`, and `μ ∈ ℚ^×` with `μ L ⊆ L'`. Then the
isogeny `ψ : E → E'`, `z ↦ μ z` on `ℂ/L → ℂ/L'`, maps `E(K)` into `E'(K)` for every number field
`K ⊂ ℂ`: for `P ∈ E(K)` there is `P' ∈ E'(K)` with `ι(P') = ψ(ι(P))`.

Content: `ψ` is an isogeny with `ψ^*ω' = μ ω` (Silverman, AEC, Thm VI.4.1 and Prop. VI.3.6;
UNVERIFIED numbers); for `σ ∈ Aut(ℂ)`, `ψ^σ : E → E'` is an isogeny with `(ψ^σ)^*ω' = σ(μ) ω = μ ω`,
and `ψ ↦ (ψ^*ω'/ω)` is injective on `Hom(E, E')` in characteristic `0` (AEC, Cor. III.5.3 and
Thm III.5.2), so `ψ^σ = ψ`: `ψ` is defined over `ℚ` and maps `E(K)` to `E'(K)` compatibly with `ι`.
Composite only because Mathlib has no isogenies of Weierstrass curves: the isogeny is given by its
analytic multiplier (compare gz-hl3's `GZHL3.IsogenyLattice`). -/
def AnalyticIsogenyRational : Prop :=
  ∀ (E E' : WeierstrassCurve ℚ) [E.IsElliptic] [E'.IsElliptic] (L L' : PeriodPair),
    ZInQ.GZHL3.IsPeriodLattice E L → ZInQ.GZHL3.IsPeriodLattice E' L' →
    ∀ μ : ℚ, μ ≠ 0 → (∀ z ∈ L.lattice, (μ : ℂ) * z ∈ L'.lattice) →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K] (ι : K →ₐ[ℚ] ℂ) (P : (E⁄K).Point),
      ∃ P' : (E'⁄K).Point, ∀ z : ℂ, Affine.Point.map ι P = ZInQ.GZHL3.weierPt E L z →
        Affine.Point.map ι P' = ZInQ.GZHL3.weierPt E' L' (μ * z)

/-! ## §4. Glue lemmas -/

open ZInQ.GZHeegner (ParamSetting zPar xPar yPar)

section Glue

variable {N : ℕ} [NeZero N] {f : Newform N 2}

theorem periodsIn_of_lattice {L : PeriodPair} {c : ℚ}
    (hlat : L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ))) :
    ZInQ.GZHL3.PeriodsIn f c L := by
  intro γ hγ τ
  rw [hlat]
  exact ⟨_, Submodule.subset_span ⟨γ, hγ, τ, rfl⟩, rfl⟩

theorem mul_mem_of_periodsIn {L : PeriodPair} {c : ℂ} (hP : ZInQ.GZHL3.PeriodsIn f c L)
    {w : ℂ} (hw : w ∈ periodLattice f) : c * w ∈ L.lattice := by
  have : periodLattice f ≤ L.lattice.comap (LinearMap.mulLeft ℤ c) := by
    rw [periodLattice, Submodule.span_le]
    rintro _ ⟨γ, hγ, τ, rfl⟩
    exact hP γ hγ τ
  exact this hw

theorem ne_zero_of_lattice {L : PeriodPair} {c : ℚ}
    (hlat : L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ))) : c ≠ 0 := by
  rintro rfl
  have h := L.ω₁_mem_lattice
  rw [hlat] at h
  obtain ⟨w, -, hw⟩ := h
  exact ω₁_ne_zero L (by simpa using hw.symm)

theorem periodsIn_zsmul {L : PeriodPair} {c : ℚ} (hP : ZInQ.GZHL3.PeriodsIn f c L) (n : ℤ) :
    ZInQ.GZHL3.PeriodsIn f ((n : ℚ) * c) L := by
  intro γ hγ τ
  have := L.lattice.smul_mem n (hP γ hγ τ)
  rw [zsmul_eq_mul] at this
  push_cast
  rwa [mul_assoc]

end Glue

/-- **From `L'(E/K, 1) = κ' ĥ(P')` to `L'(E/K, 1) = κ ĥ(y)`** when `y` and `P'` are torsion together
(Tau Ceti: `ĥ ≥ 0`, and `ĥ = 0` exactly on torsion over a number field). -/
theorem exists_pos_of_torsion_iff {K : Type} [Field K] [NumberField K] [DecidableEq K]
    {E E' : WeierstrassCurve ℚ} [E.IsElliptic] [E'.IsElliptic] (y : (E⁄K).Point)
    (P' : (E'⁄K).Point) {A : ℂ} {κ' : ℝ} (hκ' : 0 < κ') (hA : A = κ' * P'.canonicalHeight)
    (ht : IsOfFinAddOrder y ↔ IsOfFinAddOrder P') :
    ∃ κ : ℝ, 0 < κ ∧ A = κ * y.canonicalHeight := by
  by_cases h0 : y.canonicalHeight = 0
  · have hP0 : P'.canonicalHeight = 0 :=
      (Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder P').2
        (ht.1 ((Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder y).1 h0))
    exact ⟨1, one_pos, by rw [hA, hP0, h0]; simp⟩
  · have hy : 0 < y.canonicalHeight := lt_of_le_of_ne (Affine.Point.canonicalHeight_nonneg y) (Ne.symm h0)
    have hP0 : P'.canonicalHeight ≠ 0 := fun h => h0
      ((Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder y).2
        (ht.2 ((Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder P').1 h)))
    have hP : 0 < P'.canonicalHeight :=
      lt_of_le_of_ne (Affine.Point.canonicalHeight_nonneg P') (Ne.symm hP0)
    refine ⟨κ' * P'.canonicalHeight / y.canonicalHeight, by positivity, ?_⟩
    have hy' : (y.canonicalHeight : ℂ) ≠ 0 := by exact_mod_cast h0
    rw [hA]
    push_cast
    rw [div_mul_cancel₀ _ hy']

/-- The analytic Heegner point as one parameter: `Σ_{Q ∈ S} weierPt E L (c φ_f(τ_Q)) =
weierPt E L (c Σ_Q φ_f(τ_Q))`. -/
theorem heegnerC_eq {E : WeierstrassCurve ℚ} [E.IsElliptic] (hE : IsShortModel E) {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) {N : ℕ} [NeZero N] (f : Newform N 2) (c : ℂ) {D : ℤ}
    (S : Finset (HeegnerForm N D)) :
    ZInQ.GZHL3.heegnerC E L f c S =
      ZInQ.GZHL3.weierPt E L (c * ∑ r : S, ZInQ.GZHL3.eichler f r.1.tauH) := by
  rw [ZInQ.GZHL3.heegnerC, weierPt_sum hE hL, Finset.mul_sum, ← Finset.sum_coe_sort S]

/-- `Σ_r φ(τ_r)` for the analytic parametrization with constant `c`, as one parameter. -/
theorem sum_modPt_eq {E : WeierstrassCurve ℚ} [E.IsElliptic] (hE : IsShortModel E) {L : PeriodPair}
    {N : ℕ} [NeZero N] {f : Newform N 2} {c : ℚ} (hs : ParamSetting E f L c) {D : ℤ}
    (S : Finset (HeegnerForm N D)) :
    ∑ r : S, ZInQ.GZModuli.modPt E (xPar E L f c) (yPar E L f c) r.1.tauH =
      ZInQ.GZHL3.weierPt E L (c * ∑ r : S, ZInQ.GZHL3.eichler f r.1.tauH) := by
  rw [Finset.mul_sum, ← weierPt_sum hE hs.2.2.1]
  exact Finset.sum_congr rfl fun r _ => ZInQ.GZModuli.modPt_eq hs r.1.tauH

end ZInQ.GZOptimal
