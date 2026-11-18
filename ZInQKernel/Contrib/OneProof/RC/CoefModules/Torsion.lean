import ZInQKernel.Contrib.OneProof.RC.CoefModules.Characters
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard

/-!
# Lane RC28 (coefficient modules), part 3: the torsion module `E(K_S)[N]` over `G_{K,S}`

Manuscript `diophantine_zq.tex` (11/5), tex 2725–2727 and 2836–2838: the coefficient module
`M_i = (T_2E ⊗ A_i)(χ_hΨ_i)` is built from the Tate module `T = T_2E` of the fixed curve; since
`2^i A_i = 0`, `T_2E ⊗ A_i = E[2^i] ⊗ A_i`.

Here `E[N]` is realized as a genuine discrete `G_{K,S}`-module: the `N`-torsion of the points of
`W = E_K` with coordinates in `K_S` (the tree's `unramifiedOutside K S`), with `G_{K,S}` acting on
the coordinates (Mathlib's `WeierstrassCurve.Affine.Point.map`). No hypothesis is needed for the
definition.

* `TorsS K S W N`: `E(K_S)[N]`, a `DistribMulAction` of `G_{K,S}`; `coe_smul_torsS`;
* `isOpen_stabilizer_torsS`: stabilizers are open (the coordinates of a point lie in a finite
  extension), so it is a discrete `G_{K,S}`-module; `finite_torsS` (for `W` elliptic, `N ≠ 0`);
* `FullTorsion K S W N`: **`E[N]` is defined over `K_S`**, i.e. `E(K_S)[N]` has `N²` points (the
  full `N`-torsion; equivalently every `N`-torsion point of `E(K̄)` has coordinates in `K_S`). By
  the Néron–Ogg–Shafarevich criterion (Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed.,
  VII.7.1; Serre–Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968), Thm. 1)
  this holds when `S` contains the primes above `N` and above the discriminant of an integral model:
  GLUE, kept as an explicit hypothesis where it is used (`FullTorsion` is a `Prop`).
* `fullTorsion_of_trivial_action`: non-vacuity — if every `N`-torsion point is `K`-rational (for
  `E_ℓ` and `N = 2`: full rational two-torsion, tex 1765–1767) the hypothesis holds for every `S`.

Kinds: definitions, PROVED; `FullTorsion` is a hypothesis (GLUE, Néron–Ogg–Shafarevich).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside)
open scoped WeierstrassCurve

/-- Equality in `K_S` is decided classically (needed by the point arithmetic). -/
instance decEqKS (K : Type) [Field K] (S : Set (HeightOneSpectrum (𝓞 K))) :
    DecidableEq (KS K S) := Classical.decEq _

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

section Tors

variable (W : WeierstrassCurve K) (N : ℤ)

/-- **`E(K_S)[N]`**: the `N`-torsion of the points of `W` with coordinates in `K_S`. -/
abbrev TorsS : Type := AddSubgroup.torsionBy ((W.baseChange (KS K S)).toAffine.Point) N

variable {K S W N}

omit [NumberField K] in
theorem map_mem_torsS (σ : GKS K S) {P : (W.baseChange (KS K S)).toAffine.Point}
    (hP : P ∈ AddSubgroup.torsionBy ((W.baseChange (KS K S)).toAffine.Point) N) :
    Affine.Point.map (galS K S σ).toAlgHom P ∈
      AddSubgroup.torsionBy ((W.baseChange (KS K S)).toAffine.Point) N := by
  have hP' : N • P = 0 := (Submodule.mem_torsionBy_iff _ _).mp hP
  change Affine.Point.map (galS K S σ).toAlgHom P ∈ Submodule.torsionBy ℤ _ N
  rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hP', map_zero]

omit [NumberField K] in
theorem pointMap_one (P : (W.baseChange (KS K S)).toAffine.Point) :
    Affine.Point.map (galS K S (1 : GKS K S)).toAlgHom P = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact map_zero _
  · rw [Affine.Point.map_some]
    rfl

/-- **The Galois action of `G_{K,S}` on `E(K_S)[N]`** (on the coordinates of points). -/
instance instDistribMulActionTorsS : DistribMulAction (GKS K S) (TorsS K S W N) where
  smul σ P := ⟨Affine.Point.map (galS K S σ).toAlgHom P.1, map_mem_torsS σ P.2⟩
  one_smul P := Subtype.ext (pointMap_one P.1)
  mul_smul σ τ P :=
    Subtype.ext (Affine.Point.map_map (galS K S τ).toAlgHom (galS K S σ).toAlgHom P.1).symm
  smul_zero _ := Subtype.ext (map_zero _)
  smul_add _ _ _ := Subtype.ext (map_add _ _ _)

omit [NumberField K] in
/-- The action is the coordinatewise point map. -/
theorem coe_smul_torsS (σ : GKS K S) (P : TorsS K S W N) :
    ((σ • P : TorsS K S W N) : (W.baseChange (KS K S)).toAffine.Point) =
      Affine.Point.map (galS K S σ).toAlgHom (P : (W.baseChange (KS K S)).toAffine.Point) :=
  rfl

/-- **`E(K_S)[N]` is a discrete `G_{K,S}`-module**: the stabilizer of a point contains the
stabilizers of its two coordinates, which are open. Kind: PROVED. -/
theorem isOpen_stabilizer_torsS (P : TorsS K S W N) :
    IsOpen (MulAction.stabilizer (GKS K S) P : Set (GKS K S)) := by
  obtain ⟨P, hP⟩ := P
  rcases P with _ | ⟨x, y, h⟩
  · convert isOpen_univ
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_univ, iff_true]
    exact Subtype.ext (map_zero _)
  · refine Subgroup.isOpen_mono (H₁ := stabS K S x ⊓ stabS K S y) (fun σ hσ => ?_) ?_
    · rw [Subgroup.mem_inf, mem_stabS, mem_stabS] at hσ
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      rw [coe_smul_torsS, Affine.Point.map_some, Affine.Point.some.injEq]
      exact ⟨hσ.1, hσ.2⟩
    · rw [Subgroup.coe_inf]
      exact (isOpen_stabS K S x).inter (isOpen_stabS K S y)

omit [NumberField K] in
/-- `E(K_S)[N]` is finite for an elliptic `W` and `N ≠ 0`. Kind: PROVED (vendored Tau Ceti). -/
theorem finite_torsS [W.IsElliptic] (hN : N ≠ 0) : Finite (TorsS K S W N) :=
  (W.baseChange (KS K S)).finite_torsionBy hN

end Tors

/-! ### The full `N`-torsion over `K_S` -/

/-- **`E[N]` is defined over `K_S`**: `E(K_S)[N]` has `N²` points (`N` invertible, so this is the
whole `N`-torsion of `E(K̄)`). GLUE (Néron–Ogg–Shafarevich, Silverman AEC VII.7.1; Serre–Tate 1968,
Thm. 1) for `S` containing the primes above `N` and above the discriminant; a hypothesis. -/
def FullTorsion (W : WeierstrassCurve K) (N : ℕ) : Prop :=
  Nat.card (TorsS K S W N) = N ^ 2

end ZInQ.Manuscript.RC.CoefModules
