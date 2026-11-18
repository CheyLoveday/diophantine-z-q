import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Rank
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.Iota
import ZInQKernel.Contrib.CloudB3RC53.TameQuotient.TameCharacter
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedFactorization
import ZInQKernel.Contrib.CloudB3RC53.ContBridge.ComplexIso
import ZInQKernel.Contrib.RC53Assist.StrictSymmFull.FullReduction
import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Retained coefficient and absolute local cochain comparisons

The two Tate modules are identified through the same geometric torsion in every
finite level. The level identifications commute with the transition maps and
with the retained local Galois actions. Base change preserves the integral
lattices and their two-power neighbourhoods, so the resulting fibre
identification uses the given lattice topologies.

The absolute local quotient and the descended coefficient action are specified
in all degrees. Three explicit cited premises from Nekovář supply the local
tame structure and two quasi-isomorphisms. Homotopy inverses over the coefficient
field are proved separately. The small tame complex uses the full geometric
norm and geometric Frobenius of the cited formulas.

For actual old primitive places these comparisons supply the full-condition
contractions without an operator-unit premise. The reduction preserves the
original isotropy datum and traced pairing. Both strict-symmetry conventions
then hold on the actual reduced continuous switch, with its unchanged lattice
coefficient topology. The other old-place unit tests remain explicit.

Manuscript support: 2780–2785, 2813–2815 and 5055–5061.
Cited source: Nekovář, Selmer complexes, 3.7.4(ii), 4.1.4, 7.1.1,
7.2.1 and 7.2.3. No strict-symmetry premise is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.StrictSymmFull.CoefficientComparison

open NumberField IsDedekindDomain WeierstrassCurve TensorProduct
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
  ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]
  [HasFullTwoTorsion K S₀ W] [HasFullTwoTorsion K S W]

local instance powerTwoNeZero (n : ℕ) : NeZero (2 ^ n : ℕ) := ⟨pow_ne_zero n two_ne_zero⟩

attribute [local instance] levTop

/-- The finite-level identification is through the actual common geometric torsion. -/
def levelEquiv (n : ℕ) : Lev K S W n ≃+ Lev K S₀ W n :=
  (AddEquiv.ofBijective (inclTors (S := S) W (2 ^ n))
    (inclTors_bijective (S := S) W (2 ^ n) (HasFullTwoTorsion.full n))).trans
    (AddEquiv.ofBijective (inclTors (S := S₀) W (2 ^ n))
      (inclTors_bijective (S := S₀) W (2 ^ n) (HasFullTwoTorsion.full n))).symm

/-- The finite-level identification retains the geometric torsion inclusion. -/
theorem levelEquiv_incl (n : ℕ) (Q : Lev K S W n) :
    inclTors (S := S₀) W (2 ^ n) (levelEquiv (S₀ := S₀) (S := S) W n Q) = inclTors (S := S) W (2 ^ n) Q := by
  change (AddEquiv.ofBijective (inclTors (S := S₀) W (2 ^ n))
      (inclTors_bijective (S := S₀) W (2 ^ n) (HasFullTwoTorsion.full n)))
    ((AddEquiv.ofBijective (inclTors (S := S₀) W (2 ^ n))
      (inclTors_bijective (S := S₀) W (2 ^ n) (HasFullTwoTorsion.full n))).symm
      (inclTors (S := S) W (2 ^ n) Q)) = _
  exact AddEquiv.apply_symm_apply _ _

/-- The common geometric inclusion identifies the underlying points. -/
theorem levelEquiv_point (n : ℕ) (Q : Lev K S W n) :
    Affine.Point.map (inclS K S₀) (levelEquiv (S₀ := S₀) (S := S) W n Q : Pt K S₀ W) =
      Affine.Point.map (inclS K S) (Q : Pt K S W) :=
  congrArg Subtype.val (levelEquiv_incl (S₀ := S₀) (S := S) W n Q)

/-- Halving in the two coefficient supports is the same retained transition. -/
theorem levelEquiv_trans (n : ℕ) (Q : Lev K S W (n + 1)) :
    levelEquiv (S₀ := S₀) (S := S) W n (transLev K S W n Q) =
      transLev K S₀ W n (levelEquiv (S₀ := S₀) (S := S) W (n + 1) Q) := by
  apply inclTors_injective W (2 ^ n)
  apply Subtype.ext
  change Affine.Point.map (inclS K S₀)
      (levelEquiv (S₀ := S₀) (S := S) W n (transLev K S W n Q) : Pt K S₀ W) =
    Affine.Point.map (inclS K S₀)
      (transLev K S₀ W n (levelEquiv (S₀ := S₀) (S := S) W (n + 1) Q) : Pt K S₀ W)
  calc
    _ = Affine.Point.map (inclS K S) (transLev K S W n Q : Pt K S W) :=
      levelEquiv_point (S₀ := S₀) (S := S) W n _
    _ = 2 • Affine.Point.map (inclS K S) (Q : Pt K S W) := by rw [coe_transLev, map_nsmul]
    _ = 2 • Affine.Point.map (inclS K S₀) (levelEquiv (S₀ := S₀) (S := S) W (n + 1) Q : Pt K S₀ W) :=
      congrArg (fun x : (W.baseChange (AlgebraicClosure K)).toAffine.Point => 2 • x)
        (levelEquiv_point (S₀ := S₀) (S := S) W (n + 1) Q).symm
    _ = _ := by rw [coe_transLev, map_nsmul]

/-- The inverse level identification also retains the transitions. -/
theorem levelEquiv_symm_trans (n : ℕ) (Q : Lev K S₀ W (n + 1)) :
    (levelEquiv (S₀ := S₀) (S := S) W n).symm (transLev K S₀ W n Q) =
      transLev K S W n ((levelEquiv (S₀ := S₀) (S := S) W (n + 1)).symm Q) := by
  apply (levelEquiv (S₀ := S₀) (S := S) W n).injective
  rw [AddEquiv.apply_symm_apply, levelEquiv_trans, AddEquiv.apply_symm_apply]

/-- The actual inverse limits are identified as integral Tate modules. -/
def tateEquiv : TateS K S W ≃ₗ[ℤ_[2]] TateS K S₀ W where
  toFun Q := ⟨fun n => levelEquiv (S₀ := S₀) (S := S) W n (projLev n Q), fun n =>
    (levelEquiv_trans (S₀ := S₀) (S := S) W n (projLev (n + 1) Q)).symm.trans
      (congrArg (levelEquiv (S₀ := S₀) (S := S) W n) (Q.2 n))⟩
  invFun Q := ⟨fun n => (levelEquiv (S₀ := S₀) (S := S) W n).symm (projLev n Q), fun n =>
    (levelEquiv_symm_trans (S₀ := S₀) (S := S) W n (projLev (n + 1) Q)).symm.trans
      (congrArg (levelEquiv (S₀ := S₀) (S := S) W n).symm (Q.2 n))⟩
  left_inv Q := by
    apply Subtype.ext
    funext n
    exact (levelEquiv (S₀ := S₀) (S := S) W n).symm_apply_apply _
  right_inv Q := by
    apply Subtype.ext
    funext n
    exact (levelEquiv (S₀ := S₀) (S := S) W n).apply_symm_apply _
  map_add' Q R := by
    apply Subtype.ext
    funext n
    exact (levelEquiv (S₀ := S₀) (S := S) W n).map_add _ _
  map_smul' c Q := by
    apply Subtype.ext
    funext n
    change levelEquiv (S₀ := S₀) (S := S) W n (resN n c • projLev n Q) = resN n c • levelEquiv (S₀ := S₀) (S := S) W n (projLev n Q)
    exact map_nsmul (levelEquiv (S₀ := S₀) (S := S) W n) _ _

/-- The Tate identification is the specified finite-level identification at every level. -/
theorem tateEquiv_proj (n : ℕ) (Q : TateS K S W) :
    projLev n (tateEquiv (S₀ := S₀) (S := S) W Q) = levelEquiv (S₀ := S₀) (S := S) W n (projLev n Q) := rfl

/-- The integral Tate identification is continuous for the actual inverse-limit topologies. -/
theorem continuous_tateEquiv : Continuous (tateEquiv (S₀ := S₀) (S := S) W) := by
  refine continuous_induced_rng.mpr ?_
  exact continuous_pi fun n =>
    (continuous_of_discreteTopology (f := levelEquiv (S₀ := S₀) (S := S) W n)).comp (continuous_projLev n)

/-- The inverse identification is continuous for the same retained topologies. -/
theorem continuous_tateEquiv_symm : Continuous (tateEquiv (S₀ := S₀) (S := S) W).symm := by
  refine continuous_induced_rng.mpr ?_
  exact continuous_pi fun n =>
    (continuous_of_discreteTopology (f := (levelEquiv (S₀ := S₀) (S := S) W n).symm)).comp (continuous_projLev n)

/-- The support identification as an integral continuous linear equivalence. -/
def tateContinuousEquiv : TateS K S W ≃L[ℤ_[2]] TateS K S₀ W :=
  { tateEquiv (S₀ := S₀) (S := S) W with
    continuous_toFun := continuous_tateEquiv (S₀ := S₀) (S := S) W
    continuous_invFun := continuous_tateEquiv_symm (S₀ := S₀) (S := S) W }

/-- Geometric torsion inclusion commutes with the actual restriction from the absolute group. -/
theorem inclTors_absolute_action {U : Set (HeightOneSpectrum (𝓞 K))} (N : ℕ) [NeZero N]
    (τ : Field.absoluteGaloisGroup K) (Q : TorsS K U W N) :
    inclTors (S := U) W N (resAbsCont K U τ • Q) =
      Multiplicative.toAdd (W.torsionGaloisAction (N : ℤ)
        (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) τ)) (inclTors (S := U) W N Q) := by
  let τ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τ
  have hcomp : τ'.toAlgHom.comp (inclS K U) =
      (inclS K U).comp (galS K U (resAbsCont K U τ)).toAlgHom := by
    ext x
    exact (ZInQ.Contrib.CloudB3RC53.RankCounts.resAbs_apply_coe K U τ' x).symm
  apply Subtype.ext
  rw [torsionGaloisAction_apply_coe, pointGaloisAction_apply, coe_inclTors, coe_inclTors,
    coe_smul_torsS, Affine.Point.map_map, Affine.Point.map_map]
  exact congrArg (fun f : KS K U →ₐ[K] AlgebraicClosure K =>
    Affine.Point.map f (Q : (W.baseChange (KS K U)).toAffine.Point)) hcomp.symm

/-- Every finite-level identification respects the same absolute Galois action. -/
theorem levelEquiv_absolute_action (n : ℕ) (τ : Field.absoluteGaloisGroup K) (Q : Lev K S W n) :
    levelEquiv (S₀ := S₀) (S := S) W n (resAbsCont K S τ • Q) =
      resAbsCont K S₀ τ • levelEquiv (S₀ := S₀) (S := S) W n Q := by
  apply inclTors_injective W (2 ^ n)
  rw [levelEquiv_incl, inclTors_absolute_action, inclTors_absolute_action, levelEquiv_incl]

/-- The actual Tate modules have the same action through the retained absolute restrictions. -/
theorem tateEquiv_absolute_action (τ : Field.absoluteGaloisGroup K) (Q : TateS K S W) :
    tateEquiv (S₀ := S₀) (S := S) W (resAbsCont K S τ • Q) =
      resAbsCont K S₀ τ • tateEquiv (S₀ := S₀) (S := S) W Q := by
  apply Subtype.ext
  funext n
  exact levelEquiv_absolute_action (S₀ := S₀) (S := S) W n τ (projLev n Q)

/-- In particular, the specified local Galois action is retained at every place. -/
theorem tateEquiv_local_action (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v) (Q : TateS K S W) :
    tateEquiv (S₀ := S₀) (S := S) W (locMap K S v σ • Q) =
      locMap K S₀ v σ • tateEquiv (S₀ := S₀) (S := S) W Q :=
  tateEquiv_absolute_action (S₀ := S₀) (S := S) W (decompMap K v σ) Q

/-- Global support inflation gives the same retained Tate action. -/
theorem tateEquiv_inflation_action (hS : S₀ ⊆ S) (g : GKS K S) (Q : TateS K S W) :
    tateEquiv (S₀ := S₀) (S := S) W (g • Q) =
      inflMap K hS g • tateEquiv (S₀ := S₀) (S := S) W Q := by
  have hsurj : Function.Surjective (resAbsCont K S) := by
    intro g
    obtain ⟨τ, hτ⟩ := ZInQ.Contrib.CloudB3RC53.RankCounts.resAbs_surjective K S
      (@id (ZInQ.Contrib.CloudB3RC53.RankCounts.GaloisGroupS K S) g)
    exact ⟨τ, hτ⟩
  obtain ⟨τ, rfl⟩ := hsurj g
  have hinfl : inflMap K hS (resAbsCont K S τ) = resAbsCont K S₀ τ :=
    ZInQ.Contrib.CloudB3RC53.RankCounts.resUnr_comp K hS
      (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) τ)
  exact (tateEquiv_absolute_action (S₀ := S₀) (S := S) W τ Q).trans
    (congrArg (fun h : GKS K S₀ => h • tateEquiv (S₀ := S₀) (S := S) W Q) hinfl.symm)

section Fibres

variable (P : Ideal Lambda) [P.IsPrime]
  (α₀ : GKS K S₀ →* Lambdaˣ) (α : GKS K S →* Lambdaˣ)

/-- Base change of the actual integral Tate identification, with both coefficient fibres retained. -/
def fibreEquiv : VP K S W P α ≃ₗ[ResAt P] VP K S₀ W P α₀ :=
  (vpEquiv (K := K) (S := S) (W := W) (P := P) (α := α)).trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (ResAt P) (ResAt P))
      (tateEquiv (S₀ := S₀) (S := S) W)).trans
      (vpEquiv (K := K) (S := S₀) (W := W) (P := P) (α := α₀)).symm)

/-- The retained map on pure tensors. -/
theorem fibreEquiv_tmul (c : ResAt P) (Q : TateS K S W) :
    fibreEquiv (S₀ := S₀) (S := S) W P α₀ α (show VP K S W P α from c ⊗ₜ Q) =
      (show VP K S₀ W P α₀ from c ⊗ₜ tateEquiv (S₀ := S₀) (S := S) W Q) := rfl

/-- The inverse map retains the same pure tensors. -/
theorem fibreEquiv_symm_tmul (c : ResAt P) (Q : TateS K S₀ W) :
    (fibreEquiv (S₀ := S₀) (S := S) W P α₀ α).symm (show VP K S₀ W P α₀ from c ⊗ₜ Q) =
      (show VP K S W P α from c ⊗ₜ (tateEquiv (S₀ := S₀) (S := S) W).symm Q) := rfl

/-- The base-change map also retains the integral scalar action. -/
theorem fibreEquiv_lambda_smul (l : Lambda) (x : VP K S W P α) :
    fibreEquiv (S₀ := S₀) (S := S) W P α₀ α (l • x) =
      l • fibreEquiv (S₀ := S₀) (S := S) W P α₀ α x := by
  rw [← algebraMap_smul (ResAt P) l x, map_smul, algebraMap_smul]

/-- The inverse map retains the integral scalar action as well. -/
theorem fibreEquiv_symm_lambda_smul (l : Lambda) (x : VP K S₀ W P α₀) :
    (fibreEquiv (S₀ := S₀) (S := S) W P α₀ α).symm (l • x) =
      l • (fibreEquiv (S₀ := S₀) (S := S) W P α₀ α).symm x := by
  rw [← algebraMap_smul (ResAt P) l x, map_smul, algebraMap_smul]

/-- The specified coefficient identification maps the actual integral lattice into itself. -/
theorem fibreEquiv_latt {x : VP K S W P α} (hx : x ∈ latt K S W P α) :
    fibreEquiv (S₀ := S₀) (S := S) W P α₀ α x ∈ latt K S₀ W P α₀ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Q, rfl⟩ := hx
    rw [fibreEquiv_tmul]
    exact one_tmul_mem_latt P _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul l x _ hx => rw [fibreEquiv_lambda_smul]; exact Submodule.smul_mem _ _ hx

/-- The inverse coefficient identification also preserves the actual lattice. -/
theorem fibreEquiv_symm_latt {x : VP K S₀ W P α₀} (hx : x ∈ latt K S₀ W P α₀) :
    (fibreEquiv (S₀ := S₀) (S := S) W P α₀ α).symm x ∈ latt K S W P α := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Q, rfl⟩ := hx
    rw [fibreEquiv_symm_tmul]
    exact one_tmul_mem_latt P _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul l x _ hx => rw [fibreEquiv_symm_lambda_smul]; exact Submodule.smul_mem _ _ hx

/-- All basic two-power neighbourhoods are retained by the coefficient identification. -/
theorem fibreEquiv_nbhd (n : ℕ) {x : VP K S W P α} (hx : x ∈ fibNbhd K S W P α n) :
    fibreEquiv (S₀ := S₀) (S := S) W P α₀ α x ∈ fibNbhd K S₀ W P α₀ n := by
  obtain ⟨y, hy, rfl⟩ := (mem_fibNbhd P).mp hx
  rw [fibreEquiv_lambda_smul]
  exact two_pow_smul_mem_fibNbhd P (fibreEquiv_latt (S₀ := S₀) (S := S) W P α₀ α hy)

/-- The inverse map retains the same two-power neighbourhoods. -/
theorem fibreEquiv_symm_nbhd (n : ℕ) {x : VP K S₀ W P α₀} (hx : x ∈ fibNbhd K S₀ W P α₀ n) :
    (fibreEquiv (S₀ := S₀) (S := S) W P α₀ α).symm x ∈ fibNbhd K S W P α n := by
  obtain ⟨y, hy, rfl⟩ := (mem_fibNbhd P).mp hx
  rw [fibreEquiv_symm_lambda_smul]
  exact two_pow_smul_mem_fibNbhd P (fibreEquiv_symm_latt (S₀ := S₀) (S := S) W P α₀ α hy)

/-- Continuity is for the actual lattice topologies, not for discrete replacement fibres. -/
theorem continuous_fibreEquiv : Continuous (fibreEquiv (S₀ := S₀) (S := S) W P α₀ α) := by
  refine continuous_of_hasBasis (fun n => (fibNbhd K S W P α n).toAddSubgroup)
    (fun n => (fibNbhd K S₀ W P α₀ n).toAddSubgroup)
    (fib_hasBasis_nhds_zero (K := K) (S := S) (W := W) P (α := α))
    (fib_hasBasis_nhds_zero (K := K) (S := S₀) (W := W) P (α := α₀))
    (fibreEquiv (S₀ := S₀) (S := S) W P α₀ α).toAddEquiv.toAddMonoidHom
    (fun n => ⟨n, fun x hx => fibreEquiv_nbhd (S₀ := S₀) (S := S) W P α₀ α n hx⟩)

/-- The inverse is continuous for the same retained lattice topologies. -/
theorem continuous_fibreEquiv_symm : Continuous (fibreEquiv (S₀ := S₀) (S := S) W P α₀ α).symm := by
  refine continuous_of_hasBasis (fun n => (fibNbhd K S₀ W P α₀ n).toAddSubgroup)
    (fun n => (fibNbhd K S W P α n).toAddSubgroup)
    (fib_hasBasis_nhds_zero (K := K) (S := S₀) (W := W) P (α := α₀))
    (fib_hasBasis_nhds_zero (K := K) (S := S) (W := W) P (α := α))
    (fibreEquiv (S₀ := S₀) (S := S) W P α₀ α).symm.toAddEquiv.toAddMonoidHom
    (fun n => ⟨n, fun x hx => fibreEquiv_symm_nbhd (S₀ := S₀) (S := S) W P α₀ α n hx⟩)

/-- The retained coefficient map as a continuous linear equivalence of actual fibres. -/
def fibreContinuousEquiv : VP K S W P α ≃L[ResAt P] VP K S₀ W P α₀ :=
  { fibreEquiv (S₀ := S₀) (S := S) W P α₀ α with
    continuous_toFun := continuous_fibreEquiv (S₀ := S₀) (S := S) W P α₀ α
    continuous_invFun := continuous_fibreEquiv_symm (S₀ := S₀) (S := S) W P α₀ α }

/-- Compatible global coefficient characters retain the inflated Galois action. -/
theorem fibreEquiv_inflation_action (hS : S₀ ⊆ S) (g : GKS K S)
    (hα : α g = α₀ (inflMap K hS g)) (x : VP K S W P α) :
    fibreEquiv (S₀ := S₀) (S := S) W P α₀ α (g • x) =
      inflMap K hS g • fibreEquiv (S₀ := S₀) (S := S) W P α₀ α x := by
  induction x using VP.induction with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul c Q =>
    rw [VP.smul_tmul, fibreEquiv_tmul, fibreEquiv_tmul, VP.smul_tmul,
      tateEquiv_inflation_action (S₀ := S₀) (S := S) W hS,
      coe_resChar, coe_resChar, hα]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- Compatible local coefficient characters retain the specified localization action. -/
theorem fibreEquiv_local_action (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v)
    (hα : α (locMap K S v σ) = α₀ (locMap K S₀ v σ)) (x : VP K S W P α) :
    fibreEquiv (S₀ := S₀) (S := S) W P α₀ α (locMap K S v σ • x) =
      locMap K S₀ v σ • fibreEquiv (S₀ := S₀) (S := S) W P α₀ α x := by
  induction x using VP.induction with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul c Q =>
    rw [VP.smul_tmul, fibreEquiv_tmul, fibreEquiv_tmul, VP.smul_tmul,
      tateEquiv_local_action (S₀ := S₀) (S := S) W v σ, coe_resChar, coe_resChar, hα]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- For actual inflated coefficient characters, no character-compatibility premise remains. -/
theorem inflated_fibreEquiv_Galois (hS : S₀ ⊆ S) (g : GKS K S)
    (x : VP K S W P (α₀.comp (inflMap K hS).toMonoidHom)) :
    fibreEquiv (S₀ := S₀) (S := S) W P α₀ (α₀.comp (inflMap K hS).toMonoidHom) (g • x) =
      inflMap K hS g • fibreEquiv (S₀ := S₀) (S := S) W P α₀
        (α₀.comp (inflMap K hS).toMonoidHom) x :=
  fibreEquiv_inflation_action (S₀ := S₀) (S := S) W P α₀ _ hS g rfl x

/-- The canonical localization maps retain that same coefficient identification. -/
theorem inflated_fibreEquiv_local (hS : S₀ ⊆ S) (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v)
    (x : VP K S W P (α₀.comp (inflMap K hS).toMonoidHom)) :
    fibreEquiv (S₀ := S₀) (S := S) W P α₀ (α₀.comp (inflMap K hS).toMonoidHom)
      (locMap K S v σ • x) =
      locMap K S₀ v σ • fibreEquiv (S₀ := S₀) (S := S) W P α₀
        (α₀.comp (inflMap K hS).toMonoidHom) x := by
  apply fibreEquiv_local_action (S₀ := S₀) (S := S) W P α₀ _ v σ ?_ x
  exact congrArg α₀ (locMap_compat K hS v σ)

end Fibres

section PrimitiveCoefficientAction

variable (P : Ideal Lambda) [P.IsPrime] (hS : S₀ ⊆ S)
  (χ : GKS K S →* ℤˣ) (ξ₀ : GKS K S₀ →* Multiplicative ℤ_[2])

/-- The coefficient identification retains the actual primitive quadratic twist
of the smaller-support action, not an unramified replacement action. -/
theorem primitive_fibreEquiv_local_action (v : HeightOneSpectrum (𝓞 K)) (σ : Gloc K v)
    (x : VP K S W P (lambdaChar χ (ξ₀.comp (inflMap K hS).toMonoidHom))) :
    fibreEquiv (S₀ := S₀) (S := S) W P (lambdaChar 1 ξ₀)
      (lambdaChar χ (ξ₀.comp (inflMap K hS).toMonoidHom)) (locMap K S v σ • x) =
      ((χ (locMap K S v σ) : ℤˣ) : ℤ) •
        (locMap K S₀ v σ • fibreEquiv (S₀ := S₀) (S := S) W P (lambdaChar 1 ξ₀)
          (lambdaChar χ (ξ₀.comp (inflMap K hS).toMonoidHom)) x) := by
  induction x using VP.induction with
  | zero => rw [smul_zero, map_zero, smul_zero, smul_zero]
  | tmul c Q =>
    rw [VP.smul_tmul, fibreEquiv_tmul, fibreEquiv_tmul, VP.smul_tmul,
      tateEquiv_local_action (S₀ := S₀) (S := S) W v σ, coe_resChar, coe_resChar]
    change (algebraMap Lambda (ResAt P)
        (lambdaChar χ (ξ₀.comp (inflMap K hS).toMonoidHom) (locMap K S v σ)) * c) ⊗ₜ[ℤ_[2]]
        (locMap K S₀ v σ • tateEquiv (S₀ := S₀) (S := S) W Q) =
      ((χ (locMap K S v σ) : ℤˣ) : ℤ) •
        ((algebraMap Lambda (ResAt P) (lambdaChar 1 ξ₀ (locMap K S₀ v σ)) * c) ⊗ₜ[ℤ_[2]]
          (locMap K S₀ v σ • tateEquiv (S₀ := S₀) (S := S) W Q))
    have hξ : (ξ₀.comp (inflMap K hS).toMonoidHom) (locMap K S v σ) = ξ₀ (locMap K S₀ v σ) :=
      congrArg ξ₀ (locMap_compat K hS v σ)
    rw [TensorProduct.smul_tmul', zsmul_eq_mul, coe_lambdaChar, coe_lambdaChar,
      MonoidHom.one_apply, Units.val_one, Int.cast_one, one_mul, hξ, map_mul, map_intCast, mul_assoc]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add]

end PrimitiveCoefficientAction

end ZInQ.Contrib.RC53Assist.StrictSymmFull.CoefficientComparison

namespace ZInQ.Contrib.RC53Assist.StrictSymmFull.RetainedInflation

open CategoryTheory CategoryTheory.Limits TauCeti ValuativeRel
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.PairedFunctional

section FieldHomotopy

variable {k : Type} [Field k]

/-- Every actual cochain vector space is an injective object; no bounded-degree
or finite-dimensional hypothesis is needed for this elementary splitting. -/
theorem fieldModule_injective (V : ModuleCat k) : CategoryTheory.Injective V where
  factors g f m := by
    have hf : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).mp m
    obtain ⟨r, hr⟩ := f.hom.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
    refine ⟨ModuleCat.ofHom (g.hom.comp r), ?_⟩
    ext x
    exact congrArg g.hom (LinearMap.congr_fun hr x)

/-- Extension of the actual nonnegative cochains has no negative terms. -/
theorem natCx_nonnegative (C : CochainComplex (ModuleCat k) ℕ) :
    (natCx C).toCC.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  cases i with
  | ofNat n =>
    change (n : ℤ) < 0 at hi
    omega
  | negSucc n =>
    rw [IsZero.iff_id_eq_zero]
    ext x
    exact Subsingleton.elim (α := PUnit) _ _

/-- A quasi-isomorphism of retained nonnegative field complexes has a homotopy
inverse with exactly the specified forward map. This is not a printed premise. -/
theorem homotopyEquiv_of_nonnegative_field_quasiIso
    {C D : CochainComplex (ModuleCat k) ℤ} [C.IsStrictlyGE 0] [D.IsStrictlyGE 0]
    (f : C ⟶ D) (hf : QuasiIso f) : ∃ e : HomotopyEquiv C D, e.hom = f := by
  let : ∀ n : ℤ, CategoryTheory.Injective (C.X n) := fun n => fieldModule_injective (C.X n)
  let : ∀ n : ℤ, CategoryTheory.Injective (D.X n) := fun n => fieldModule_injective (D.X n)
  let : C.IsKInjective := CochainComplex.isKInjective_of_injective C 0
  let : D.IsKInjective := CochainComplex.isKInjective_of_injective D 0
  exact (CochainComplex.IsKInjective.quasiIso_iff f).mp hf

/-- In particular, acyclic retained field cochains have an all-degree contraction. -/
theorem nonnegative_field_contractible
    (C : CochainComplex (ModuleCat k) ℤ) [C.IsStrictlyGE 0] (hC : C.Acyclic) :
    Nonempty (Homotopy (𝟙 C) 0) := by
  let : ∀ n : ℤ, CategoryTheory.Injective (C.X n) := fun n => fieldModule_injective (C.X n)
  let : C.IsKInjective := CochainComplex.isKInjective_of_injective C 0
  exact CochainComplex.IsKInjective.nonempty_homotopy_zero (𝟙 C) hC

end FieldHomotopy

section RelationIndexedMaps

variable {k : Type} [CommRing k]

/-- Convert a retained relation-indexed morphism without changing any component. -/
def cochainMorphism {A B : GCx k} (f : GHom A B) : A.toCC ⟶ B.toCC where
  f n := ModuleCat.ofHom (f.f n n rfl)
  comm' i j hij := by
    ext x
    change ((B.toCC).d i j).hom ((f.f i i rfl) x) =
      (f.f j j rfl) (((A.toCC).d i j).hom x)
    rw [GCx.toCC_d_hom A i j hij x, GCx.toCC_d_hom B i j hij ((f.f i i rfl) x)]
    exact (f.comm i j i j rfl hij hij rfl x).symm

end RelationIndexedMaps

section CoefficientCochains

variable {k G M L : Type} [CommRing k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module k M] [TopologicalSpace M] [ContinuousAdd M]
  [DistribMulAction G M] [SMulCommClass G k M] [ContinuousConstSMul k M] [ContinuousSMul G M]
  [AddCommGroup L] [Module k L] [TopologicalSpace L] [ContinuousAdd L]
  [DistribMulAction G L] [SMulCommClass G k L] [ContinuousConstSMul k L] [ContinuousSMul G L]

/-- A continuous equivariant coefficient identification preserves all continuous cochains. -/
def coefficientCochainsIso (e : M ≃L[k] L) (he : ∀ (g : G) (x : M), e (g • x) = g • e x) :
    contCochains k G M ≅ contCochains k G L := by
  have hi : ∀ (g : G) (x : L), e.symm (g • x) = g • e.symm x := by
    intro g x
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  let f := contCochainsMap (ContinuousMonoidHom.id G) e.toLinearMap e.continuous he
  let g := contCochainsMap (ContinuousMonoidHom.id G) e.symm.toLinearMap e.symm.continuous hi
  refine { hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }
  · ext n x
    apply Subtype.ext
    funext p
    change e.symm (e (asFun k G M x.1 p)) = asFun k G M x.1 p
    exact e.symm_apply_apply _
  · ext n x
    apply Subtype.ext
    funext p
    change e (e.symm (asFun k G L x.1 p)) = asFun k G L x.1 p
    exact e.apply_symm_apply _

end CoefficientCochains

section ExtendedCoefficientIso

variable {k : Type} [CommRing k]

/-- Extending a coefficient cochain isomorphism retains every specified component. -/
def fullCochainsIso {C D : CochainComplex (ModuleCat k) ℕ} (e : C ≅ D) :
    (natCx C).toCC ≅ (natCx D).toCC where
  hom := cochainMorphism (natHom e.hom)
  inv := cochainMorphism (natHom e.inv)
  hom_inv_id := by
    ext i x
    cases i with
    | ofNat n =>
      exact congrArg (fun f : C ⟶ C => (f.f n).hom x) e.hom_inv_id
    | negSucc n => exact Subsingleton.elim (α := PUnit) _ _
  inv_hom_id := by
    ext i x
    cases i with
    | ofNat n =>
      exact congrArg (fun f : D ⟶ D => (f.f n).hom x) e.inv_hom_id
    | negSucc n => exact Subsingleton.elim (α := PUnit) _ _

end ExtendedCoefficientIso

section ActualCoefficientCochains

open NumberField IsDedekindDomain
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]
  [HasFullTwoTorsion K S₀ W] [HasFullTwoTorsion K S W]
  (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
  (α₀ : GKS K S₀ →* Lambdaˣ) [IsContChar α₀]
  (α : GKS K S →* Lambdaˣ) [IsContChar α]
  (v : HeightOneSpectrum (𝓞 K))

/-- The retained coefficient identification gives an isomorphism of all full
local continuous cochains, for the actual restricted coefficient fibres. -/
def actualLocalCoefficientCochains
    (hα : ∀ σ : Gloc K v, α (locMap K S v σ) = α₀ (locMap K S₀ v σ)) :
    (natCx (contCochains (ResAt P) (Gloc K v) (ResMod (locMap K S v) (VP K S W P α)))).toCC ≅
      (natCx (contCochains (ResAt P) (Gloc K v) (ResMod (locMap K S₀ v) (VP K S₀ W P α₀)))).toCC := by
  let e : ResMod (locMap K S v) (VP K S W P α) ≃L[ResAt P]
      ResMod (locMap K S₀ v) (VP K S₀ W P α₀) :=
    CoefficientComparison.fibreContinuousEquiv (S₀ := S₀) (S := S) W P α₀ α
  have he : ∀ (σ : Gloc K v) (x : ResMod (locMap K S v) (VP K S W P α)),
      e (σ • x) = σ • e x := by
    intro σ x
    exact CoefficientComparison.fibreEquiv_local_action (S₀ := S₀) (S := S) W P α₀ α v σ (hα σ) x
  exact fullCochainsIso (coefficientCochainsIso e he)

end ActualCoefficientCochains

namespace ActualTameKernel

open NumberField IsDedekindDomain TauCeti ValuativeRel

variable {K : Type} [Field K] [NumberField K]

/-- The prime-to-residue-characteristic radicals of actual local uniformizers. -/
def tameRadicals (v : HeightOneSpectrum (𝓞 K)) : Set (AlgebraicClosure (v.adicCompletion K)) :=
  {x | ∃ n : ℕ, 0 < n ∧ n.Coprime (ringChar 𝓀[v.adicCompletion K]) ∧
    ∃ π : (v.adicCompletion K)ˣ, normalizedValuation (v.adicCompletion K) π = .ofAdd 1 ∧
      x ^ n = algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) π}

/-- The unramified/tame-radical extension is fixed rather than chosen per proof. -/
def tameRadicalField (v : HeightOneSpectrum (𝓞 K)) :
    IntermediateField (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) :=
  maximalUnramifiedExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) ⊔
    IntermediateField.adjoin (v.adicCompletion K) (tameRadicals v)

/-- The normal fixing kernel of the actual tame-radical extension. Its pro-order
and its action on the coefficient fibre remain explicit arithmetic hypotheses. -/
def wildKernel (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gloc K v) :=
  (show Subgroup (Gloc K v) from (tameRadicalField v).fixingSubgroup).normalCore

instance wildKernel_normal (v : HeightOneSpectrum (𝓞 K)) : (wildKernel v).Normal := by
  unfold wildKernel
  infer_instance

/-- The specified fixing kernel is closed in the actual local Krull topology. -/
theorem wildKernel_closed (v : HeightOneSpectrum (𝓞 K)) :
    IsClosed (wildKernel v : Set (Gloc K v)) := by
  have h : IsClosed ((show Subgroup (Gloc K v) from (tameRadicalField v).fixingSubgroup) : Set (Gloc K v)) :=
    IntermediateField.fixingSubgroup_isClosed_of_isAlgebraic (tameRadicalField v)
  exact Subgroup.normalCore_isClosed _ h

/-- Every element of this kernel fixes the prescribed tame-radical extension. -/
theorem wildKernel_fixes (v : HeightOneSpectrum (𝓞 K)) (σ : wildKernel v)
    (x : AlgebraicClosure (v.adicCompletion K)) (hx : x ∈ tameRadicalField v) :
    (@id (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) σ.1) x = x := by
  have hs : σ.1 ∈ (show Subgroup (Gloc K v) from (tameRadicalField v).fixingSubgroup) :=
    (Subgroup.normalCore_le _) σ.2
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs x hx

/-- The actual tame fixing kernel lies in actual inertia, without a free subgroup identification. -/
theorem wildKernel_inertia (v : HeightOneSpectrum (𝓞 K)) (σ : wildKernel v) :
    σ.1 ∈ inertiaSubgroup (v.adicCompletion K) := by
  apply mem_inertiaSubgroup_iff.mpr
  intro x hx
  exact wildKernel_fixes v σ x ((show maximalUnramifiedExtension (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K)) ≤ tameRadicalField v from le_sup_left) hx)

end ActualTameKernel

section ActualLocalQuotient

open NumberField IsDedekindDomain
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (P : Ideal Lambda) [P.IsPrime]
  (α : GKS K S →* Lambdaˣ) (v : HeightOneSpectrum (𝓞 K)) (N : Subgroup (Gloc K v))

/-- The exact prime-to-two pro-order condition used by the cited inflation lemma. -/
class PrimeToTwoKernel : Prop where
  closed : IsClosed (N : Set (Gloc K v))
  odd_quotients : ∀ U : OpenNormalSubgroup N, (Nat.card (N ⧸ U.toSubgroup)).Coprime 2

/-- Triviality is stated on the actual restricted coefficient fibre. -/
class KernelActsTrivially : Prop where
  fixes : ∀ (σ : N) (x : VP K S W P α), locMap K S v σ.1 • x = x

/-- The actual local quotient, with its quotient group and quotient topology retained. -/
def LocalQuotient : Type := Gloc K v ⧸ N

instance localQuotientGroup [N.Normal] : Group (LocalQuotient v N) :=
  inferInstanceAs (Group (Gloc K v ⧸ N))
instance localQuotientTopology : TopologicalSpace (LocalQuotient v N) :=
  inferInstanceAs (TopologicalSpace (Gloc K v ⧸ N))
instance localQuotientTopologicalGroup [N.Normal] : IsTopologicalGroup (LocalQuotient v N) :=
  inferInstanceAs (IsTopologicalGroup (Gloc K v ⧸ N))

/-- The specified quotient map from the actual absolute local group. -/
def localQuotientMap [N.Normal] : Gloc K v →ₜ* LocalQuotient v N where
  toFun := QuotientGroup.mk' N
  map_one' := map_one (QuotientGroup.mk' N)
  map_mul' := map_mul (QuotientGroup.mk' N)
  continuous_toFun := QuotientGroup.continuous_mk

/-- This coefficient carrier is the same actual fibre, with no discrete replacement. -/
def QuotientCoefficients (_v : HeightOneSpectrum (𝓞 K)) (_N : Subgroup (Gloc K _v)) : Type := VP K S W P α

instance quotientCoefficientAdd : AddCommGroup (QuotientCoefficients W P α v N) :=
  inferInstanceAs (AddCommGroup (VP K S W P α))
instance quotientCoefficientModule : Module (ResAt P) (QuotientCoefficients W P α v N) :=
  inferInstanceAs (Module (ResAt P) (VP K S W P α))
instance quotientCoefficientTopology : TopologicalSpace (QuotientCoefficients W P α v N) :=
  inferInstanceAs (TopologicalSpace (VP K S W P α))
instance quotientCoefficientTopologicalAddGroup : IsTopologicalAddGroup (QuotientCoefficients W P α v N) :=
  inferInstanceAs (IsTopologicalAddGroup (VP K S W P α))
instance quotientCoefficientConstantScalar [IsHeightOneOdd P] :
    ContinuousConstSMul (ResAt P) (QuotientCoefficients W P α v N) :=
  inferInstanceAs (ContinuousConstSMul (ResAt P) (VP K S W P α))

/-- The original local action is bundled before descent to the quotient. -/
def localEndAction : Gloc K v →* Module.End (ResAt P) (QuotientCoefficients W P α v N) where
  toFun σ :=
    { toFun x := (show QuotientCoefficients W P α v N from locMap K S v σ • (show VP K S W P α from x))
      map_add' x y := by
        change locMap K S v σ • ((show VP K S W P α from x) + (show VP K S W P α from y)) =
          locMap K S v σ • (show VP K S W P α from x) + locMap K S v σ • (show VP K S W P α from y)
        exact smul_add (locMap K S v σ) _ _
      map_smul' c x := by
        change locMap K S v σ • (c • (show VP K S W P α from x)) =
          c • (locMap K S v σ • (show VP K S W P α from x))
        exact smul_comm (locMap K S v σ) c _ }
  map_one' := by
    ext x
    change locMap K S v 1 • (show VP K S W P α from x) = x
    rw [map_one, one_smul]
  map_mul' σ τ := by
    ext x
    change locMap K S v (σ * τ) • (show VP K S W P α from x) =
      locMap K S v σ • (locMap K S v τ • (show VP K S W P α from x))
    rw [map_mul, mul_smul]

/-- Descent of that same action uses only the actual kernel-triviality hypothesis. -/
def quotientEndAction [N.Normal] [KernelActsTrivially W P α v N] :
    LocalQuotient v N →* Module.End (ResAt P) (QuotientCoefficients W P α v N) :=
  QuotientGroup.lift N (localEndAction W P α v N) (by
    intro σ hσ
    ext x
    exact KernelActsTrivially.fixes (W := W) (P := P) (α := α) (v := v) (N := N) ⟨σ, hσ⟩ x)

instance quotientCoefficientAction [N.Normal] [KernelActsTrivially W P α v N] :
    DistribMulAction (LocalQuotient v N) (QuotientCoefficients W P α v N) where
  smul σ x := quotientEndAction W P α v N σ x
  one_smul x := by
    change quotientEndAction W P α v N 1 x = x
    rw [map_one]
    rfl
  mul_smul σ τ x := by
    change quotientEndAction W P α v N (σ * τ) x =
      quotientEndAction W P α v N σ (quotientEndAction W P α v N τ x)
    rw [map_mul]
    rfl
  smul_zero σ := (quotientEndAction W P α v N σ).map_zero
  smul_add σ := (quotientEndAction W P α v N σ).map_add

instance quotientCoefficientScalarComm [N.Normal] [KernelActsTrivially W P α v N] :
    SMulCommClass (LocalQuotient v N) (ResAt P) (QuotientCoefficients W P α v N) where
  smul_comm σ c x := (quotientEndAction W P α v N σ).map_smul c x

/-- Pullback of the descended action is the original specified local action. -/
theorem quotientCoefficient_pullback [N.Normal] [KernelActsTrivially W P α v N]
    (σ : Gloc K v) (x : QuotientCoefficients W P α v N) :
    localQuotientMap v N σ • x =
      (show QuotientCoefficients W P α v N from locMap K S v σ • (show VP K S W P α from x)) := rfl

/-- The quotient action is jointly continuous for the unchanged lattice topology. -/
instance quotientCoefficientContinuous [N.Normal] [IsHeightOneOdd P] [IsContChar α]
    [KernelActsTrivially W P α v N] :
    ContinuousSMul (LocalQuotient v N) (QuotientCoefficients W P α v N) where
  continuous_smul := by
    let q : Gloc K v × QuotientCoefficients W P α v N →
        LocalQuotient v N × QuotientCoefficients W P α v N :=
      fun p => (localQuotientMap v N p.1, p.2)
    have hq : IsOpenQuotientMap q :=
      QuotientGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id
    apply hq.continuous_comp_iff.mp
    change Continuous (fun p : Gloc K v × VP K S W P α => locMap K S v p.1 • p.2)
    exact ((locMap K S v).continuous.comp continuous_fst).smul continuous_snd

/-- The coefficient part of inflation is literally the identity of the actual fibre. -/
def coefficientIdentity : QuotientCoefficients W P α v N →ₗ[ResAt P] ResMod (locMap K S v) (VP K S W P α) :=
  LinearMap.id

/-- This identity retains the coefficient topology. -/
theorem coefficientIdentity_continuous : Continuous (coefficientIdentity W P α v N) := continuous_id

/-- The compatible pair used by inflation is the specified quotient map and identity. -/
theorem coefficientIdentity_compatible [N.Normal] [KernelActsTrivially W P α v N]
    (σ : Gloc K v) (x : QuotientCoefficients W P α v N) :
    coefficientIdentity W P α v N (localQuotientMap v N σ • x) =
      σ • coefficientIdentity W P α v N x := rfl

/-- The retained quotient cochains, in all integer degrees. -/
abbrev quotientFull [N.Normal] [IsHeightOneOdd P] [IsContChar α]
    [KernelActsTrivially W P α v N] : GCx (ResAt P) :=
  natCx (contCochains (ResAt P) (LocalQuotient v N) (QuotientCoefficients W P α v N))

/-- The retained full absolute local cochains on the actual coefficient fibre. -/
abbrev absoluteFull [IsHeightOneOdd P] [IsContChar α] : GCx (ResAt P) :=
  natCx (contCochains (ResAt P) (Gloc K v) (ResMod (locMap K S v) (VP K S W P α)))

/-- Inflation is constructed in every cochain degree, not only on low-degree cohomology. -/
def inflation [N.Normal] [IsHeightOneOdd P] [IsContChar α]
    [KernelActsTrivially W P α v N] :
    (quotientFull W P α v N).toCC ⟶ (absoluteFull W P α v).toCC :=
  cochainMorphism (natHom (contCochainsMap (localQuotientMap v N) (coefficientIdentity W P α v N)
    (coefficientIdentity_continuous W P α v N) (coefficientIdentity_compatible W P α v N)))

/-- Kernel triviality on the actual fibre follows from its actual Tate and
character actions; it is not an abstract homological assumption. -/
theorem kernelActsTrivially_of_tate_character
    (hT : ∀ (σ : N) (Q : ZInQ.Manuscript.RC.LambdaCoef.TateS K S W), locMap K S v σ.1 • Q = Q)
    (hα : ∀ σ : N, α (locMap K S v σ.1) = 1) : KernelActsTrivially W P α v N := by
  refine ⟨fun σ x => ?_⟩
  induction x using VP.induction with
  | zero => rw [smul_zero]
  | tmul c Q =>
    rw [VP.smul_tmul, coe_resChar, hα σ, Units.val_one, map_one, one_mul, hT σ Q]
  | add x y hx hy => rw [smul_add, hx, hy]

end ActualLocalQuotient

section ActualPrimitiveKernel

open NumberField IsDedekindDomain TauCeti ValuativeRel
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
  ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]
  [HasFullTwoTorsion K S₀ W] [HasFullTwoTorsion K S W]

/-- The actual tame fixing kernel is killed by the retained unramified restriction. -/
theorem wildKernel_urRes_one (v : HeightOneSpectrum (𝓞 K)) (σ : ActualTameKernel.wildKernel v) :
    urRes K v σ.1 = 1 := by
  have hI := ActualTameKernel.wildKernel_inertia v σ
  change restrictMaximalUnramifiedHom (v.adicCompletion K) σ.1 = 1
  rw [← ker_restrictMaximalUnramifiedHom] at hI
  exact hI

/-- Full torsion over the smaller support fixes the actual whole Tate module
under the tame kernel at each old place outside that support. -/
theorem wildKernel_tate_fixed (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S₀)
    (σ : ActualTameKernel.wildKernel v) (Q : TateS K S W) : locMap K S v σ.1 • Q = Q := by
  apply (CoefficientComparison.tateEquiv (S₀ := S₀) (S := S) W).injective
  rw [CoefficientComparison.tateEquiv_local_action (S₀ := S₀) (S := S) W v σ.1]
  rw [locMap_eq_one_of_urRes_eq_one K S₀ v hv σ.1 (wildKernel_urRes_one v σ), one_smul]

variable (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)

/-- The actual local square root of a primitive radicand is fixed by the tame kernel. -/
theorem primitive_wild_quadChar (v : HeightOneSpectrum (𝓞 K))
    (hodd : (2 : ℕ).Coprime (ringChar 𝓀[v.adicCompletion K]))
    (hh0 : algebraMap K (v.adicCompletion K) h ≠ 0)
    (hv : normalizedValuation (v.adicCompletion K)
      (Units.mk0 (algebraMap K (v.adicCompletion K) h) hh0) = .ofAdd 1)
    (σ : ActualTameKernel.wildKernel v) : quadChar s hs hs0 (locMap K S v σ.1) = 1 := by
  have hrad : localSqrt s v ∈ ActualTameKernel.tameRadicals v :=
    ⟨2, by decide, hodd, Units.mk0 (algebraMap K (v.adicCompletion K) h) hh0,
      hv, localSqrt_sq s hs v⟩
  have hfix := ActualTameKernel.wildKernel_fixes v σ (localSqrt s v)
    ((show IntermediateField.adjoin (v.adicCompletion K) (ActualTameKernel.tameRadicals v) ≤
      ActualTameKernel.tameRadicalField v from le_sup_right) (IntermediateField.subset_adjoin (v.adicCompletion K) _ hrad))
  have hgs : galS K S (locMap K S v σ.1) s = s := by
    apply (embS K S v).injective
    exact (embS_locMap K S v σ.1 s).trans hfix
  simp [quadChar, hgs]

/-- Wild-kernel triviality is now bound to the actual old primitive fibre,
including the inflated moving character and the genuine Tate action. -/
theorem actual_old_primitive_kernel_trivial
    (hS : S₀ ⊆ S) (P : Ideal Lambda) [P.IsPrime]
    (ξ₀ : GKS K S₀ →* Multiplicative ℤ_[2])
    (v : Places K S) (hv₀ : v.1 ∉ S₀)
    (hodd : (2 : ℕ).Coprime (ringChar 𝓀[v.1.adicCompletion K]))
    (hh0 : algebraMap K (v.1.adicCompletion K) h ≠ 0)
    (hv : normalizedValuation (v.1.adicCompletion K)
      (Units.mk0 (algebraMap K (v.1.adicCompletion K) h) hh0) = .ofAdd 1) :
    KernelActsTrivially W P (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom))
      v.1 (ActualTameKernel.wildKernel v.1) := by
  apply kernelActsTrivially_of_tate_character W P _ v.1 _
  · exact wildKernel_tate_fixed (S₀ := S₀) (S := S) W v.1 hv₀
  · intro σ
    have hχ := primitive_wild_quadChar s hs hs0 v.1 hodd hh0 hv σ
    have hξ : (ξ₀.comp (inflMap K hS).toMonoidHom) (locMap K S v.1 σ.1) = 1 := by
      change ξ₀ (inflMap K hS (locMap K S v.1 σ.1)) = 1
      rw [locMap_compat K hS v.1 σ.1,
        locMap_eq_one_of_urRes_eq_one K S₀ v.1 hv₀ σ.1 (wildKernel_urRes_one v.1 σ), map_one]
    apply Units.ext
    have hz : Multiplicative.toAdd (1 : Multiplicative ℤ_[2]) = 0 := rfl
    rw [coe_lambdaChar, hχ, hξ, hz, Units.val_one, Int.cast_one, onePlusTPow_zero, one_mul]
    rfl

end ActualPrimitiveKernel

/-- Specialized cited input: Nekovář, Selmer complexes, Lemma 4.1.4 (p. 96),
with residual characteristic two, together with the localized-coefficient
identification of Proposition 3.7.4(ii) (p. 94). The coefficient topology, action
and inflation map below are fixed actual ones. This input asserts only the
quasi-isomorphism; the homotopy inverse is proved separately. -/
def Nekovar414Fibre : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (W : WeierstrassCurve K) [W.IsElliptic] [ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S W]
    (P : Ideal ZInQ.Manuscript.RC.Uniform.Lambda) [P.IsPrime]
    [ZInQ.Manuscript.RC.LambdaCoef.IsHeightOneOdd P]
    (α : GKS K S →* ZInQ.Manuscript.RC.Uniform.Lambdaˣ)
    [ZInQ.Manuscript.RC.LambdaCoef.IsContChar α]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (N : Subgroup (Gloc K v)) [N.Normal] [PrimeToTwoKernel v N]
    [KernelActsTrivially W P α v N], QuasiIso (inflation W P α v N)

/-- The cited quasi-isomorphism supplies a retained all-degree homotopy comparison,
with forward map equal to the actual inflation map. -/
theorem absolute_inflation_homotopy
    (hprint : Nekovar414Fibre) {K : Type} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (W : WeierstrassCurve K) [W.IsElliptic] [ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S W]
    (P : Ideal ZInQ.Manuscript.RC.Uniform.Lambda) [P.IsPrime]
    [ZInQ.Manuscript.RC.LambdaCoef.IsHeightOneOdd P]
    (α : GKS K S →* ZInQ.Manuscript.RC.Uniform.Lambdaˣ)
    [ZInQ.Manuscript.RC.LambdaCoef.IsContChar α]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (N : Subgroup (Gloc K v)) [N.Normal] [PrimeToTwoKernel v N]
    [KernelActsTrivially W P α v N] :
    ∃ e : HomotopyEquiv (quotientFull W P α v N).toCC (absoluteFull W P α v).toCC,
      e.hom = inflation W P α v N := by
  have hq := natCx_nonnegative
    (contCochains (ZInQ.Manuscript.RC.Wiring.ResAt P) (LocalQuotient v N)
      (QuotientCoefficients W P α v N))
  have ha := natCx_nonnegative
    (contCochains (ZInQ.Manuscript.RC.Wiring.ResAt P) (Gloc K v)
      (ResMod (locMap K S v) (ZInQ.Manuscript.RC.LambdaCoef.VP K S W P α)))
  exact homotopyEquiv_of_nonnegative_field_quasiIso (inflation W P α v N)
    (hprint K S W P α v N)

/-- A genuine pro-ell certificate at an odd place discharges the exact
prime-to-two pro-order hypothesis; the two notions are not confused. -/
theorem primeToTwoKernel_of_proOdd
    {K : Type} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (N : Subgroup (Gloc K v)) (hclosed : IsClosed (N : Set (Gloc K v)))
    (ell : ℕ) (hell : ell.Prime) (hne : ell ≠ 2) (hpro : TauCeti.IsProP ell N) :
    PrimeToTwoKernel v N := by
  have : CompactSpace (Gloc K v) := inferInstance
  have : CompactSpace N := isCompact_iff_compactSpace.mp hclosed.isCompact
  have : Fact ell.Prime := ⟨hell⟩
  refine ⟨hclosed, fun U => ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hpro U)
  rw [hn]
  exact ((Nat.coprime_primes hell Nat.prime_two).mpr hne).pow_left n

/-- At every actual retained place, the fixed tame-radical kernel gives a
comparison of the retained absolute cochains with its actual quotient cochains.
The reverse morphism is exactly the specified inflation. -/
theorem old_place_absolute_tame_comparison
    (hprint : Nekovar414Fibre) {K : Type} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (W : WeierstrassCurve K) [W.IsElliptic] [ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S W]
    (P : Ideal ZInQ.Manuscript.RC.Uniform.Lambda) [P.IsPrime]
    [ZInQ.Manuscript.RC.LambdaCoef.IsHeightOneOdd P]
    (α : GKS K S →* ZInQ.Manuscript.RC.Uniform.Lambdaˣ)
    [ZInQ.Manuscript.RC.LambdaCoef.IsContChar α]
    (v : Places K S) [PrimeToTwoKernel v.1 (ActualTameKernel.wildKernel v.1)]
    [KernelActsTrivially W P α v.1 (ActualTameKernel.wildKernel v.1)] :
    ∃ e : HomotopyEquiv (absoluteFull W P α v.1).toCC
      (quotientFull W P α v.1 (ActualTameKernel.wildKernel v.1)).toCC,
      e.inv = inflation W P α v.1 (ActualTameKernel.wildKernel v.1) := by
  obtain ⟨e, he⟩ := absolute_inflation_homotopy hprint W P α v.1 (ActualTameKernel.wildKernel v.1)
  exact ⟨e.symm, he⟩

section TameNorm

variable {k M : Type} [CommRing k] [AddCommGroup M] [Module k M]

/-- The full geometric tame norm; no quadratic truncation is made. -/
def geometricNorm (L : ℕ) (t : Module.End k M) : Module.End k M :=
  ∑ i ∈ Finset.range L, t ^ i

/-- The full norm satisfies the actual tame telescoping identity. -/
theorem geometricNorm_identity (L : ℕ) (t : Module.End k M) :
    geometricNorm L t * (t - 1) = t ^ L - 1 := by
  induction L with
  | zero => simp [geometricNorm]
  | succ L ih =>
    rw [geometricNorm, Finset.sum_range_succ, add_mul, ← geometricNorm, ih, mul_sub, pow_succ, mul_one]
    noncomm_ring

/-- The geometric Frobenius relation gives the correct small-complex identity. -/
theorem geometric_tame_relation (L : ℕ) (f t : Module.End k M) (hft : t * f = f * t ^ L) :
    (f * geometricNorm L t - 1) * (t - 1) = (t - 1) * (f - 1) := by
  calc
    _ = f * (geometricNorm L t * (t - 1)) - (t - 1) := by noncomm_ring
    _ = f * (t ^ L - 1) - (t - 1) := by rw [geometricNorm_identity]
    _ = (t - 1) * (f - 1) := by rw [mul_sub, ← hft]; noncomm_ring

end TameNorm

section TameFrame

open NumberField IsDedekindDomain TauCeti ValuativeRel
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (v : HeightOneSpectrum (𝓞 K)) (N : Subgroup (Gloc K v)) [N.Normal]

/-- The actual tame generators and geometric Frobenius convention of
Nekovář 7.2.1, retaining their lifts and the inertia image. -/
structure TameFrame where
  t : Gloc K v
  f : Gloc K v
  inertia : t ∈ inertiaSubgroup (v.adicCompletion K)
  frobenius : IsArithFrobeniusLift (v.adicCompletion K) f⁻¹
  dense_inertia : (Subgroup.zpowers (localQuotientMap v N t)).topologicalClosure =
    (inertiaSubgroup (v.adicCompletion K)).map (localQuotientMap v N).toMonoidHom
  relation : localQuotientMap v N t * localQuotientMap v N f =
    localQuotientMap v N f * (localQuotientMap v N t) ^ Nat.card 𝓀[v.adicCompletion K]

variable (W : WeierstrassCurve K) (P : Ideal Lambda) [P.IsPrime]
  (α : GKS K S →* Lambdaˣ) [KernelActsTrivially W P α v N]

/-- The small-complex relation uses the actual descended coefficient representation. -/
theorem frame_operator_relation (F : TameFrame v N) :
    quotientEndAction W P α v N (localQuotientMap v N F.t) *
      quotientEndAction W P α v N (localQuotientMap v N F.f) =
    quotientEndAction W P α v N (localQuotientMap v N F.f) *
      (quotientEndAction W P α v N (localQuotientMap v N F.t)) ^ Nat.card 𝓀[v.adicCompletion K] := by
  have h := congrArg (quotientEndAction W P α v N) F.relation
  simpa only [map_mul, map_pow] using h

/-- The exact three-term complex of Nekovář 7.2.1, with the full tame norm. -/
def frameTameComplex (F : TameFrame v N) : CochainComplex (ModuleCat (ResAt P)) ℤ :=
  tameComplex
    (quotientEndAction W P α v N (localQuotientMap v N F.f) - 1)
    (quotientEndAction W P α v N (localQuotientMap v N F.t) - 1)
    (quotientEndAction W P α v N (localQuotientMap v N F.f) *
      geometricNorm (Nat.card 𝓀[v.adicCompletion K])
        (quotientEndAction W P α v N (localQuotientMap v N F.t)) - 1)
    (geometric_tame_relation _ _ _ (frame_operator_relation v N W P α F))

variable [IsHeightOneOdd P] [IsContChar α]

/-- Values of the actual continuous cochains, without a discreteness premise. -/
def quotientValue (n : ℕ) (x : (quotientFull W P α v N).X n) :
    (Fin n → LocalQuotient v N) → QuotientCoefficients W P α v N :=
  asFun (ResAt P) (LocalQuotient v N) (QuotientCoefficients W P α v N) x.1

/-- The explicit degree-zero formula in the cited tame comparison. -/
def frameLambdaZero (x : (quotientFull W P α v N).X 0) : QuotientCoefficients W P α v N :=
  quotientValue v N W P α 0 x Fin.elim0

/-- The explicit degree-one formula retains geometric Frobenius and inertia. -/
def frameLambdaOne (F : TameFrame v N) (x : (quotientFull W P α v N).X 1) :
    QuotientCoefficients W P α v N × QuotientCoefficients W P α v N :=
  (quotientValue v N W P α 1 x (fun _ => localQuotientMap v N F.f),
    quotientValue v N W P α 1 x (fun _ => localQuotientMap v N F.t))

/-- The complete degree-two formula of Nekovář Proposition 7.2.3 (p. 158). -/
def frameLambdaTwo (F : TameFrame v N) (x : (quotientFull W P α v N).X 2) :
    QuotientCoefficients W P α v N :=
  let t := localQuotientMap v N F.t
  let f := localQuotientMap v N F.f
  let L := Nat.card 𝓀[v.adicCompletion K]
  let z : LocalQuotient v N → LocalQuotient v N → QuotientCoefficients W P α v N :=
    fun a b => quotientValue v N W P α 2 x ![a,b]
  (-z t f + z f (t ^ L) + f • (∑ i ∈ Finset.range (L - 1), t ^ i • z t (t ^ (L - 1 - i))))

/-- The cited comparison is a cochain map with precisely these retained formulas. -/
structure FrameComparison (F : TameFrame v N) where
  map : (quotientFull W P α v N).toCC ⟶ frameTameComplex v N W P α F
  zero_formula : ∀ x, (map.f 0).hom x = frameLambdaZero v N W P α x
  one_formula : ∀ x, (map.f 1).hom x = frameLambdaOne v N W P α F x
  two_formula : ∀ x, (map.f 2).hom x = frameLambdaTwo v N W P α F x
  quasiIso : QuasiIso map

omit [IsHeightOneOdd P] [IsContChar α] in
/-- The correct tame model is bounded below, with its actual coefficients retained. -/
theorem frameTame_nonnegative (F : TameFrame v N) : (frameTameComplex v N W P α F).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [IsZero.iff_id_eq_zero]
  ext x
  have hs : Subsingleton ((frameTameComplex v N W P α F).X i) :=
    threeTermX_subsingleton (S := ResAt P) (M := QuotientCoefficients W P α v N)
      (N := QuotientCoefficients W P α v N × QuotientCoefficients W P α v N)
      (M' := QuotientCoefficients W P α v N) i (by omega) (by omega) (by omega)
  exact hs.elim _ _

/-- A formula-preserving quasi-isomorphism of this tame frame has an all-degree
homotopy inverse without a further printed comparison premise. -/
theorem frame_comparison_homotopy (F : TameFrame v N) (C : FrameComparison v N W P α F) :
    ∃ e : HomotopyEquiv (quotientFull W P α v N).toCC (frameTameComplex v N W P α F),
      e.hom = C.map := by
  have hq := natCx_nonnegative
    (contCochains (ResAt P) (LocalQuotient v N) (QuotientCoefficients W P α v N))
  have ht := frameTame_nonnegative v N W P α F
  exact homotopyEquiv_of_nonnegative_field_quasiIso C.map C.quasiIso

end TameFrame

/-- Specialized local-structure input from Nekovář 7.2.1 (p. 156): the actual
wild fixing kernel is pro-residue-characteristic and the tame quotient admits
the indicated procyclic-inertia/geometric-Frobenius frame. It is separate from
both cohomological comparison inputs and contains no contraction. -/
def Nekovar721Structure : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
    ringChar 𝓀[v.adicCompletion K] ≠ 2 →
      TauCeti.IsProP (ringChar 𝓀[v.adicCompletion K]) (ActualTameKernel.wildKernel v) ∧
        Nonempty (TameFrame v (ActualTameKernel.wildKernel v))

/-- The cited local structure discharges the exact wild pro-order requirement
for every actual odd old place, rather than assuming it for a freely chosen kernel. -/
theorem actual_wild_primeToTwo (h721 : Nekovar721Structure)
    {K : Type} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hodd : ringChar 𝓀[v.adicCompletion K] ≠ 2) :
    PrimeToTwoKernel v (ActualTameKernel.wildKernel v) :=
  primeToTwoKernel_of_proOdd v (ActualTameKernel.wildKernel v) (ActualTameKernel.wildKernel_closed v)
    (ringChar 𝓀[v.adicCompletion K]) (CharP.prime_ringChar _) hodd (h721 K v hodd).1

/-- Second specialized cited input: Nekovář Proposition 7.2.3 (pp. 158–160),
with its specified formulas and the localized coefficient identification of
3.7.4(ii). The actual quotient, coefficient topology and tame frame are fixed.
This statement asserts only the formula-preserving quasi-isomorphism. -/
def Nekovar723Fibre : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (W : WeierstrassCurve K) [W.IsElliptic] [ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S W]
    (P : Ideal ZInQ.Manuscript.RC.Uniform.Lambda) [P.IsPrime]
    [ZInQ.Manuscript.RC.LambdaCoef.IsHeightOneOdd P]
    (α : GKS K S →* ZInQ.Manuscript.RC.Uniform.Lambdaˣ)
    [ZInQ.Manuscript.RC.LambdaCoef.IsContChar α]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (_hodd : ringChar 𝓀[v.adicCompletion K] ≠ 2)
    [PrimeToTwoKernel v (ActualTameKernel.wildKernel v)]
    [KernelActsTrivially W P α v (ActualTameKernel.wildKernel v)]
    (F : TameFrame v (ActualTameKernel.wildKernel v)),
      Nonempty (FrameComparison v (ActualTameKernel.wildKernel v) W P α F)

/-- Assemble the retained absolute-to-tame comparison from the two cited
quasi-isomorphisms. The inverse-to-absolute leg is precisely inflation. -/
theorem retained_absolute_tame_homotopy
    (h414 : Nekovar414Fibre) (h723 : Nekovar723Fibre)
    {K : Type} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (W : WeierstrassCurve K) [W.IsElliptic] [ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S W]
    (P : Ideal ZInQ.Manuscript.RC.Uniform.Lambda) [P.IsPrime]
    [ZInQ.Manuscript.RC.LambdaCoef.IsHeightOneOdd P]
    (α : GKS K S →* ZInQ.Manuscript.RC.Uniform.Lambdaˣ)
    [ZInQ.Manuscript.RC.LambdaCoef.IsContChar α]
    (v : Places K S) (hodd : ringChar 𝓀[v.1.adicCompletion K] ≠ 2)
    [PrimeToTwoKernel v.1 (ActualTameKernel.wildKernel v.1)]
    [KernelActsTrivially W P α v.1 (ActualTameKernel.wildKernel v.1)]
    (F : TameFrame v.1 (ActualTameKernel.wildKernel v.1)) :
    ∃ (A : HomotopyEquiv (quotientFull W P α v.1 (ActualTameKernel.wildKernel v.1)).toCC
          (absoluteFull W P α v.1).toCC)
      (C : FrameComparison v.1 (ActualTameKernel.wildKernel v.1) W P α F)
      (B : HomotopyEquiv (quotientFull W P α v.1 (ActualTameKernel.wildKernel v.1)).toCC
          (frameTameComplex v.1 (ActualTameKernel.wildKernel v.1) W P α F)),
      A.hom = inflation W P α v.1 (ActualTameKernel.wildKernel v.1) ∧ B.hom = C.map ∧
      Nonempty (HomotopyEquiv (absoluteFull W P α v.1).toCC
        (frameTameComplex v.1 (ActualTameKernel.wildKernel v.1) W P α F)) := by
  obtain ⟨A, hA⟩ := absolute_inflation_homotopy h414 W P α v.1 (ActualTameKernel.wildKernel v.1)
  obtain ⟨C⟩ := h723 K S W P α v.1 hodd F
  obtain ⟨B, hB⟩ := frame_comparison_homotopy v.1 (ActualTameKernel.wildKernel v.1) W P α F C
  exact ⟨A, C, B, hA, hB, ⟨A.symm.trans B⟩⟩

section FrameContractions

open NumberField IsDedekindDomain
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] [HasFullTwoTorsion K S W]
  (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
  (α : GKS K S →* Lambdaˣ) [IsContChar α]
  (v : Places K S) [PrimeToTwoKernel v.1 (ActualTameKernel.wildKernel v.1)]
  [KernelActsTrivially W P α v.1 (ActualTameKernel.wildKernel v.1)]
  (F : TameFrame v.1 (ActualTameKernel.wildKernel v.1))

/-- The precise unit tests for the actual correct tame operators. -/
def FrameUnitTests : Prop :=
  let t := quotientEndAction W P α v.1 (ActualTameKernel.wildKernel v.1)
    (localQuotientMap v.1 (ActualTameKernel.wildKernel v.1) F.t)
  let f := quotientEndAction W P α v.1 (ActualTameKernel.wildKernel v.1)
    (localQuotientMap v.1 (ActualTameKernel.wildKernel v.1) F.f)
  (IsUnit (f - 1) ∧ IsUnit (f * geometricNorm (Nat.card 𝓀[v.1.adicCompletion K]) t - 1)) ∨
    IsUnit (t - 1)

/-- The displayed inertia/Frobenius contraction is transported through the
retained all-degree absolute/tame comparison for the actual old place. -/
theorem absolute_contraction_of_frame (h414 : Nekovar414Fibre) (h723 : Nekovar723Fibre)
    (hodd : ringChar 𝓀[v.1.adicCompletion K] ≠ 2) (hunit : FrameUnitTests W P α v F) :
    Nonempty (ZInQ.Contrib.RC53Assist.StrictSymmFull.Contraction (absoluteFull W P α v.1)) := by
  obtain ⟨A, C, B, _, _, ⟨e⟩⟩ := retained_absolute_tame_homotopy h414 h723 W P α v hodd F
  have hm : Nonempty (Homotopy (𝟙 (frameTameComplex v.1 (ActualTameKernel.wildKernel v.1) W P α F)) 0) :=
    tameComplexContractible_proof (ResAt P)
      (QuotientCoefficients W P α v.1 (ActualTameKernel.wildKernel v.1)) _ _ _ _ hunit
  obtain ⟨H⟩ := contractible_of_homotopyEquiv e hm
  exact ⟨ZInQ.Contrib.RC53Assist.StrictSymmFull.Contraction.ofHomotopy H⟩

omit [W.IsElliptic] [HasFullTwoTorsion K S W] [IsContChar α]
  [PrimeToTwoKernel v.1 (ActualTameKernel.wildKernel v.1)] in
/-- The tame-frame inertia-minus-one unit can be checked directly on the actual
restricted fibre; no unrelated endomorphism is introduced. -/
theorem frameUnitTests_of_primitive
    (hσ : ∀ x : VP K S W P α, locMap K S v.1 F.t • x = -x) : FrameUnitTests W P α v F := by
  apply Or.inr
  have ht : quotientEndAction W P α v.1 (ActualTameKernel.wildKernel v.1)
      (localQuotientMap v.1 (ActualTameKernel.wildKernel v.1) F.t) = -1 := by
    ext x
    exact hσ x
  rw [ht]
  have he : (-1 : Module.End (ResAt P) (QuotientCoefficients W P α v.1 (ActualTameKernel.wildKernel v.1))) - 1 =
      algebraMap (ResAt P) (Module.End (ResAt P)
        (QuotientCoefficients W P α v.1 (ActualTameKernel.wildKernel v.1))) (-2) := by
    ext x
    change -x - x = (-2 : ResAt P) • x
    rw [show (-2 : ResAt P) = -(1 + 1) from by ring, neg_smul, add_smul, one_smul,
      sub_eq_add_neg, neg_add]
  rw [he]
  exact (isUnit_two_resAt (IsHeightOneOdd.height_eq (P := P)) (IsHeightOneOdd.ne_two (P := P))).neg.map _

end FrameContractions

section PrimitiveFrameBinding

open NumberField IsDedekindDomain TauCeti ValuativeRel Filter Topology
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
  ZInQ.Manuscript.RC.KummerMaps ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

/-- Open-kernel characters are continuous even when no scalar topology is changed. -/
theorem continuous_openKernel_character {G H : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] (χ : G →* H)
    (hker : IsOpen (χ.ker : Set G)) : Continuous χ := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hU := hker.preimage (show Continuous (fun x : G => g⁻¹ * x) from continuous_const.mul continuous_id)
  have hg : g ∈ (fun x : G => g⁻¹ * x) ⁻¹' (χ.ker : Set G) := by
    change χ (g⁻¹ * g) = 1
    rw [inv_mul_cancel, map_one]
  apply (continuousAt_const : ContinuousAt (fun _ : G => χ g) g).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hg] with x hx
  have he : χ (g⁻¹ * x) = 1 := hx
  rw [map_mul, map_inv] at he
  exact (inv_mul_eq_one.mp he).symm

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
  (v : HeightOneSpectrum (𝓞 K))
  (hodd : (2 : ℕ).Coprime (ringChar 𝓀[v.adicCompletion K]))
  (hh0 : algebraMap K (v.adicCompletion K) h ≠ 0)
  (hv : normalizedValuation (v.adicCompletion K)
    (Units.mk0 (algebraMap K (v.adicCompletion K) h) hh0) = .ofAdd 1)

/-- The actual primitive quadratic character descends to the prescribed tame quotient. -/
def primitiveQuotientSign : LocalQuotient v (ActualTameKernel.wildKernel v) →* ℤˣ :=
  QuotientGroup.lift (ActualTameKernel.wildKernel v)
    ((quadChar s hs hs0).comp (locMap K S v).toMonoidHom) (by
      intro σ hσ
      exact primitive_wild_quadChar s hs hs0 v hodd hh0 hv ⟨σ, hσ⟩)

/-- Descent retains the specified character value on every absolute local element. -/
theorem primitiveQuotientSign_pullback (σ : Gloc K v) :
    primitiveQuotientSign s hs hs0 v hodd hh0 hv
      (localQuotientMap v (ActualTameKernel.wildKernel v) σ) =
        quadChar s hs hs0 (locMap K S v σ) := rfl

/-- The descended sign is continuous for the genuine quotient topology. -/
theorem primitiveQuotientSign_continuous :
    Continuous (primitiveQuotientSign s hs hs0 v hodd hh0 hv) := by
  have hq : IsQuotientMap (localQuotientMap v (ActualTameKernel.wildKernel v)) :=
    QuotientGroup.isQuotientMap_mk _
  apply hq.continuous_iff.mpr
  exact (continuous_openKernel_character (quadChar s hs hs0)
    (IsOpenKer.isOpen_ker (α := quadChar s hs hs0))).comp (locMap K S v).continuous

include hodd hh0 hv in
/-- Every topological tame inertia generator has the actual primitive sign.
The sign is forced by its dense inertia image and the actual ramified root. -/
theorem frame_primitive_sign (F : TameFrame v (ActualTameKernel.wildKernel v)) :
    quadChar s hs hs0 (locMap K S v F.t) = -1 := by
  let ψ := primitiveQuotientSign s hs hs0 v hodd hh0 hv
  have hψ : Continuous ψ := primitiveQuotientSign_continuous s hs hs0 v hodd hh0 hv
  have hn : quadChar s hs hs0 (locMap K S v F.t) ≠ 1 := by
    intro h1
    have ht : ψ (localQuotientMap v (ActualTameKernel.wildKernel v) F.t) = 1 := h1
    have hz : Subgroup.zpowers (localQuotientMap v (ActualTameKernel.wildKernel v) F.t) ≤ ψ.ker := by
      intro x hx
      obtain ⟨n, rfl⟩ := hx
      change ψ ((localQuotientMap v (ActualTameKernel.wildKernel v) F.t) ^ n) = 1
      rw [map_zpow, ht, one_zpow]
    have hclosed : IsClosed (ψ.ker : Set (LocalQuotient v (ActualTameKernel.wildKernel v))) :=
      isClosed_singleton.preimage hψ
    have hd := (Subgroup.zpowers (localQuotientMap v (ActualTameKernel.wildKernel v) F.t)).topologicalClosure_minimal hz hclosed
    rw [F.dense_inertia] at hd
    have hroot := localSqrt_sq s hs v
    have hroot0 := localSqrt_ne_zero s hs0 v
    obtain ⟨σ, hσI, hσroot⟩ := exists_tame_generator hodd hroot hroot0 hh0
      (congrArg Multiplicative.toAdd hv)
    have hmove : σ (localSqrt s v) = -localSqrt s v := by
      rw [apply_eq_kummerVal_mul hroot0, hσroot.eq_neg_one_of_two_right, neg_one_mul]
    have hsneg : galS K S (locMap K S v σ) s = -s := by
      apply (embS K S v).injective
      exact (embS_locMap K S v σ s).trans (hmove.trans (map_neg (embS K S v) s).symm)
    have hneg : ψ (localQuotientMap v (ActualTameKernel.wildKernel v) σ) = -1 := by
      change quadChar s hs hs0 (locMap K S v σ) = -1
      simp [quadChar, hsneg, neg_ne_self_of_ne_zero s hs0]
    have hmem : localQuotientMap v (ActualTameKernel.wildKernel v) σ ∈
        (inertiaSubgroup (v.adicCompletion K)).map (localQuotientMap v (ActualTameKernel.wildKernel v)).toMonoidHom :=
      ⟨σ, hσI, rfl⟩
    have hone : ψ (localQuotientMap v (ActualTameKernel.wildKernel v) σ) = 1 := hd hmem
    exact (show (-1 : ℤˣ) ≠ 1 from by decide) (hneg.symm.trans hone)
  exact (Int.units_eq_one_or _).resolve_left hn

variable (W : WeierstrassCurve K) [W.IsElliptic]
  [HasFullTwoTorsion K S₀ W] [HasFullTwoTorsion K S W]
  (P : Ideal Lambda) [P.IsPrime] (hS : S₀ ⊆ S)
  (ξ₀ : GKS K S₀ →* Multiplicative ℤ_[2])

include hodd hh0 hv in
/-- The actual old primitive fibre has sign minus one at the prescribed tame
frame generator, with the Tate and inflated moving actions discharged. -/
theorem frame_primitive_fibre_scalar (hv₀ : v ∉ S₀)
    (F : TameFrame v (ActualTameKernel.wildKernel v)) :
    ∀ x : VP K S W P (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom)),
      locMap K S v F.t • x = -x := by
  have hur : urRes K v F.t = 1 := by
    have hI := F.inertia
    change restrictMaximalUnramifiedHom (v.adicCompletion K) F.t = 1
    rw [← ker_restrictMaximalUnramifiedHom] at hI
    exact hI
  have hT : ∀ Q : TateS K S W, locMap K S v F.t • Q = Q := by
    intro Q
    apply (CoefficientComparison.tateEquiv (S₀ := S₀) (S := S) W).injective
    rw [CoefficientComparison.tateEquiv_local_action (S₀ := S₀) (S := S) W v F.t,
      locMap_eq_one_of_urRes_eq_one K S₀ v hv₀ F.t hur, one_smul]
  have hχ := frame_primitive_sign s hs hs0 v hodd hh0 hv F
  have hξ : (ξ₀.comp (inflMap K hS).toMonoidHom) (locMap K S v F.t) = 1 := by
    change ξ₀ (inflMap K hS (locMap K S v F.t)) = 1
    rw [locMap_compat K hS v F.t, locMap_eq_one_of_urRes_eq_one K S₀ v hv₀ F.t hur, map_one]
  intro x
  induction x using VP.induction with
  | zero => rw [smul_zero, neg_zero]
  | tmul c Q =>
    have hz : Multiplicative.toAdd (1 : Multiplicative ℤ_[2]) = 0 := rfl
    rw [VP.smul_tmul, coe_resChar, coe_lambdaChar, hχ, hξ, hz, onePlusTPow_zero,
      mul_one, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, map_neg, map_one,
      neg_one_mul, hT]
    change (-c) ⊗ₜ[ℤ_[2]] Q = -(c ⊗ₜ[ℤ_[2]] Q)
    exact TensorProduct.neg_tmul c Q
  | add x y hx hy => rw [smul_add, hx, hy, neg_add]

end PrimitiveFrameBinding

section PrimitiveAbsolute

open NumberField IsDedekindDomain TauCeti ValuativeRel
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

/-- For actual old primitive primes, the two all-degree comparisons and the
specified tame contraction supply a contraction of the actual full absolute
cochains. Neither a homotopy comparison nor a unit operator is assumed. -/
theorem actual_old_primitive_absolute_contraction
    (h414 : Nekovar414Fibre) (h721 : Nekovar721Structure) (h723 : Nekovar723Fibre)
    {K : Type} [Field K] [NumberField K]
    {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
    (W : WeierstrassCurve K) [W.IsElliptic]
    [HasFullTwoTorsion K S₀ W] [HasFullTwoTorsion K S W]
    (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
    (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
    (ξ₀ : GKS K S₀ →* Multiplicative ℤ_[2])
    [IsContChar (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom))]
    (v : Places K S) (hv₀ : v.1 ∉ S₀)
    (hodd : (2 : ℕ).Coprime (ringChar 𝓀[v.1.adicCompletion K]))
    (hh0 : algebraMap K (v.1.adicCompletion K) h ≠ 0)
    (hv : normalizedValuation (v.1.adicCompletion K)
      (Units.mk0 (algebraMap K (v.1.adicCompletion K) h) hh0) = .ofAdd 1) :
    Nonempty (ZInQ.Contrib.RC53Assist.StrictSymmFull.Contraction
      (absoluteFull W P (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom)) v.1)) := by
  have hneq : ringChar 𝓀[v.1.adicCompletion K] ≠ 2 := by
    intro he
    rw [he] at hodd
    exact (by decide : ¬ (2 : ℕ).Coprime 2) hodd
  have hk := actual_old_primitive_kernel_trivial (S₀ := S₀) (S := S) W s hs hs0 hS P ξ₀ v hv₀ hodd hh0 hv
  have hp := actual_wild_primeToTwo h721 v.1 hneq
  obtain ⟨F⟩ := (h721 K v.1 hneq).2
  have hσ := frame_primitive_fibre_scalar s hs hs0 v.1 hodd hh0 hv
    (S₀ := S₀) W P hS ξ₀ hv₀ F
  have hu := frameUnitTests_of_primitive W P
    (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom)) v F hσ
  exact absolute_contraction_of_frame W P _ v F h414 h723 hneq hu

end PrimitiveAbsolute

section ActualFullCondition

open NumberField IsDedekindDomain
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

/-- A specified contraction of an ambient complex gives the same contraction
of its full subcomplex, with the retained subtype inclusion. -/
def fullSubContraction {k : Type} [Field k] {L : GCx k}
    (C : ZInQ.Contrib.RC53Assist.StrictSymmFull.Contraction L) :
    ZInQ.Contrib.RC53Assist.StrictSymmFull.Contraction (SubFam.top L).cx where
  h i j hij := (C.h i j hij).domRestrict ⊤ |>.codRestrict ⊤ (fun _ => Submodule.mem_top)
  identity i j l hj hl x := Subtype.ext (C.identity i j l hj hl x.1)

/-- The primitive contraction is for the genuine retained full local condition,
not just for an independently chosen cochain or tame-model object. -/
theorem actual_old_primitive_full_condition_contraction
    (h414 : Nekovar414Fibre) (h721 : Nekovar721Structure) (h723 : Nekovar723Fibre)
    {K : Type} [Field K] [NumberField K]
    {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
    (W : WeierstrassCurve K) [W.IsElliptic]
    [HasFullTwoTorsion K S₀ W] [HasFullTwoTorsion K S W]
    (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
    (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
    (ξ₀ : GKS K S₀ →* Multiplicative ℤ_[2])
    [IsContChar (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom))]
    (v : Places K S) (hv₀ : v.1 ∉ S₀)
    (hodd : (2 : ℕ).Coprime (ringChar 𝓀[v.1.adicCompletion K]))
    (hh0 : algebraMap K (v.1.adicCompletion K) h ≠ 0)
    (hv : normalizedValuation (v.1.adicCompletion K)
      (Units.mk0 (algebraMap K (v.1.adicCompletion K) h) hh0) = .ofAdd 1) :
    Nonempty (ZInQ.Contrib.RC53Assist.StrictSymmFull.Contraction
      (SubFam.top (localCx (ResAt P) (GKS K S) (fun w : Places K S => Gloc K w.1)
        (fun w => locMap K S w.1)
        (VP K S W P (lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom))) v)).cx) := by
  obtain ⟨C⟩ := actual_old_primitive_absolute_contraction h414 h721 h723 hS W P s hs hs0 ξ₀ v hv₀ hodd hh0 hv
  exact ⟨fullSubContraction C⟩

end ActualFullCondition

end ZInQ.Contrib.RC53Assist.StrictSymmFull.RetainedInflation

namespace ZInQ.Contrib.RC53Assist.StrictSymmFull.ContinuousReduction

open CategoryTheory CategoryTheory.Limits
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.RC53Assist.StrictLocal

open ZInQ.Contrib.RC53Assist.StrictSymmFull

section ActualContinuousSwitch

variable {k GS V : Type} [Field k] [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  [DecidableEq V] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]

/-- The contraction license for the actual retained full continuous conditions.
No topology, module or strict-symmetry hypothesis is replaced. -/
structure RetainedReduction (q : V) (old : ∀ v, SubFam (localCx k GS Gv loc M v)) (E : Set V) where
  new_retained : q ∉ E
  full : ∀ v, v ∈ E → old v = SubFam.top (localCx k GS Gv loc M v)
  contraction : ∀ v, v ∈ E → Contraction (old v).cx
  bounded : ∀ v, v ≠ q → v ∉ E → DegreeTwoZero (old v).cx

variable (q : V) (old : ∀ v, SubFam (localCx k GS Gv loc M v)) (E : Set V)
  (side : ∀ v, Set (Gv v))

omit [IsTopologicalGroup GS] in
/-- The generic retained strict switch commutes with precisely the licensed erasure. -/
theorem erase_strict (hq : q ∉ E) :
    eraseFull E (switchStrK k Gv (fun v => ResMod (loc v) M) q old) =
      switchStrK k Gv (fun v => ResMod (loc v) M) q (eraseFull E old) := by
  funext v
  by_cases hv : v = q
  · subst v
    simp only [eraseFull, switchStrK, ite_eq_right hq]
  · simp only [eraseFull, switchStrK, ite_eq_right hv]

omit [IsTopologicalGroup GS] in
/-- The relaxed switch uses the same licensed erasure and retained map. -/
theorem erase_relaxed (hq : q ∉ E) :
    eraseFull E (switchRelK k Gv (fun v => ResMod (loc v) M) q old) =
      switchRelK k Gv (fun v => ResMod (loc v) M) q (eraseFull E old) := by
  funext v
  by_cases hv : v = q
  · subst v
    simp only [eraseFull, switchRelK, ite_eq_right hq]
  · simp only [eraseFull, switchRelK, ite_eq_right hv]

/-- The prescribed strict comparison is the actual subtype inclusion. -/
def strictComparison (hq : q ∉ E) (v : V) :
    GHom ((continuousSwitch q (eraseFull E old) side).str v).cx
      ((continuousSwitch q old side).str v).cx :=
  SubFam.inclLe (by
    intro n
    change (switchStrK k Gv (fun v => ResMod (loc v) M) q (eraseFull E old) v).S n ≤
      (switchStrK k Gv (fun v => ResMod (loc v) M) q old v).S n
    rw [← erase_strict q old E hq]
    unfold eraseFull
    split_ifs
    · exact bot_le
    · exact le_rfl)

/-- The prescribed relaxed comparison retains the same subtype inclusion. -/
def relaxedComparison (hq : q ∉ E) (v : V) :
    GHom ((continuousSwitch q (eraseFull E old) side).rel v).cx
      ((continuousSwitch q old side).rel v).cx :=
  SubFam.inclLe (by
    intro n
    change (switchRelK k Gv (fun v => ResMod (loc v) M) q (eraseFull E old) v).S n ≤
      (switchRelK k Gv (fun v => ResMod (loc v) M) q old v).S n
    rw [← erase_relaxed q old E hq]
    unfold eraseFull
    split_ifs
    · exact bot_le
    · exact le_rfl)

omit [IsTopologicalGroup GS] in
/-- The actual reduced strict complex has a literally zero degree-two term. -/
theorem reduced_degreeTwoZero (R : RetainedReduction q old E) :
    DegreeTwoZero (continuousSwitch q (eraseFull E old) side).Ustr := by
  apply (switch_degreeTwoZero_iff Gv (fun v => ResMod (loc v) M) q (eraseFull E old) side).mpr
  intro v hvq
  by_cases hv : v ∈ E
  · change DegreeTwoZero (eraseFull E old v).cx
    rw [eraseFull, ite_eq_left hv]
    intro x
    exact Subtype.ext ((Submodule.mem_bot k).mp x.2)
  · simpa only [eraseFull, ite_eq_right hv] using R.bounded v hvq hv

variable {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction GS T] [SMulCommClass GS k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul GS T]
  (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GS) (x y : M), β (g • x) (g • y) = g • β x y)
  (hβc : Continuous fun x : M × M => β x.1 x.2)

/-- Pull back the original genuine isotropy datum through the specified
comparisons, retaining all bidegrees of the original homotopy. -/
def reducedIsotropy (hq : q ∉ E) (I : ContinuousIsotropy q old side β hβ hβc) :
    ContinuousIsotropy q (eraseFull E old) side β hβ hβc where
  h v i j l hij := (I.h v i j l hij).compl₁₂
    ((strictComparison q old E side hq v).f i i rfl)
    ((relaxedComparison q old E side hq v).f j j rfl)
  isotropy₂ v i i₁ j j₁ hh hi hj x y := by
    let a := strictComparison q old E side hq v
    let b := relaxedComparison q old E side hq v
    have he := I.isotropy₂ v i i₁ j j₁ hh hi hj (a.f i i rfl x) (b.f j j rfl y)
    dsimp only [continuousConditions] at he ⊢
    erw [← a.comm i i₁ i i₁ rfl hi hi rfl x, ← b.comm j j₁ j j₁ rfl hj hj rfl y] at he
    exact he
  isotropy₃ v i i₁ j j₁ l l₁ hh hi hj hl h3 x y := by
    let a := strictComparison q old E side hq v
    let b := relaxedComparison q old E side hq v
    have he := I.isotropy₃ v i i₁ j j₁ l l₁ hh hi hj hl h3 (a.f i i rfl x) (b.f j j rfl y)
    dsimp only [continuousConditions] at he ⊢
    erw [← a.comm i i₁ i i₁ rfl hi hi rfl x, ← b.comm j j₁ j j₁ rfl hj hj rfl y] at he
    exact he

omit [IsTopologicalGroup GS] in
/-- The homotopy is retained exactly, not replaced by a newly chosen isotropy. -/
theorem reducedIsotropy_formula (hq : q ∉ E) (I : ContinuousIsotropy q old side β hβ hβc)
    (v : V) (i j l : ℤ) (hij : i + j = l + 1)
    (x : ((continuousSwitch q (eraseFull E old) side).str v).cx.X i)
    (y : ((continuousSwitch q (eraseFull E old) side).rel v).cx.X j) :
    (reducedIsotropy q old E side β hβ hβc hq I).h v i j l hij x y =
      I.h v i j l hij ((strictComparison q old E side hq v).f i i rfl x)
        ((relaxedComparison q old E side hq v).f j j rfl y) := rfl

/-- Both original Hsw symmetry conventions hold for the actual reduced switch
with lattice-topologized coefficients and the retained genuine isotropy datum. -/
theorem reduced_strictSymmetry (R : RetainedReduction q old E)
    (I : ContinuousIsotropy q old side β hβ hβc) (c : k) (hc : ∀ x y : M, β x y = c • β y x) :
    let X' := continuousSwitch q (eraseFull E old) side
    let I' := reducedIsotropy q old E side β hβ hβc R.new_retained I
    let Q' := continuousPairData q (eraseFull E old) side β hβ hβc I'
    let Cd := ZInQ.Contrib.CloudB3RC53.Hsw.localPairCupOneGen GS Gv loc β hβ hβc c hc
    ZInQ.Contrib.CloudB3RC53.Hsw.StrictSymmTrunc
      (continuousRelaxedData q (eraseFull E old) side) X'.Ustr X'.fr Q' Cd ∧
    ZInQ.Contrib.CloudB3RC53.Hsw.StrictSymm
      (continuousRelaxedData q (eraseFull E old) side) X'.Ustr X'.fr Q'.toSelPairData Cd.trunc := by
  dsimp only
  exact strictSymmTrunc_of_degreeTwoZero
    (continuousRelaxedData q (eraseFull E old) side)
    (continuousSwitch q (eraseFull E old) side).Ustr
    (continuousSwitch q (eraseFull E old) side).fr _ _ (reduced_degreeTwoZero q old E side R)

omit [IsTopologicalGroup GS] in
/-- The original RC26 place-wise strict-symmetry formula also holds on the
actual reduced continuous data, without invoking a discrete coefficient wrapper. -/
theorem reduced_rc26_strictSymm (R : RetainedReduction q old E)
    (I : ContinuousIsotropy q old side β hβ hβc) (c : k) :
    let X' := continuousSwitch q (eraseFull E old) side
    let I' := reducedIsotropy q old E side β hβ hβc R.new_retained I
    ∀ (v : V) (s₂ : (X'.str v).cx.X 2) (t₁ : (X'.str v).cx.X 1),
      continuousForward q (eraseFull E old) side β hβ hβc I' v 2 1 2 rfl s₂
        ((continuousLocalInclusion q (eraseFull E old) side v).f 1 1 rfl t₁) -
        c • continuousForward q (eraseFull E old) side β hβ hβc I' v 1 2 2 rfl t₁
          ((continuousLocalInclusion q (eraseFull E old) side v).f 2 2 rfl s₂) -
        localCupOne21 k GS Gv loc β hβc v
          ((X'.rel v).incl.f 2 2 rfl ((continuousLocalInclusion q (eraseFull E old) side v).f 2 2 rfl s₂))
          ((X'.rel v).incl.f 1 1 rfl ((continuousLocalInclusion q (eraseFull E old) side v).f 1 1 rfl t₁)) ∈
        LinearMap.range ((localCx k GS Gv loc T v).d 1 2 rfl) := by
  dsimp only
  intro v s₂ t₁
  have hzero : DegreeTwoZero ((continuousSwitch q (eraseFull E old) side).str v).cx :=
    (degreeTwoZero_pi_iff _).mp (reduced_degreeTwoZero q old E side R) v
  rw [hzero s₂]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, sub_zero]
  exact Submodule.zero_mem (LinearMap.range ((localCx k GS Gv loc T v).d 1 2 rfl))

/-- The actual retained local inclusions commute with the prescribed reduction
maps, without changing the global or ambient local terms. -/
theorem retained_condition_maps (hq : q ∉ E) (i j : ℤ) (hij : i = j) :
    (∀ x : (continuousStrictData q (eraseFull E old) side).U.X i,
      (continuousStrictData q (eraseFull E old) side).ι.f i j hij x =
        (continuousStrictData q old side).ι.f i j hij
          ((piMap (strictComparison q old E side hq)).f i i rfl x)) ∧
    (∀ x : (continuousRelaxedData q (eraseFull E old) side).U.X i,
      (continuousRelaxedData q (eraseFull E old) side).ι.f i j hij x =
        (continuousRelaxedData q old side).ι.f i j hij
          ((piMap (relaxedComparison q old E side hq)).f i i rfl x)) := by
  subst hij
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- The strict Selmer comparison retains the actual global and ambient local
cochains, and changes only the licensed condition component. -/
def strictSelmerComparison (hq : q ∉ E) :
    GHom (selCx (continuousStrictData q (eraseFull E old) side))
      (selCx (continuousStrictData q old side)) where
  f i j hij := by
    subst hij
    exact (changeMap (continuousStrictData q old side)
      (piMap (strictComparison q old E side hq))).f i i rfl
  comm i i₁ j j₁ hij hi hj h₁ x := by
    subst hij h₁
    obtain ⟨a, u, y⟩ := x
    refine Prod.ext rfl (Prod.ext
      ((piMap (strictComparison q old E side hq)).comm i i₁ i i₁ rfl hi hj rfl u) ?_)
    change (continuousStrictData q (eraseFull E old) side).res.f i (i₁ - 1) (by omega) a -
        (continuousStrictData q (eraseFull E old) side).ι.f i (i₁ - 1) (by omega) u -
        (continuousStrictData q (eraseFull E old) side).L.d (i - 1) (i₁ - 1) (by omega) y =
      (continuousStrictData q old side).res.f i (i₁ - 1) (by omega) a -
        (continuousStrictData q old side).ι.f i (i₁ - 1) (by omega)
          ((piMap (strictComparison q old E side hq)).f i i rfl u) -
        (continuousStrictData q old side).L.d (i - 1) (i₁ - 1) (by omega) y
    rw [(retained_condition_maps q old E side hq i (i₁ - 1) (by omega)).1 u]
    rfl

/-- The relaxed Selmer comparison retains precisely the same global and local terms. -/
def relaxedSelmerComparison (hq : q ∉ E) :
    GHom (selCx (continuousRelaxedData q (eraseFull E old) side))
      (selCx (continuousRelaxedData q old side)) where
  f i j hij := by
    subst hij
    exact (changeMap (continuousRelaxedData q old side)
      (piMap (relaxedComparison q old E side hq))).f i i rfl
  comm i i₁ j j₁ hij hi hj h₁ x := by
    subst hij h₁
    obtain ⟨a, u, y⟩ := x
    refine Prod.ext rfl (Prod.ext
      ((piMap (relaxedComparison q old E side hq)).comm i i₁ i i₁ rfl hi hj rfl u) ?_)
    change (continuousRelaxedData q (eraseFull E old) side).res.f i (i₁ - 1) (by omega) a -
        (continuousRelaxedData q (eraseFull E old) side).ι.f i (i₁ - 1) (by omega) u -
        (continuousRelaxedData q (eraseFull E old) side).L.d (i - 1) (i₁ - 1) (by omega) y =
      (continuousRelaxedData q old side).res.f i (i₁ - 1) (by omega) a -
        (continuousRelaxedData q old side).ι.f i (i₁ - 1) (by omega)
          ((piMap (relaxedComparison q old E side hq)).f i i rfl u) -
        (continuousRelaxedData q old side).L.d (i - 1) (i₁ - 1) (by omega) y
    rw [(retained_condition_maps q old E side hq i (i₁ - 1) (by omega)).2 u]
    rfl

/-- Every trace of the original genuine cup formula is preserved on the
specified forward comparison, including its retained isotropy homotopy. -/
theorem retained_traced_pairing (hq : q ∉ E) (I : ContinuousIsotropy q old side β hβ hβc)
    (tr : (coneCx (continuousPairData q old side β hβ hβc I).resE).X 3 →ₗ[k] k)
    (i j : ℤ) (hij : i + j = 3)
    (x : (selCx (continuousStrictData q (eraseFull E old) side)).X i)
    (y : (selCx (continuousRelaxedData q (eraseFull E old) side)).X j) :
    tr (selCupFunT (continuousPairData q (eraseFull E old) side β hβ hβc
        (reducedIsotropy q old E side β hβ hβc hq I)) i j 3 hij x y) =
      tr (selCupFunT (continuousPairData q old side β hβ hβc I) i j 3 hij
        ((strictSelmerComparison q old E side hq).f i i rfl x)
        ((relaxedSelmerComparison q old E side hq).f j j rfl y)) := rfl

omit [IsTopologicalGroup GS] in
/-- The full-condition contractions produce deformation retracts of the
actual strict and relaxed condition complexes, with their prescribed inclusions. -/
theorem condition_retractions (R : RetainedReduction q old E) :
    (∃ C : ConditionRetraction (continuousSwitch q (eraseFull E old) side).Ustr
        (continuousSwitch q old side).Ustr,
      C.inc = piMap (strictComparison q old E side R.new_retained)) ∧
    (∃ C : ConditionRetraction (continuousSwitch q (eraseFull E old) side).Urel
        (continuousSwitch q old side).Urel,
      C.inc = piMap (relaxedComparison q old E side R.new_retained)) := by
  constructor
  · apply erasureRetraction_prescribed E _ _ (erase_strict q old E R.new_retained).symm
      (strictComparison q old E side R.new_retained) (fun _ _ _ => rfl)
    intro v hv
    have hvq : v ≠ q := by
      intro he
      subst v
      exact R.new_retained hv
    change Contraction (switchStrK k Gv (fun v => ResMod (loc v) M) q old v).cx
    rw [switchStr_neK q old hvq]
    exact R.contraction v hv
  · apply erasureRetraction_prescribed E _ _ (erase_relaxed q old E R.new_retained).symm
      (relaxedComparison q old E side R.new_retained) (fun _ _ _ => rfl)
    intro v hv
    have hvq : v ≠ q := by
      intro he
      subst v
      exact R.new_retained hv
    change Contraction (switchRelK k Gv (fun v => ResMod (loc v) M) q old v).cx
    rw [switchRel_neK q old hvq]
    exact R.contraction v hv

/-- Licensed erasure gives actual strict and relaxed Selmer homotopy inverses.
The retraction used for these inverses includes the local correction term. -/
theorem selmer_retractions (R : RetainedReduction q old E) :
    (∃ C : ConditionRetraction (continuousSwitch q (eraseFull E old) side).Ustr
        (continuousStrictData q old side).U,
      C.inc = piMap (strictComparison q old E side R.new_retained) ∧
      Nonempty (HomotopyEquiv
        (selCx (restrictData (continuousStrictData q old side) C.inc)).toCC
        (selCx (continuousStrictData q old side)).toCC)) ∧
    (∃ C : ConditionRetraction (continuousSwitch q (eraseFull E old) side).Urel
        (continuousRelaxedData q old side).U,
      C.inc = piMap (relaxedComparison q old E side R.new_retained) ∧
      Nonempty (HomotopyEquiv
        (selCx (restrictData (continuousRelaxedData q old side) C.inc)).toCC
        (selCx (continuousRelaxedData q old side)).toCC)) := by
  obtain ⟨⟨Cs, hs⟩, ⟨Cr, hr⟩⟩ := condition_retractions q old E side R
  exact ⟨⟨Cs, hs, ⟨selmerRetractionEquiv (continuousStrictData q old side) Cs⟩⟩,
    ⟨Cr, hr, ⟨selmerRetractionEquiv (continuousRelaxedData q old side) Cr⟩⟩⟩

/-- The reduced actual Selmer data are restriction along the specified strict
and relaxed condition inclusions, not a different local-data package. -/
theorem reduced_data_eq (hq : q ∉ E) :
    continuousStrictData q (eraseFull E old) side =
      restrictData (continuousStrictData q old side) (piMap (strictComparison q old E side hq)) ∧
    continuousRelaxedData q (eraseFull E old) side =
      restrictData (continuousRelaxedData q old side) (piMap (relaxedComparison q old E side hq)) := by
  constructor
  · have hi : (continuousStrictData q (eraseFull E old) side).ι =
        ghomComp (piMap (strictComparison q old E side hq)) (continuousStrictData q old side).ι :=
      ghom_ext fun n x => (retained_condition_maps q old E side hq n n rfl).1 x
    exact congrArg (fun a : GHom (continuousStrictData q (eraseFull E old) side).U
        (continuousStrictData q old side).L =>
      (⟨(continuousStrictData q old side).G,
        (continuousStrictData q (eraseFull E old) side).U,
        (continuousStrictData q old side).L, (continuousStrictData q old side).res, a⟩ : SelData k)) hi
  · have hi : (continuousRelaxedData q (eraseFull E old) side).ι =
        ghomComp (piMap (relaxedComparison q old E side hq)) (continuousRelaxedData q old side).ι :=
      ghom_ext fun n x => (retained_condition_maps q old E side hq n n rfl).2 x
    exact congrArg (fun a : GHom (continuousRelaxedData q (eraseFull E old) side).U
        (continuousRelaxedData q old side).L =>
      (⟨(continuousRelaxedData q old side).G,
        (continuousRelaxedData q (eraseFull E old) side).U,
        (continuousRelaxedData q old side).L, (continuousRelaxedData q old side).res, a⟩ : SelData k)) hi

/-- The licensed contractions yield homotopy equivalences of the actual reduced
and original Selmer complexes on the retained continuous coefficients. -/
theorem actual_selmer_equivalences (R : RetainedReduction q old E) :
    Nonempty (HomotopyEquiv
      (selCx (continuousStrictData q (eraseFull E old) side)).toCC
      (selCx (continuousStrictData q old side)).toCC) ∧
    Nonempty (HomotopyEquiv
      (selCx (continuousRelaxedData q (eraseFull E old) side)).toCC
      (selCx (continuousRelaxedData q old side)).toCC) := by
  obtain ⟨⟨Cs, hs, ⟨es⟩⟩, ⟨Cr, hr, ⟨er⟩⟩⟩ := selmer_retractions q old E side R
  have hDs := (reduced_data_eq q old E side R.new_retained).1
  have hDr := (reduced_data_eq q old E side R.new_retained).2
  rw [hs, ← hDs] at es
  rw [hr, ← hDr] at er
  exact ⟨⟨es⟩, ⟨er⟩⟩

end ActualContinuousSwitch

end ZInQ.Contrib.RC53Assist.StrictSymmFull.ContinuousReduction

namespace ZInQ.Contrib.RC53Assist.StrictSymmFull.ActualSwitchAssembly

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain TauCeti ValuativeRel
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Contrib.RC53Assist.StrictLocal
  ZInQ.Contrib.RC53Assist.StrictSymmFull
  ZInQ.Contrib.RC53Assist.StrictSymmFull.RetainedInflation
  ZInQ.Contrib.RC53Assist.StrictSymmFull.ContinuousReduction
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] [HasFullTwoTorsion K S₀ W] [HasFullTwoTorsion K S W]
  (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
  (s : KS K S) {h : K} (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
  (ξ₀ : GKS K S₀ →* Multiplicative ℤ_[2])

local instance placesDecidable : DecidableEq (Places K S) := Classical.decEq _

/-- The actual height-one primitive coefficient character of the switch. -/
abbrev coefficientCharacter : GKS K S →* Lambdaˣ :=
  lambdaChar (quadChar s hs hs0) (ξ₀.comp (inflMap K hS).toMonoidHom)

/-- Exactly the actual old-prime conditions discharged by the primitive contraction. -/
structure PrimitivePlace (v : Places K S) : Prop where
  outside : v.1 ∉ S₀
  odd : (2 : ℕ).Coprime (ringChar 𝓀[v.1.adicCompletion K])
  radicand_nonzero : algebraMap K (v.1.adicCompletion K) h ≠ 0
  uniformizer : normalizedValuation (v.1.adicCompletion K)
    (Units.mk0 (algebraMap K (v.1.adicCompletion K) h) radicand_nonzero) = .ofAdd 1

variable [IsContChar (coefficientCharacter hS s hs hs0 ξ₀)]

/-- A remaining nonprimitive full place needs its actual tame frame and displayed
unit tests, not a strict-symmetry or full-cochain contraction premise. -/
structure OtherPlaceInputs (v : Places K S) where
  odd : ringChar 𝓀[v.1.adicCompletion K] ≠ 2
  kernel : KernelActsTrivially W P (coefficientCharacter hS s hs hs0 ξ₀)
    v.1 (ActualTameKernel.wildKernel v.1)
  frame : TameFrame v.1 (ActualTameKernel.wildKernel v.1)
  units :
    let _ : KernelActsTrivially W P (coefficientCharacter hS s hs hs0 ξ₀) v.1
        (ActualTameKernel.wildKernel v.1) := kernel
    FrameUnitTests W P (coefficientCharacter hS s hs hs0 ξ₀) v frame

omit [HasFullTwoTorsion K S₀ W] in
/-- The remaining arithmetic tests also yield the actual retained full-cochain
contraction by the specified comparisons, with no circular symmetry premise. -/
theorem other_place_contraction (h414 : Nekovar414Fibre) (h721 : Nekovar721Structure)
    (h723 : Nekovar723Fibre) (v : Places K S)
    (O : OtherPlaceInputs hS W P s hs hs0 ξ₀ v) :
    Nonempty (Contraction (SubFam.top (localCx (ResAt P) (GKS K S)
      (fun w : Places K S => Gloc K w.1) (fun w => locMap K S w.1)
      (VP K S W P (coefficientCharacter hS s hs hs0 ξ₀)) v)).cx) := by
  have hk := O.kernel
  have hp := actual_wild_primeToTwo h721 v.1 O.odd
  obtain ⟨C⟩ := absolute_contraction_of_frame W P (coefficientCharacter hS s hs hs0 ξ₀) v O.frame
    h414 h723 O.odd O.units
  exact ⟨fullSubContraction C⟩

variable (q : Places K S)
  (old : ∀ v, SubFam (localCx (ResAt P) (GKS K S) (fun w : Places K S => Gloc K w.1)
    (fun w => locMap K S w.1) (VP K S W P (coefficientCharacter hS s hs hs0 ξ₀)) v))
  (E Eprim : Set (Places K S))

/-- Assemble the contraction license from the actual primitive-prime theorem
and the precise remaining nonprimitive tame unit tests. The given full
conditions and all nonremoved local conditions are retained literally. -/
def actualRetainedReduction
    (h414 : Nekovar414Fibre) (h721 : Nekovar721Structure) (h723 : Nekovar723Fibre)
    (hq : q ∉ E)
    (hfull : ∀ v, v ∈ E → old v = SubFam.top (localCx (ResAt P) (GKS K S)
      (fun w : Places K S => Gloc K w.1) (fun w => locMap K S w.1)
      (VP K S W P (coefficientCharacter hS s hs hs0 ξ₀)) v))
    (hprim : ∀ v, v ∈ Eprim → PrimitivePlace (S₀ := S₀) (h := h) v)
    (hother : ∀ v, v ∈ E → v ∉ Eprim → OtherPlaceInputs hS W P s hs hs0 ξ₀ v)
    (hbounded : ∀ v, v ≠ q → v ∉ E → DegreeTwoZero (old v).cx) :
    RetainedReduction q old E where
  new_retained := hq
  full := hfull
  contraction v hv := by
    classical
    rw [hfull v hv]
    by_cases hpr : v ∈ Eprim
    · let A := hprim v hpr
      exact Classical.choice (actual_old_primitive_full_condition_contraction h414 h721 h723 hS W P
        s hs hs0 ξ₀ v A.outside A.odd A.radicand_nonzero A.uniformizer)
    · exact Classical.choice (other_place_contraction hS W P s hs hs0 ξ₀ h414 h721 h723 v (hother v hv hpr))
  bounded := hbounded

variable (side : ∀ v : Places K S, Set (Gloc K v.1))
  {T : Type} [AddCommGroup T] [Module (ResAt P) T] [TopologicalSpace T] [ContinuousAdd T]
  [ContinuousConstSMul (ResAt P) T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) (ResAt P) T] [ContinuousSMul (GKS K S) T]
  (β : VP K S W P (coefficientCharacter hS s hs hs0 ξ₀) →ₗ[ResAt P]
    VP K S W P (coefficientCharacter hS s hs hs0 ξ₀) →ₗ[ResAt P] T)
  (hβ : ∀ (g : GKS K S) (x y : VP K S W P (coefficientCharacter hS s hs hs0 ξ₀)),
    β (g • x) (g • y) = g • β x y)
  (hβc : Continuous fun x : VP K S W P (coefficientCharacter hS s hs hs0 ξ₀) ×
      VP K S W P (coefficientCharacter hS s hs hs0 ξ₀) => β x.1 x.2)

/-- Route B for the actual height-one switch: the supplied arithmetic tests
produce the contraction license, and its reduced genuine isotropy satisfies
both strict-symmetry conventions on the unchanged lattice coefficient topology. -/
theorem actual_reduced_switch_symmetry
    (h414 : Nekovar414Fibre) (h721 : Nekovar721Structure) (h723 : Nekovar723Fibre)
    (hq : q ∉ E)
    (hfull : ∀ v, v ∈ E → old v = SubFam.top (localCx (ResAt P) (GKS K S)
      (fun w : Places K S => Gloc K w.1) (fun w => locMap K S w.1)
      (VP K S W P (coefficientCharacter hS s hs hs0 ξ₀)) v))
    (hprim : ∀ v, v ∈ Eprim → PrimitivePlace (S₀ := S₀) (h := h) v)
    (hother : ∀ v, v ∈ E → v ∉ Eprim → OtherPlaceInputs hS W P s hs hs0 ξ₀ v)
    (hbounded : ∀ v, v ≠ q → v ∉ E → DegreeTwoZero (old v).cx)
    (I : ContinuousIsotropy q old side β hβ hβc) (c : ResAt P)
    (hc : ∀ x y, β x y = c • β y x) :
    ∃ R : RetainedReduction q old E,
      let X' := continuousSwitch q (eraseFull E old) side
      let I' := ContinuousReduction.reducedIsotropy q old E side β hβ hβc R.new_retained I
      let Q' := continuousPairData q (eraseFull E old) side β hβ hβc I'
      let Cd := ZInQ.Contrib.CloudB3RC53.Hsw.localPairCupOneGen (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc c hc
      ZInQ.Contrib.CloudB3RC53.Hsw.StrictSymmTrunc
        (continuousRelaxedData q (eraseFull E old) side) X'.Ustr X'.fr Q' Cd ∧
      ZInQ.Contrib.CloudB3RC53.Hsw.StrictSymm
        (continuousRelaxedData q (eraseFull E old) side) X'.Ustr X'.fr Q'.toSelPairData Cd.trunc := by
  let R := actualRetainedReduction hS W P s hs hs0 ξ₀ q old E Eprim h414 h721 h723 hq hfull hprim hother hbounded
  exact ⟨R, ContinuousReduction.reduced_strictSymmetry q old E side β hβ hβc R I c hc⟩

/-- The RC26 place-wise formula is assembled for the same actual reduced
switch and the same contraction license, on the retained coefficient topology. -/
theorem actual_reduced_switch_rc26
    (h414 : Nekovar414Fibre) (h721 : Nekovar721Structure) (h723 : Nekovar723Fibre)
    (hq : q ∉ E)
    (hfull : ∀ v, v ∈ E → old v = SubFam.top (localCx (ResAt P) (GKS K S)
      (fun w : Places K S => Gloc K w.1) (fun w => locMap K S w.1)
      (VP K S W P (coefficientCharacter hS s hs hs0 ξ₀)) v))
    (hprim : ∀ v, v ∈ Eprim → PrimitivePlace (S₀ := S₀) (h := h) v)
    (hother : ∀ v, v ∈ E → v ∉ Eprim → OtherPlaceInputs hS W P s hs hs0 ξ₀ v)
    (hbounded : ∀ v, v ≠ q → v ∉ E → DegreeTwoZero (old v).cx)
    (I : ContinuousIsotropy q old side β hβ hβc) (c : ResAt P) :
    ∃ R : RetainedReduction q old E,
      let X' := continuousSwitch q (eraseFull E old) side
      let I' := ContinuousReduction.reducedIsotropy q old E side β hβ hβc R.new_retained I
      ∀ (v : Places K S) (s₂ : (X'.str v).cx.X 2) (t₁ : (X'.str v).cx.X 1),
        continuousForward q (eraseFull E old) side β hβ hβc I' v 2 1 2 rfl s₂
          ((continuousLocalInclusion q (eraseFull E old) side v).f 1 1 rfl t₁) -
          c • continuousForward q (eraseFull E old) side β hβ hβc I' v 1 2 2 rfl t₁
            ((continuousLocalInclusion q (eraseFull E old) side v).f 2 2 rfl s₂) -
          localCupOne21 (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) β hβc v
            ((X'.rel v).incl.f 2 2 rfl ((continuousLocalInclusion q (eraseFull E old) side v).f 2 2 rfl s₂))
            ((X'.rel v).incl.f 1 1 rfl ((continuousLocalInclusion q (eraseFull E old) side v).f 1 1 rfl t₁)) ∈
          LinearMap.range ((localCx (ResAt P) (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) T v).d 1 2 rfl) := by
  let R := actualRetainedReduction hS W P s hs hs0 ξ₀ q old E Eprim h414 h721 h723 hq hfull hprim hother hbounded
  exact ⟨R, ContinuousReduction.reduced_rc26_strictSymm q old E side β hβ hβc R I c⟩

end ZInQ.Contrib.RC53Assist.StrictSymmFull.ActualSwitchAssembly
