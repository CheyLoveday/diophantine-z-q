import ZInQKernel.Contrib.RC53Assist.CalibrationModel.IntegralReplacement
import ZInQKernel.Contrib.RC53Assist.Finiteness.GaloisFiniteness
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dual.Lemmas
import ZInQKernel.Contrib.RC53Assist.CentralUniversal.Arithmetic

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.CalibrationShape

/-!
# Integral cochains and canonical central coefficient reduction

The coefficient projection is compared with tensor reduction before taking
cohomology.  The local Kummer condition is retained, including its degree-zero
term and finite torsion.
-/

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.Finiteness
open scoped TensorProduct

section TensorReduction

variable {R A X Y : Type} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup X] [Module R X] [AddCommGroup Y]
  (n : R) (q : X →+ Y) (hq : Function.Surjective q)
  (hker : ∀ x, q x = 0 → ∃ z, x = n • z)
  (hA : algebraMap R A n = 0)

/-- A residue class determines its unit tensor independently of the lift. -/
def residueTensorLift : Y →+ A ⊗[R] X :=
  (QuotientAddGroup.lift q.ker (TensorProduct.mk R A X 1).toAddMonoidHom (by
    intro x hx
    obtain ⟨z, rfl⟩ := hker x hx
    change (1 : A) ⊗ₜ[R] (n • z) = 0
    rw [← TensorProduct.smul_tmul, ← algebraMap_smul A n (1 : A), hA,
      zero_smul, TensorProduct.zero_tmul])).comp
      (QuotientAddGroup.quotientKerEquivOfSurjective q hq).symm.toAddMonoidHom

/-- The unit tensor of a lifted residue is the original unit tensor. -/
theorem residueTensorLift_apply (x : X) :
    residueTensorLift n q hq hker hA (q x) = (1 : A) ⊗ₜ[R] x := by
  dsimp only [residueTensorLift, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  have he : (QuotientAddGroup.quotientKerEquivOfSurjective q hq).symm (q x) =
      QuotientAddGroup.mk x := by
    apply (QuotientAddGroup.quotientKerEquivOfSurjective q hq).injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [he]
  rfl

/-- Extending the residue lift in the coefficient factor. -/
def residueTensorInverse : A ⊗[ℤ] Y →+ A ⊗[R] X :=
  TensorProduct.liftAddHom
    { toFun := fun a => a • residueTensorLift n q hq hker hA
      map_zero' := by ext y; simp
      map_add' := by intro a b; ext y; simp [add_smul] }
    (by
      intro r a y
      change (r • a) • residueTensorLift n q hq hker hA y =
        a • residueTensorLift n q hq hker hA (r • y)
      rw [map_zsmul, smul_assoc, smul_comm r a])

/-- The extended inverse on a tensor of a projected element. -/
theorem residueTensorInverse_tmul (a : A) (x : X) :
    residueTensorInverse n q hq hker hA (a ⊗ₜ[ℤ] q x) = a ⊗ₜ[R] x := by
  rw [residueTensorInverse, TensorProduct.liftAddHom_tmul]
  change a • residueTensorLift n q hq hker hA (q x) = _
  rw [residueTensorLift_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

include n hq hker hA in
/-- A coefficient comparison with the displayed projection formula is bijective. -/
theorem tensorReduction_bijective
    (F : A ⊗[R] X →ₗ[A] A ⊗[ℤ] Y)
    (hF : ∀ a x, F (a ⊗ₜ[R] x) = a ⊗ₜ[ℤ] q x) :
    Function.Bijective F := by
  let J := residueTensorInverse n q hq hker hA
  have hJF : ∀ z, J (F z) = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x => rw [hF]; exact residueTensorInverse_tmul n q hq hker hA a x
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hFJ : ∀ z, F (J z) = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a y =>
      obtain ⟨x, rfl⟩ := hq y
      rw [residueTensorInverse_tmul, hF]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact ⟨fun x y h => (hJF x).symm.trans ((congrArg J h).trans (hJF y)),
    fun z => ⟨J z, hFJ z⟩⟩

end TensorReduction

section ContinuousReduction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {T : Type} [AddCommGroup T] [Module ℤ_[2] T]
  [DistribMulAction G T] [SMulCommClass G ℤ_[2] T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul ℤ_[2] T] [ContinuousSMul G T]
  {L : ℕ → Type} [∀ k, AddCommGroup (L k)] [∀ k, DistribMulAction G (L k)]
  [∀ k, TopologicalSpace (L k)] [∀ k, DiscreteTopology (L k)] [∀ k, ContinuousSMul G (L k)]
  {p : ∀ k, T →+ L k}
  {A : Type} [CommRing A] {π : ℤ_[2] →+* A}
  {N : Type} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulCommClass G A N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

/-- Reduction of continuous cochains is the tensor comparison in every degree. -/
theorem continuousReduction_bijective (hp : IsTwoAdicLimit p) (i : ℕ)
    (f : T →ₛₗ[π] N) (hfc : Continuous f)
    (hf : ∀ (g : G) (t : T), f (g • t) = g • f t)
    (e : A ⊗[ℤ] L i ≃ₗ[A] N)
    (he : ∀ t, f t = e ((1 : A) ⊗ₜ[ℤ] p i t))
    (hA : π ((2 : ℤ_[2]) ^ i) = 0) (n : ℤ) :
    Function.Bijective ((continuousCoefficientComplexMap f hfc hf).extend.f n).hom := by
  let : Algebra ℤ_[2] A := π.toAlgebra
  cases n with
  | ofNat j =>
    let E := ZInQ.Contrib.RC53Assist.ResidualFiniteness.cochainBaseChangeEquivOf
      ℤ A G (L i) e j
    let F : A ⊗[ℤ_[2]] (contCochains ℤ_[2] G T).X j →ₗ[A]
        A ⊗[ℤ] (contCochains ℤ G (L i)).X j :=
      E.symm.toLinearMap.comp ((continuousCoefficientComplexMap f hfc hf).extend.f (.ofNat j)).hom
    have hF : ∀ (a : A) (c : (contCochains ℤ_[2] G T).X j),
        F (a ⊗ₜ[ℤ_[2]] c) = a ⊗ₜ[ℤ] redCochain G p hp i j c := by
      intro a c
      apply E.injective
      change E (E.symm (((continuousCoefficientComplexMap f hfc hf).extend.f (.ofNat j)).hom
        (a ⊗ₜ[ℤ_[2]] c))) = E (a ⊗ₜ[ℤ] redCochain G p hp i j c)
      rw [E.apply_symm_apply]
      apply Subtype.ext
      funext g
      change a • f (cfun c g) = e (a ⊗ₜ[ℤ] p i (cfun c g))
      rw [he, ← e.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hbij := tensorReduction_bijective ((2 : ℤ_[2]) ^ i) (redCochain G p hp i j)
      (red_surjective hp i (.ofNat j)) (red_ker hp i (.ofNat j)) hA F hF
    constructor
    · intro x y hxy
      exact hbij.1 (congrArg E.symm hxy)
    · intro y
      obtain ⟨x, hx⟩ := hbij.2 (E.symm y)
      exact ⟨x, E.symm.injective hx⟩
  | negSucc j =>
    let : Subsingleton ((scalarChangedComplex π (natCx (contCochains ℤ_[2] G T)).toCC).X
        (.negSucc j)) := by
      change Subsingleton (A ⊗[ℤ_[2]] PUnit.{1})
      exact ZInQ.Contrib.RC53Assist.ResidualFiniteness.subsingleton_tensor_punit ℤ_[2] A
    let : Subsingleton ((natCx (contCochains A G N)).toCC.X (.negSucc j)) := by
      change Subsingleton PUnit.{1}
      infer_instance
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end ContinuousReduction

section CentralCoefficients

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

attribute [local instance] levTop continuousSMul_lev

/-- The finite central coefficient module is the tensor of the Tate residue,
with the integral quadratic-twist identification. -/
def finiteCentralTensorEquiv (D : GenuineKummerData K E₀ hZ) (i : ℕ) :
    ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i ⊗[ℤ] Lev K D.S (centralCurve D) i ≃ₗ[
      ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i] finiteCentralModule D i :=
  LinearEquiv.baseChange ℤ (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) _ _
    (globalTwistTorsEquiv D.W D.s D.hs D.hs0 i).toIntLinearEquiv

/-- The finite coefficient identification has the canonical unit-tensor formula. -/
theorem finiteCentralTensorEquiv_projection (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (t : TateS K D.S (centralCurve D)) :
    inflatedCoefficientReduction D i t =
      finiteCentralTensorEquiv D i ((1 : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) ⊗ₜ[ℤ] projLev i t) :=
  rfl

/-- The canonical comparison of global cochains is an isomorphism in every degree. -/
theorem globalCentralReduction_bijective (D : GenuineKummerData K E₀ hZ) (i : ℕ) (n : ℤ) :
    Function.Bijective ((continuousCoefficientComplexMap (inflatedCoefficientReduction D i)
      (inflatedCoefficientReduction_continuous D i) (inflatedCoefficientReduction_galois D i)).extend.f n).hom := by
  let : HasFullTwoTorsion K D.S (centralCurve D) := ⟨centralFullTorsion D⟩
  exact continuousReduction_bijective (isTwoAdicLimit_tate K D.S (centralCurve D)) i
    (inflatedCoefficientReduction D i) (inflatedCoefficientReduction_continuous D i)
    (inflatedCoefficientReduction_galois D i) (finiteCentralTensorEquiv D i)
    (finiteCentralTensorEquiv_projection D i)
    (by rw [map_pow, map_ofNat, acoef_two_pow_eq_zero]) n

/-- The same tensor identification after restricting to a decomposition group. -/
def localCentralTensorEquiv (D : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K D.S) :
    ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i ⊗[ℤ]
      ResMod (locMap K D.S v.1) (Lev K D.S (centralCurve D) i) ≃ₗ[
        ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i]
          ResMod (locMap K D.S v.1) (finiteCentralModule D i) :=
  finiteCentralTensorEquiv D i

/-- The full local cochain comparison is an isomorphism in every degree. -/
theorem fullLocalCentralReduction_bijective (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K D.S) (n : ℤ) :
    Function.Bijective ((fullLocalCoefficientMap D i v).extend.f n).hom := by
  let : HasFullTwoTorsion K D.S (centralCurve D) := ⟨centralFullTorsion D⟩
  exact continuousReduction_bijective
    (isTwoAdicLimit_tateRes K D.S (centralCurve D) (locMap K D.S v.1)) i
    (localCoefficientReduction D i v) (localCoefficientReduction_continuous D i v)
    (localCoefficientReduction_galois D i v) (localCentralTensorEquiv D i v)
    (fun _ => rfl) (by rw [map_pow, map_ofNat, acoef_two_pow_eq_zero]) n

end CentralCoefficients

section CoefficientProducts

variable {R A : Type} [CommRing R] [CommRing A] {π : R →+* A}

/-- Extension of a finite product of coefficient comparisons is bijective
when each extended component is bijective. -/
theorem coefficientPi_bijective {ι : Type} [Fintype ι]
    {C : ι → GCx R} {D : ι → GCx A}
    (f : ∀ v, CoefficientComplexMap π (C v) (D v)) (n : ℤ)
    (hf : ∀ v, Function.Bijective ((f v).extend.f n).hom) :
    Function.Bijective ((CoefficientComplexMap.pi f).extend.f n).hom := by
  classical
  let : Algebra R A := π.toAlgebra
  let E := TensorProduct.piRight R A A (fun v => (C v).X n)
  let F : (∀ v, A ⊗[R] (C v).X n) →ₗ[A] ∀ v, (D v).X n :=
    LinearMap.pi fun v => ((f v).extend.f n).hom.comp (LinearMap.proj v)
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      funext v
      exact (hf v).1 (congrFun hxy v)
    · intro y
      choose x hx using fun v => (hf v).2 (y v)
      exact ⟨x, funext hx⟩
  have h : ((CoefficientComplexMap.pi f).extend.f n).hom = F.comp E.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x => funext v; rfl
    | add x y hx hy => simp only [map_add, LinearMap.comp_apply] at hx hy ⊢; rw [hx, hy]
  rw [h]
  exact hF.comp E.bijective

/-- Bijective comparisons of the global, local-condition, and full local
terms give a bijective comparison of the Selmer-cone terms. -/
theorem coefficientSelmer_bijective {D : SelData R} {D' : SelData A}
    (g : CoefficientComplexMap π D.G D'.G) (u : CoefficientComplexMap π D.U D'.U)
    (l : CoefficientComplexMap π D.L D'.L)
    (hres : ∀ (i j : ℤ) (hij : i = j) (a : D.G.X i),
      l.f j (D.res.f i j hij a) = D'.res.f i j hij (g.f i a))
    (hι : ∀ (i j : ℤ) (hij : i = j) (a : D.U.X i),
      l.f j (D.ι.f i j hij a) = D'.ι.f i j hij (u.f i a))
    (n : ℤ) (hg : Function.Bijective (g.extend.f n).hom)
    (hu : Function.Bijective (u.extend.f n).hom)
    (hl : Function.Bijective (l.extend.f (n - 1)).hom) :
    Function.Bijective ((CoefficientComplexMap.selmer g u l hres hι).extend.f n).hom := by
  let : Algebra R A := π.toAlgebra
  let E := ZInQ.Contrib.RC53Assist.ResidualFiniteness.selBaseChangeEquiv A D n
  let F := (g.extend.f n).hom.prodMap
    ((u.extend.f n).hom.prodMap (l.extend.f (n - 1)).hom)
  have hF : Function.Bijective F := hg.prodMap (hu.prodMap hl)
  have h : ((CoefficientComplexMap.selmer g u l hres hι).extend.f n).hom =
      F.comp E.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, LinearMap.comp_apply] at hx hy ⊢; rw [hx, hy]
  rw [h]
  exact hF.comp E.bijective

/-- Changing only the presentation of the target Selmer data preserves
bijectivity of the extended comparison. -/
theorem coefficientSelmer_transport_bijective {C : GCx R} {D D' : SelData A}
    (e : D = D')
    (eT : CoefficientComplexMap π C (selCx D) = CoefficientComplexMap π C (selCx D'))
    (f : CoefficientComplexMap π C (selCx D)) (n : ℤ)
    (hf : Function.Bijective (f.extend.f n).hom) :
    Function.Bijective (((Eq.mp eT f).extend.f n).hom) := by
  cases e
  have h : eT = rfl := Subsingleton.elim _ _
  rw [h]
  exact hf

/-- A coefficient comparison with bijective extended components is an
isomorphism of cochain complexes. -/
theorem coefficientComparison_isIso {C : GCx R} {D : GCx A}
    (f : CoefficientComplexMap π C D)
    (hf : ∀ n, Function.Bijective (f.extend.f n).hom) : IsIso f.extend := by
  have : ∀ n, IsIso (f.extend.f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).2 (hf n)
  exact HomologicalComplex.Hom.isIso_of_components _

end CoefficientProducts

open ZInQ.Manuscript.RC.KummerMaps

/-- Every two-adic scalar is an integer residue plus a multiple of the precision. -/
theorem exists_residue_remainder (i : ℕ) (a : ℤ_[2]) :
    ∃ b : ℤ_[2], a = (resN i a : ℤ_[2]) + (2 : ℤ_[2]) ^ i * b := by
  have hz : PadicInt.toZModPow i (a - (resN i a : ℤ_[2])) = 0 := by
    rw [map_sub, map_natCast]
    change PadicInt.toZModPow i a - ((PadicInt.toZModPow i a).val : ZMod (2 ^ i)) = 0
    rw [ZMod.natCast_zmod_val, sub_self]
  have hm : a - (resN i a : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow i) := hz
  rw [PadicInt.ker_toZModPow] at hm
  have hm' : a - (resN i a : ℤ_[2]) ∈ Ideal.span {(2 : ℤ_[2]) ^ i} := by
    simpa only [Nat.cast_ofNat] using hm
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hm'
  exact ⟨b, by rw [← hb]; ring⟩

section LinearResidues

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/-- The linear identity separating an integer residue from its precision multiple. -/
theorem scalarResidue_identity (a r d b : R) (ha : a = r + d * b) (x y : M) :
    a • (x + d • y) = r • x + d • (b • x + a • y) := by
  calc
    a • (x + d • y) = (r + d * b) • x + a • d • y := by
      rw [smul_add]
      nth_rewrite 1 [ha]
      rfl
    _ = r • x + d • b • x + d • a • y := by
      rw [add_smul, mul_smul, smul_comm a d]
    _ = r • x + d • (b • x + a • y) := by
      rw [smul_add]
      abel

end LinearResidues

section LocalKummer

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic]
  (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  (v : HeightOneSpectrum (𝓞 K)) [DecidableEq (v.adicCompletion K)]

attribute [local instance] levTop continuousSMul_lev

/-- The integral cochains at a finite place. -/
abbrev localTateCochain (n : ℕ) : Type :=
  contCochain ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) n

/-- The integral degree-one Kummer lattice, including all continuous coboundaries. -/
abbrev localKummerLattice : Submodule ℤ_[2] (localTateCochain (S := S) W v 1) :=
  tateKummerZ W hFull v ⊔ contB1 ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W))

/-- The integral Kummer map into cochains modulo continuous coboundaries. -/
def tateKummerToQuot :
    (W.baseChange (v.adicCompletion K)).toAffine.Point →+
      (localTateCochain (S := S) W v 1 ⧸
        contB1 ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W))) :=
  AddMonoidHom.mk' (fun P => Submodule.Quotient.mk (tateKummerCocycle W hFull v P))
    (fun P Q => by
      rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq, ← sub_sub]
      exact tateKummerCocycle_add_sub_mem W hFull v P Q)

/-- An integral Kummer cocycle lies in the integral local condition. -/
theorem tateKummerCocycle_mem_lattice
    (P : (W.baseChange (v.adicCompletion K)).toAffine.Point) :
    tateKummerCocycle W hFull v P ∈ localKummerLattice W hFull v :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨P, rfl⟩)

/-- Modulo a prescribed power of two and coboundaries, every Kummer cochain
is the Kummer cocycle of a single local point. -/
theorem localKummer_residue (i : ℕ) (x : localTateCochain (S := S) W v 1)
    (hx : x ∈ localKummerLattice W hFull v) :
    ∃ (P : (W.baseChange (v.adicCompletion K)).toAffine.Point) (z : localTateCochain (S := S) W v 1),
      z ∈ localKummerLattice W hFull v ∧
      (Submodule.Quotient.mk x : localTateCochain (S := S) W v 1 ⧸
        contB1 ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W))) =
          tateKummerToQuot W hFull v P + (2 : ℤ_[2]) ^ i • Submodule.Quotient.mk z := by
  let B := contB1 ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W))
  have hspan : ∀ x ∈ tateKummerZ W hFull v,
      ∃ (P : (W.baseChange (v.adicCompletion K)).toAffine.Point) (z : localTateCochain (S := S) W v 1),
        z ∈ localKummerLattice W hFull v ∧
        B.mkQ x = tateKummerToQuot W hFull v P + (2 : ℤ_[2]) ^ i • B.mkQ z := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, rfl⟩ := hx
      refine ⟨P, 0, Submodule.zero_mem _, ?_⟩
      simp only [map_zero, smul_zero, add_zero]
      rfl
    | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp only [map_zero, smul_zero, add_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨P, z, hz, hx⟩ := hx
      obtain ⟨Q, w, hw, hy⟩ := hy
      refine ⟨P + Q, z + w, Submodule.add_mem _ hz hw, ?_⟩
      simp only [map_add, smul_add, hx, hy]
      abel
    | smul a x _ hx =>
      obtain ⟨P, z, hz, hx⟩ := hx
      obtain ⟨b, hb⟩ := exists_residue_remainder i a
      refine ⟨(resN i a : ℕ) • P, b • tateKummerCocycle W hFull v P + a • z,
        Submodule.add_mem _ (Submodule.smul_mem _ _ (tateKummerCocycle_mem_lattice W hFull v P))
          (Submodule.smul_mem _ _ hz), ?_⟩
      simp only [map_smul, hx, map_nsmul, map_add]
      change a • (tateKummerToQuot W hFull v P + (2 : ℤ_[2]) ^ i • B.mkQ z) =
        (resN i a : ℕ) • tateKummerToQuot W hFull v P +
          (2 : ℤ_[2]) ^ i • (b • tateKummerToQuot W hFull v P + a • B.mkQ z)
      rw [← Nat.cast_smul_eq_nsmul ℤ_[2]]
      exact scalarResidue_identity a (resN i a : ℤ_[2]) ((2 : ℤ_[2]) ^ i) b hb
        (tateKummerToQuot W hFull v P) (B.mkQ z)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨P, z, hz, h⟩ := hspan a ha
  refine ⟨P, z, hz, ?_⟩
  change B.mkQ (a + b) = _
  have hb0 : B.mkQ b = 0 := (Submodule.Quotient.mk_eq_zero B).2 hb
  rw [map_add, hb0, add_zero]
  exact h

/-- A Tate coordinate read in the local algebraic closure. -/
def localTatePoint (n : ℕ) : TateS K S W →+ PtAlg (v.adicCompletion K)
    (W.baseChange (v.adicCompletion K)) :=
  (compPt W v).comp
    ((AddSubgroup.torsionBy ((W.baseChange (KS K S)).toAffine.Point)
      ((2 ^ n : ℕ) : ℤ)).subtype.comp (projLev n))

/-- Local Tate coordinates retain the underlying global Tate point. -/
theorem localTatePoint_apply (n : ℕ) (t : TateS K S W) :
    localTatePoint W v n t = compPt W v (t.pt n) := rfl

/-- Compatibility of adjacent local Tate coordinates. -/
theorem localTatePoint_two (n : ℕ) (t : TateS K S W) :
    2 • localTatePoint W v (n + 1) t = localTatePoint W v n t := by
  rw [localTatePoint_apply, localTatePoint_apply, ← map_nsmul, t.two_smul_pt]

/-- Reading multiplication by a power of two at a later coordinate reads
exactly the earlier coordinate. -/
theorem localTatePoint_two_pow (n i : ℕ) (t : TateS K S W) :
    localTatePoint W v (n + i) ((2 : ℤ_[2]) ^ i • t) = localTatePoint W v n t := by
  rw [localTatePoint_apply, localTatePoint_apply, TateS.pt_padicSmul]
  have hlev : (2 ^ (n + i) : ℕ) • t.pt (n + i) = 0 :=
    two_pow_nsmul_lev (projLev (n + i) t)
  rw [show ((2 : ℤ_[2]) ^ i) = ((2 ^ i : ℕ) : ℤ_[2]) by push_cast; rfl,
    resN_natCast, nsmul_mod_eq hlev, t.two_pow_smul_pt n i]

/-- Local Tate coordinates are equivariant for the fixed decomposition map. -/
theorem localTatePoint_galois (n : ℕ) (σ : Gloc K v) (t : TateS K S W) :
    localTatePoint W v n (locMap K S v σ • t) = σ • localTatePoint W v n t :=
  congrArg Subtype.val (compTors_smul W (2 ^ n) v σ (projLev n t))

/-- The zeroth coordinate of a Tate module is zero. -/
theorem localTatePoint_zero (t : TateS K S W) : localTatePoint W v 0 t = 0 := by
  have h : t.pt 0 = 0 := by
    have h' : (2 ^ 0 : ℕ) • t.pt 0 = 0 := two_pow_nsmul_lev (projLev 0 t)
    simpa only [pow_zero, one_nsmul] using h'
  rw [localTatePoint_apply, h, map_zero]

/-- The local coordinate of a tower's Kummer cocycle is its actual Galois difference. -/
theorem localTatePoint_kummer {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (hR : IsDivTower _ _ P R) (n : ℕ) (g : Fin 1 → Gloc K v) :
    localTatePoint W v n
      (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) (tateKummerCocycleOf W hFull v hR) g) =
        g 0 • R n - R n :=
  congrArg Subtype.val (compTors_tateKummerFunOf W hFull v hR (g 0) n)

/-- The local coordinate of a continuous coboundary is the Galois difference
of its degree-zero value. -/
theorem localTatePoint_boundary (c : localTateCochain (S := S) W v 0)
    (n : ℕ) (g : Fin 1 → Gloc K v) :
    localTatePoint W v n (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) (contD ℤ_[2] (Gloc K v)
      (ResMod (locMap K S v) (TateS K S W)) 0 c) g) =
        g 0 • localTatePoint W v n (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) c default) -
          localTatePoint W v n (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) c default) := by
  rw [contD_zero_apply]
  change localTatePoint W v n (locMap K S v (g 0) • (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) c default) -
    (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) c default)) = _
  rw [map_sub, localTatePoint_galois]

/-- Dividing a Kummer cocycle modulo a coboundary produces another integral
Kummer cochain.  Its local point is obtained by Galois descent of the shifted tower. -/
theorem localKummer_division_of_boundary (i : ℕ)
    (P : (W.baseChange (v.adicCompletion K)).toAffine.Point)
    (y : localTateCochain (S := S) W v 1) (c : localTateCochain (S := S) W v 0)
    (hc : tateKummerCocycle W hFull v P - (2 : ℤ_[2]) ^ i • y =
      contD ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 0 c) :
    y ∈ localKummerLattice W hFull v := by
  let F := v.adicCompletion K
  let B := W.baseChange F
  let R := divTower F B P
  have hR : IsDivTower F B P R := isDivTower_divTower F B P
  let t : TateS K S W := cfun (M := ResMod (locMap K S v) (TateS K S W)) c default
  have hcoord (σ : Gloc K v) (n : ℕ) :
      (σ • R n - R n) - localTatePoint W v n
        ((2 : ℤ_[2]) ^ i • (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) y (fun _ => σ))) =
      σ • localTatePoint W v n t - localTatePoint W v n t := by
    have h := congrArg (fun z : localTateCochain (S := S) W v 1 =>
      localTatePoint W v n (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) z (fun _ => σ))) hc
    change localTatePoint W v n
      ((show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) (tateKummerCocycleOf W hFull v hR) (fun _ => σ)) -
        (2 : ℤ_[2]) ^ i • (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) y (fun _ => σ))) =
      localTatePoint W v n (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W))
        (contD ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 0 c) (fun _ => σ)) at h
    rw [map_sub, localTatePoint_kummer, localTatePoint_boundary] at h
    exact h
  let R' : ℕ → PtAlg F B := fun n => R (n + i) - localTatePoint W v (n + i) t
  have hfixed : ∀ σ : Gloc K v, σ • R' 0 = R' 0 := by
    intro σ
    have h := hcoord σ i
    have hz : localTatePoint W v i
        ((2 : ℤ_[2]) ^ i • (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) y (fun _ => σ))) = 0 := by
      simpa only [zero_add] using (localTatePoint_two_pow W v 0 i
        (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) y (fun _ => σ))).trans (localTatePoint_zero W v _)
    rw [hz, sub_zero] at h
    dsimp only [R']
    simp only [zero_add]
    apply sub_eq_zero.1
    calc
      σ • (R i - localTatePoint W v i t) - (R i - localTatePoint W v i t) =
          (σ • R i - R i) - (σ • localTatePoint W v i t - localTatePoint W v i t) := by
        rw [smul_sub]
        abel
      _ = 0 := sub_eq_zero.2 h
  obtain ⟨Q, hQ⟩ := exists_basePt_of_fixed hfixed
  have hR' : IsDivTower F B Q R' := by
    refine ⟨hQ.symm, fun n => ?_⟩
    dsimp only [R']
    rw [show n + 1 + i = n + i + 1 by omega, nsmul_sub, hR.2,
      localTatePoint_two]
  have hy : y = tateKummerCocycleOf W hFull v hR' := by
    apply Subtype.ext
    funext g
    change (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) y g) =
      (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) (tateKummerCocycleOf W hFull v hR') g)
    apply TateS.ext'
    intro n
    apply compPt_injective W v
    change localTatePoint W v n (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) y g) =
      localTatePoint W v n (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) (tateKummerCocycleOf W hFull v hR') g)
    rw [localTatePoint_kummer]
    have h := hcoord (g 0) (n + i)
    have hg : (fun _ : Fin 1 => g 0) = g := by funext j; fin_cases j; rfl
    rw [hg, localTatePoint_two_pow] at h
    change localTatePoint W v n (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) y g) =
      g 0 • (R (n + i) - localTatePoint W v (n + i) t) -
        (R (n + i) - localTatePoint W v (n + i) t)
    calc
      localTatePoint W v n (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) y g) =
          ((g 0 • localTatePoint W v (n + i) t - localTatePoint W v (n + i) t) +
            localTatePoint W v n (show TateS K S W from cfun (M := ResMod (locMap K S v) (TateS K S W)) y g)) -
          (g 0 • localTatePoint W v (n + i) t - localTatePoint W v (n + i) t) := by abel
      _ = (g 0 • R (n + i) - R (n + i)) -
          (g 0 • localTatePoint W v (n + i) t - localTatePoint W v (n + i) t) := by
        rw [← sub_eq_iff_eq_add.1 h]
      _ = _ := by rw [smul_sub]; abel
  rw [hy]
  exact tateKummerCocycleOf_mem_sup W hFull v hR'

/-- The integral Kummer lattice is saturated under every power of two. -/
theorem localKummer_saturated (i : ℕ) (y : localTateCochain (S := S) W v 1)
    (hy : (2 : ℤ_[2]) ^ i • y ∈ localKummerLattice W hFull v) :
    y ∈ localKummerLattice W hFull v := by
  let B := contB1 ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W))
  obtain ⟨P, z, hz, h⟩ := localKummer_residue W hFull v i ((2 : ℤ_[2]) ^ i • y) hy
  have hb : tateKummerCocycle W hFull v P - (2 : ℤ_[2]) ^ i • (y - z) ∈ B := by
    apply (Submodule.Quotient.mk_eq_zero B).1
    change B.mkQ (tateKummerCocycle W hFull v P - (2 : ℤ_[2]) ^ i • (y - z)) = 0
    simp only [map_sub, map_smul]
    have h' : (2 : ℤ_[2]) ^ i • B.mkQ y =
        tateKummerToQuot W hFull v P + (2 : ℤ_[2]) ^ i • B.mkQ z := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul] using h
    change tateKummerToQuot W hFull v P -
      (2 : ℤ_[2]) ^ i • (B.mkQ y - B.mkQ z) = 0
    rw [smul_sub]
    calc
      tateKummerToQuot W hFull v P -
          ((2 : ℤ_[2]) ^ i • B.mkQ y - (2 : ℤ_[2]) ^ i • B.mkQ z) =
        (tateKummerToQuot W hFull v P + (2 : ℤ_[2]) ^ i • B.mkQ z) -
          (2 : ℤ_[2]) ^ i • B.mkQ y := by abel
      _ = 0 := sub_eq_zero.2 h'.symm
  obtain ⟨c, hc⟩ := (mem_contB1_iff _).1 hb
  have hu := localKummer_division_of_boundary W hFull v i P (y - z) c hc.symm
  simpa only [sub_add_cancel] using Submodule.add_mem (localKummerLattice W hFull v) hu hz

/-- The quotient of local integral cochains by the Kummer lattice is torsion-free. -/
theorem localKummer_quotient_torsionFree : Module.IsTorsionFree ℤ_[2]
    (localTateCochain (S := S) W v 1 ⧸ localKummerLattice W hFull v) := by
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot]
  apply le_antisymm
  · intro x hx
    change x = 0
    obtain ⟨a, ha⟩ := hx
    obtain ⟨y, rfl⟩ := (localKummerLattice W hFull v).mkQ_surjective x
    have hm : (a : ℤ_[2]) • y ∈ localKummerLattice W hFull v := by
      exact (Submodule.Quotient.mk_eq_zero _).1 ha
    let u := PadicInt.unitCoeff (nonZeroDivisors.coe_ne_zero a)
    have hu : ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (a : ℤ_[2]) = (2 : ℤ_[2]) ^ (a : ℤ_[2]).valuation := by
      calc
        ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (a : ℤ_[2]) =
            ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((u : ℤ_[2]) * (2 : ℤ_[2]) ^ (a : ℤ_[2]).valuation) :=
          congrArg (((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ·)
            (PadicInt.unitCoeff_spec (nonZeroDivisors.coe_ne_zero a))
        _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]
    have hp := Submodule.smul_mem (localKummerLattice W hFull v) ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) hm
    rw [smul_smul, hu] at hp
    exact (Submodule.Quotient.mk_eq_zero _).2
      (localKummer_saturated W hFull v _ y hp)
  · exact bot_le

end LocalKummer

section LocalKummerReduction

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

attribute [local instance] levTop continuousSMul_lev

/-- The genuine finite central local condition, written as its cocycle subcomplex. -/
abbrev centralFiniteCondition (D : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K D.S) :
    GCx (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) :=
  cocycleCondition (finiteCentralZ D i v) (finiteCentralZ_cocycle D i v)

/-- The local condition in the finite central Selmer data. -/
abbrev centralActualCondition (D : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K D.S) :
    GCx (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) :=
  (actualKummerAtS (subset_refl D.S) D.W i D.s D.hs D.hs0
    (centralChar i D.s D.hs D.hs0) (D.hFull i) v
      (isLocallyQuadAt_centralChar i D.s D.hs D.hs0 v.1)).U

/-- Degree zero of the compact Kummer condition is the full degree-zero cochain module. -/
def compactConditionZeroEquiv (D : GenuineKummerData K E₀ hZ) (v : Places K D.S) :
    (tateKummerCondition (centralCurve D) (centralFullTorsion D) v.1).X 0 ≃ₗ[ℤ_[2]]
      contCochain ℤ_[2] (Gloc K v.1)
        (ResMod (locMap K D.S v.1) (TateS K D.S (centralCurve D))) 0 :=
  Submodule.topEquiv

/-- Degree zero of the genuine finite condition is the full degree-zero cochain module. -/
def finiteConditionZeroEquiv (D : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K D.S) :
    (centralFiniteCondition D i v).X 0 ≃ₗ[ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i]
      contCochain (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (Gloc K v.1)
        (ResMod (locMap K D.S v.1) (finiteCentralModule D i)) 0 :=
  Submodule.topEquiv

/-- The local Kummer comparison is bijective in degree zero. -/
theorem localKummerReduction_zero_bijective (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K D.S) :
    Function.Bijective ((kummerLocalCoefficientMap D (centralReductionCompatibility D) i v).extend.f 0).hom := by
  let : Algebra ℤ_[2] (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) := (constRed i).toAlgebra
  let E := LinearEquiv.baseChange ℤ_[2] (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) _ _
    (compactConditionZeroEquiv D v)
  let F := (finiteConditionZeroEquiv D i v).symm.toLinearMap.comp
    (((fullLocalCoefficientMap D i v).extend.f 0).hom.comp E.toLinearMap)
  have h : ((kummerLocalCoefficientMap D (centralReductionCompatibility D) i v).extend.f 0).hom = F := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a c => apply Subtype.ext; rfl
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  rw [h]
  exact (finiteConditionZeroEquiv D i v).symm.bijective.comp
    ((fullLocalCentralReduction_bijective D i v 0).comp E.bijective)

/-- A full compact degree-zero cochain gives its coboundary in the compact local condition. -/
def compactConditionBoundary (D : GenuineKummerData K E₀ hZ) (v : Places K D.S) :
    contCochain ℤ_[2] (Gloc K v.1)
      (ResMod (locMap K D.S v.1) (TateS K D.S (centralCurve D))) 0 →ₗ[ℤ_[2]]
        (tateKummerCondition (centralCurve D) (centralFullTorsion D) v.1).X 1 :=
  ((tateKummerCondition (centralCurve D) (centralFullTorsion D) v.1).d 0 1 rfl).comp
    (compactConditionZeroEquiv D v).symm.toLinearMap

/-- On underlying cochains this map is exactly the continuous coboundary. -/
theorem compactConditionBoundary_coe (D : GenuineKummerData K E₀ hZ) (v : Places K D.S)
    (c : contCochain ℤ_[2] (Gloc K v.1)
      (ResMod (locMap K D.S v.1) (TateS K D.S (centralCurve D))) 0) :
    (tateKummerConditionι (centralCurve D) (centralFullTorsion D) v.1).f 1 1 rfl
      (compactConditionBoundary D v c) =
        contD ℤ_[2] (Gloc K v.1) (ResMod (locMap K D.S v.1) (TateS K D.S (centralCurve D))) 0 c :=
  cocycleCondition_d₀ _ _ _

/-- The extended local Kummer comparison, followed by the local inclusion. -/
def extendedLocalKummerOne (D : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K D.S) :
    (scalarChangedComplex (constRed i)
      (tateKummerCondition (centralCurve D) (centralFullTorsion D) v.1).toCC).X 1 →ₗ[
        ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i]
      contCochain (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (Gloc K v.1)
        (ResMod (locMap K D.S v.1) (finiteCentralModule D i)) 1 :=
  ((cocycleConditionι (finiteCentralZ D i v) (finiteCentralZ_cocycle D i v)).f 1 1 rfl).comp
    ((kummerLocalCoefficientMap D (centralReductionCompatibility D) i v).extend.f 1).hom

/-- All finite continuous coboundaries lie in the extended integral Kummer image. -/
theorem extendedLocalKummerOne_boundaries (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K D.S) :
    contB1 (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (Gloc K v.1)
      (ResMod (locMap K D.S v.1) (finiteCentralModule D i)) ≤
        LinearMap.range (extendedLocalKummerOne D i v) := by
  intro b hb
  obtain ⟨c, rfl⟩ := (mem_contB1_iff b).1 hb
  let C := scalarChangedComplex (constRed i)
    (tateKummerCondition (centralCurve D) (centralFullTorsion D) v.1).toCC
  let f := (kummerLocalCoefficientMap D (centralReductionCompatibility D) i v).extend
  let cU := (finiteConditionZeroEquiv D i v).symm c
  obtain ⟨x, hx⟩ := (localKummerReduction_zero_bijective D i v).2 cU
  refine ⟨(C.d 0 1).hom x, ?_⟩
  have h := congrArg (fun t => t.hom x) (f.comm 0 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change (cocycleConditionι (finiteCentralZ D i v) (finiteCentralZ_cocycle D i v)).f 1 1 rfl
    ((f.f 1).hom ((C.d 0 1).hom x)) = _
  rw [← h, hx]
  exact cocycleCondition_toCC_d₀ (finiteCentralZ D i v) (finiteCentralZ_cocycle D i v) cU

/-- The finite central Kummer generators can be read on the actual central twist. -/
theorem finiteCentralZ_eq_localTwist (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K D.S) :
    finiteCentralZ D i v =
      kummerZ' (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (localTwistIota D i v) := by
  have := isElliptic_localTwist D.W (ne_zero_of_sqrt D.s D.hs D.hs0) v.1
  exact (kummerZ'_curveCast (A := ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
    (localTwist_eq_baseChange D.W (hZ : K) v.1).symm
    (kummerIotaS (subset_refl D.S) D.W i D.s D.hs D.hs0
      (centralChar i D.s D.hs D.hs0) (D.hFull i) v)).symm

/-- The reduction of an integral Kummer cocycle differs from the finite
Kummer generator of the same point by a finite continuous coboundary. -/
theorem reducedKummer_sub_generator (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K D.S)
    (P : ((centralCurve D).baseChange (v.1.adicCompletion K)).toAffine.Point) :
    cochainCoefficientMap (localCoefficientReduction D i v)
      (localCoefficientReduction_continuous D i v) 1
        (tateKummerCocycle (centralCurve D) (centralFullTorsion D) v.1 P) -
      kummerCocycleIn (localTwistIota D i v)
        (1 : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) P ∈
      contB1 (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (Gloc K v.1)
        (ResMod (locMap K D.S v.1) (finiteCentralModule D i)) := by
  let B := (centralCurve D).baseChange (v.1.adicCompletion K)
  let hP := (isDivTower_divTower (v.1.adicCompletion K) B P).two_pow_smul i
  have hb := kummerCocycleOf_sub_mem (v.1.adicCompletion K) B (2 ^ i) hP
  have h := cochainCoefficientMap_mem_B1
    (integerCoefficientMap (A := ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (localTwistIota D i v))
    (integerCoefficientMap_continuous (A := ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
      (localTwistIota D i v)) (localTwistIota_galois D i v) _ hb
  rw [map_sub] at h
  have hp : cochainCoefficientMap
      (integerCoefficientMap (A := ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (localTwistIota D i v))
      (integerCoefficientMap_continuous (A := ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
        (localTwistIota D i v)) 1 (kummerCocycle (v.1.adicCompletion K) B (2 ^ i) P) =
      kummerCocycleIn (localTwistIota D i v)
        (1 : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) P := by
    apply Subtype.ext
    funext g
    change localTwistIota D i v (kummerFun (v.1.adicCompletion K) B (2 ^ i) P (g 0)) =
      (1 : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) •
        localTwistIota D i v (kummerFun (v.1.adicCompletion K) B (2 ^ i) P (g 0))
    rw [one_smul]
  rw [hp] at h
  rw [localCoefficientReduction_tateKummer D i v P]
  exact h

/-- Every finite Kummer generator lies in the extended integral Kummer image. -/
theorem extendedLocalKummerOne_generators (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K D.S) :
    finiteCentralZ D i v ≤ LinearMap.range (extendedLocalKummerOne D i v) := by
  let : Algebra ℤ_[2] (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) := (constRed i).toAlgebra
  rw [finiteCentralZ_eq_localTwist]
  apply Submodule.span_le.2
  rintro _ ⟨⟨a, P⟩, rfl⟩
  change kummerCocycleIn (localTwistIota D i v) a P ∈
    LinearMap.range (extendedLocalKummerOne D i v)
  rw [kummerCocycleIn_eq_smul (localTwistIota D i v) a P]
  apply Submodule.smul_mem _ a
  let k := cochainCoefficientMap (localCoefficientReduction D i v)
    (localCoefficientReduction_continuous D i v) 1
      (tateKummerCocycle (centralCurve D) (centralFullTorsion D) v.1 P)
  have hk : k ∈ LinearMap.range (extendedLocalKummerOne D i v) := by
    let c : (tateKummerCondition (centralCurve D) (centralFullTorsion D) v.1).X 1 :=
      ⟨tateKummerCocycle (centralCurve D) (centralFullTorsion D) v.1 P,
        tateKummerCocycle_mem_lattice (centralCurve D) (centralFullTorsion D) v.1 P⟩
    refine ⟨(1 : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) ⊗ₜ[ℤ_[2]] c, ?_⟩
    change (1 : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) • k = k
    exact one_smul _ _
  have hb : k - kummerCocycleIn (localTwistIota D i v)
      (1 : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) P ∈
        LinearMap.range (extendedLocalKummerOne D i v) :=
    extendedLocalKummerOne_boundaries D i v (reducedKummer_sub_generator D i v P)
  have h : kummerCocycleIn (localTwistIota D i v)
      (1 : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) P =
      k - (k - kummerCocycleIn (localTwistIota D i v)
        (1 : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) P) := by abel
  rw [h]
  exact Submodule.sub_mem _ hk hb

/-- Saturation makes the compact Kummer inclusion injective after every
finite central coefficient extension. -/
theorem compactKummerSubtype_baseChange_injective (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K D.S) [Algebra ℤ_[2] (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)] :
    Function.Injective ((localKummerLattice (centralCurve D) (centralFullTorsion D) v.1).subtype.baseChange
      (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)) := by
  let U := localKummerLattice (centralCurve D) (centralFullTorsion D) v.1
  let := localKummer_quotient_torsionFree (centralCurve D) (centralFullTorsion D) v.1
  have h := ZInQ.Contrib.RC53Assist.CalibrationModel.tensor_kernel_injective
    (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) U.mkQ U.mkQ_surjective
  rw [Submodule.ker_mkQ] at h
  exact h

/-- The canonical local Kummer comparison is bijective in degree one. -/
theorem localKummerReduction_one_bijective (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K D.S) :
    Function.Bijective ((kummerLocalCoefficientMap D (centralReductionCompatibility D) i v).extend.f 1).hom := by
  let : Algebra ℤ_[2] (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) := (constRed i).toAlgebra
  let U := localKummerLattice (centralCurve D) (centralFullTorsion D) v.1
  have h : extendedLocalKummerOne D i v = ((fullLocalCoefficientMap D i v).extend.f 1).hom.comp
      (U.subtype.baseChange (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a c => rfl
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  have hinj : Function.Injective (extendedLocalKummerOne D i v) := by
    rw [h]
    exact (fullLocalCentralReduction_bijective D i v 1).1.comp
      (compactKummerSubtype_baseChange_injective D i v)
  constructor
  · intro x y hxy
    apply hinj
    exact congrArg ((cocycleConditionι (finiteCentralZ D i v) (finiteCentralZ_cocycle D i v)).f 1 1 rfl) hxy
  · intro y
    have hy : (cocycleConditionι (finiteCentralZ D i v) (finiteCentralZ_cocycle D i v)).f 1 1 rfl y ∈
        finiteCentralZ D i v ⊔ contB1 (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (Gloc K v.1)
          (ResMod (locMap K D.S v.1) (finiteCentralModule D i)) := y.2
    have hle := sup_le (extendedLocalKummerOne_generators D i v)
      (extendedLocalKummerOne_boundaries D i v)
    obtain ⟨x, hx⟩ := hle hy
    refine ⟨x, ?_⟩
    apply cocycleConditionι_injective (finiteCentralZ D i v) (finiteCentralZ_cocycle D i v) 1
    exact hx

/-- Every extended local Kummer component is bijective, including both
nonzero degrees of the condition and its zero terms. -/
theorem localKummerReduction_bijective (D : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K D.S) (n : ℤ) :
    Function.Bijective ((kummerLocalCoefficientMap D (centralReductionCompatibility D) i v).extend.f n).hom := by
  let : Algebra ℤ_[2] (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) := (constRed i).toAlgebra
  cases n with
  | ofNat j =>
    rcases j with _ | _ | j
    · exact localKummerReduction_zero_bijective D i v
    · exact localKummerReduction_one_bijective D i v
    · let : Subsingleton ((scalarChangedComplex (constRed i)
          (tateKummerCondition (centralCurve D) (centralFullTorsion D) v.1).toCC).X (.ofNat (j + 2))) := by
        change Subsingleton (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i ⊗[ℤ_[2]]
          ↥(⊥ : Submodule ℤ_[2] (contCochain ℤ_[2] (Gloc K v.1)
            (ResMod (locMap K D.S v.1) (TateS K D.S (centralCurve D))) (j + 2))))
        infer_instance
      let : Subsingleton ((centralActualCondition D i v).toCC.X (.ofNat (j + 2))) := by
        change Subsingleton ↥(⊥ : Submodule (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
          (contCochain (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (Gloc K v.1)
            (ResMod (locMap K D.S v.1) (finiteCentralModule D i)) (j + 2)))
        infer_instance
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  | negSucc j =>
    let : Subsingleton ((scalarChangedComplex (constRed i)
        (tateKummerCondition (centralCurve D) (centralFullTorsion D) v.1).toCC).X (.negSucc j)) := by
      change Subsingleton (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i ⊗[ℤ_[2]] PUnit.{1})
      exact ZInQ.Contrib.RC53Assist.ResidualFiniteness.subsingleton_tensor_punit ℤ_[2]
        (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
    let : Subsingleton ((centralActualCondition D i v).toCC.X (.negSucc j)) := by
      change Subsingleton PUnit.{1}
      infer_instance
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end LocalKummerReduction

section CentralReduction

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The canonical comparison of the entire Selmer cone has bijective components. -/
theorem canonicalCentralReduction_bijective (D : GenuineKummerData K E₀ hZ) (i : ℕ) (n : ℤ) :
    Function.Bijective ((canonicalCentralReductionMap D i).f n).hom := by
  classical
  let : Finite (Places K D.S) := D.hSfin.to_subtype
  let : Fintype (Places K D.S) := Fintype.ofFinite _
  let g : CoefficientComplexMap (constRed i) (compactCentralSelData D).G (simpleCentralSelData D i).G :=
    continuousCoefficientComplexMap (inflatedCoefficientReduction D i)
      (inflatedCoefficientReduction_continuous D i) (inflatedCoefficientReduction_galois D i)
  let l : CoefficientComplexMap (constRed i) (compactCentralSelData D).L (simpleCentralSelData D i).L :=
    CoefficientComplexMap.pi (fullLocalCoefficientMap D i)
  let u : CoefficientComplexMap (constRed i) (compactCentralSelData D).U (simpleCentralSelData D i).U :=
    CoefficientComplexMap.pi (kummerLocalCoefficientMap D (centralReductionCompatibility D) i)
  have hres : ∀ (a b : ℤ) (hab : a = b) (x : (compactCentralSelData D).G.X a),
      l.f b ((compactCentralSelData D).res.f a b hab x) =
        (simpleCentralSelData D i).res.f a b hab (g.f a x) := by
    intro a b hab x
    subst hab
    funext v
    cases a <;> rfl
  have hι : ∀ (a b : ℤ) (hab : a = b) (x : (compactCentralSelData D).U.X a),
      l.f b ((compactCentralSelData D).ι.f a b hab x) =
        (simpleCentralSelData D i).ι.f a b hab (u.f a x) := by
    intro a b hab x
    subst hab
    funext v
    cases a <;> rfl
  have h := coefficientSelmer_bijective g u l hres hι n
    (globalCentralReduction_bijective D i n)
    (coefficientPi_bijective (kummerLocalCoefficientMap D (centralReductionCompatibility D) i) n
      (fun v => localKummerReduction_bijective D i v n))
    (coefficientPi_bijective (fullLocalCoefficientMap D i) (n - 1)
      (fun v => fullLocalCentralReduction_bijective D i v (n - 1)))
  dsimp only [canonicalCentralReductionMap, centralReductionMap, centralCoefficientComplexMap]
  exact coefficientSelmer_transport_bijective (simpleCentralSelData_eq D i) _ _ n h

/-- The canonical compact-to-finite comparison is an isomorphism of complexes. -/
theorem canonicalCentralReductionMap_isIso (D : GenuineKummerData K E₀ hZ) (i : ℕ) :
    IsIso (canonicalCentralReductionMap D i) := by
  have : ∀ n, IsIso ((canonicalCentralReductionMap D i).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).2 (canonicalCentralReduction_bijective D i n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- All canonical central reduction maps are quasi-isomorphisms. -/
theorem canonicalCentralReductionMap_quasiIso (D : GenuineKummerData K E₀ hZ) (i : ℕ) :
    QuasiIso (canonicalCentralReductionMap D i) := by
  have := canonicalCentralReductionMap_isIso D i
  infer_instance

end CentralReduction

/-!
# The cohomological support of the compact Kummer complex

The dimension bounds are used at finite discrete coefficients and lifted
through the two-adic limit.  No cohomology shape or finite-level order is
assumed.  The global dimension statement is Milne, Arithmetic Duality
Theorems, second edition, I.4.10(c), p. 57.  The local statement follows
from I.2.3, p. 28, for finite discrete modules over a field of characteristic
zero.  The usual continuous inhomogeneous cochains are used throughout.
-/

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Manuscript.RC53Assist.CentralUniversal
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.RC53Assist.Finiteness
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open scoped TensorProduct

/-- Milne I.4.10(c), p. 57, in the absence of real places: a finite discrete
module whose order is invertible outside the support has no cohomology above degree two. -/
def MilneGlobalDimensionTwo : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
    ∀ (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite →
    ∀ (M : Type) [AddCommGroup M] [DistribMulAction (GKS K S) M]
      [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M],
      Finite M →
      (∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
      ∀ n : ℤ, 2 < n → Subsingleton ((natCx (contCochains ℤ (GKS K S) M)).toCC.homology n)

/-- Milne I.2.3, p. 28: local Tate duality gives vanishing above degree two
for every finite discrete module over a finite completion of a number field. -/
def MilneLocalDimensionTwo : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (M : Type) [AddCommGroup M] [DistribMulAction (Gloc K v) M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Gloc K v) M],
    Finite M → ∀ n : ℤ, 2 < n →
      Subsingleton ((natCx (contCochains ℤ (Gloc K v) M)).toCC.homology n)

section VanishingAlgebra

variable {R : Type} [CommRing R]

/-- Cohomology is cycles modulo boundaries, with the relation-indexed
differentials displayed explicitly. -/
def gcxRawHomologyEquiv (C : GCx R) (i n j : ℤ) (hi : i + 1 = n) (hj : n + 1 = j) :
    C.toCC.homology n ≃ₗ[R] subquot (LinearMap.range (C.d i n hi)) (LinearMap.ker (C.d n j hj)) := by
  let e := ZInQ.Contrib.RC53Assist.Finiteness.gcxHomologyEquiv C i n j hi hj
  rw [sc'_f_hom C i n j hi, sc'_g_hom C i n j hj] at e
  exact e

/-- A zero term has zero cohomology. -/
theorem homology_subsingleton_of_term (C : GCx R) (n : ℤ) (h : Subsingleton (C.X n)) :
    Subsingleton (C.toCC.homology n) := by
  let : Subsingleton (C.toCC.X n) := h
  have he : C.toCC.ExactAt n := by
    apply (C.toCC.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).2
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    change Function.Exact (C.toCC.sc' (n - 1) n (n + 1)).f.hom
      (C.toCC.sc' (n - 1) n (n + 1)).g.hom
    rw [sc'_f_hom C (n - 1) n (n + 1) (by omega), sc'_g_hom C (n - 1) n (n + 1) rfl]
    change Function.Exact (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl)
    intro x
    constructor
    · intro _
      exact ⟨0, (map_zero _).trans (h.elim _ _)⟩
    · rintro ⟨y, rfl⟩
      exact C.d_d _ _ _ _ _ y
  exact ModuleCat.isZero_iff_subsingleton.1 ((C.toCC.exactAt_iff_isZero_homology n).1 he)

/-- An exact middle module is zero when its two ends are zero. -/
theorem subsingleton_of_exact {T : ShortComplex (ModuleCat.{0} R)} (h : T.Exact)
    (h₁ : Subsingleton T.X₁) (h₃ : Subsingleton T.X₃) : Subsingleton T.X₂ := by
  let := h₁
  let := h₃
  rw [ShortComplex.moduleCat_exact_iff] at h
  have hz (x : T.X₂) : x = 0 := by
    obtain ⟨y, hy⟩ := h x (Subsingleton.elim _ _)
    have hy0 : y = 0 := Subsingleton.elim _ _
    simpa only [hy0, map_zero] using hy.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Vanishing of every component gives vanishing of a product's cohomology. -/
theorem pi_homology_subsingleton {ι : Type} (C : ι → GCx R) (n : ℤ)
    (h : ∀ v, Subsingleton ((C v).toCC.homology n)) :
    Subsingleton ((piCx C).toCC.homology n) := by
  have hc (v : ι) : Subsingleton (subquot
      (LinearMap.range ((C v).d (n - 1) n (by omega)))
      (LinearMap.ker ((C v).d n (n + 1) rfl))) := by
    let := h v
    exact (gcxRawHomologyEquiv (C v) (n - 1) n (n + 1) (by omega) rfl).symm.injective.subsingleton
  let : ∀ v : ι, Subsingleton (subquot
      (LinearMap.range ((C v).d (n - 1) n (by omega)))
      (LinearMap.ker ((C v).d n (n + 1) rfl))) := hc
  obtain ⟨f, hf⟩ := exists_injective_subquot_piCx C n
  let := hf.subsingleton
  exact (gcxRawHomologyEquiv (piCx C) (n - 1) n (n + 1) (sub_add_cancel n 1) rfl).injective.subsingleton

/-- Shifting down shifts a vanishing cohomology group by one degree. -/
theorem shiftDown_homology_subsingleton (C : GCx R) (n : ℤ)
    (h : Subsingleton (C.toCC.homology (n - 1))) :
    Subsingleton ((shiftDown C).toCC.homology n) := by
  let := h
  have hc : Subsingleton (subquot
      (LinearMap.range (C.d (n - 1 - 1) (n - 1) (by omega)))
      (LinearMap.ker (C.d (n - 1) (n - 1 + 1) rfl))) :=
    (gcxRawHomologyEquiv C (n - 1 - 1) (n - 1) (n - 1 + 1) (by omega) rfl).symm.injective.subsingleton
  let : Subsingleton (subquot
      (LinearMap.range ((shiftDown C).d (n - 1) n (by omega)))
      (LinearMap.ker ((shiftDown C).d n (n + 1) rfl))) := by
    rw [range_shiftDown_d, ker_shiftDown_d]
    exact hc
  exact (gcxRawHomologyEquiv (shiftDown C) (n - 1) n (n + 1) (sub_add_cancel n 1) rfl).injective.subsingleton

/-- The two exact sequences of the Selmer cone give its degreewise vanishing. -/
theorem selmer_homology_subsingleton (D : SelData R) (n : ℤ)
    (hG : Subsingleton (D.G.toCC.homology n))
    (hU : Subsingleton (D.U.toCC.homology n))
    (hL : Subsingleton (D.L.toCC.homology (n - 1))) :
    Subsingleton ((selCx D).toCC.homology n) := by
  have hC : Subsingleton ((locCx D).toCC.homology n) :=
    subsingleton_of_exact ((coneSES_shortExact (negι D)).homology_exact₂ n)
      (shiftDown_homology_subsingleton D.L n hL) hU
  exact subsingleton_of_exact ((sesTop_shortExact D).homology_exact₂ n) hC hG

/-- Extension by zero has zero negative terms. -/
theorem natCx_negative_term (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℤ) (hn : n < 0) :
    Subsingleton ((natCx C).X n) := by
  cases n with
  | ofNat j => simp only [Int.ofNat_eq_natCast] at hn; omega
  | negSucc j => exact inferInstanceAs (Subsingleton PUnit.{1})

end VanishingAlgebra

section LimitVanishing

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {T : Type} [AddCommGroup T] [Module ℤ_[2] T]
  [DistribMulAction G T] [SMulCommClass G ℤ_[2] T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul ℤ_[2] T] [ContinuousSMul G T]
  {L : ℕ → Type} [∀ k, AddCommGroup (L k)] [∀ k, DistribMulAction G (L k)]
  [∀ k, TopologicalSpace (L k)] [∀ k, DiscreteTopology (L k)] [∀ k, ContinuousSMul G (L k)]
  {p : ∀ k, T →+ L k}

/-- Vanishing at every finite level lifts to the two-adic cochain complex.
The finite residual quotients make approximate primitives actual primitives. -/
theorem twoAdic_homology_subsingleton (hp : IsTwoAdicLimit p) (hG : IsEquivariantLevels G p)
    (hfin : ∀ k m, Finite ((natCx (contCochains ℤ G (L k))).toCC.homology m))
    (n : ℤ) (hzero : ∀ k, Subsingleton ((natCx (contCochains ℤ G (L k))).toCC.homology n)) :
    Subsingleton ((natCx (contCochains ℤ_[2] G T)).toCC.homology n) := by
  let C := natCx (contCochains ℤ_[2] G T)
  have he : C.toCC.ExactAt n := by
    apply (C.toCC.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).2
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    change Function.Exact (C.toCC.sc' (n - 1) n (n + 1)).f.hom
      (C.toCC.sc' (n - 1) n (n + 1)).g.hom
    rw [sc'_f_hom C (n - 1) n (n + 1) (by omega), sc'_g_hom C (n - 1) n (n + 1) rfl]
    change Function.Exact (C.d (n - 1) n (by omega)) (C.d n (n + 1) rfl)
    intro x
    constructor
    · intro hx
      have happrox : ∀ k : ℕ, ∃ (y : C.X n) (w : C.X (n - 1)),
          x - C.d (n - 1) n (by omega) w = (2 : ℤ_[2]) ^ k • y := by
        intro k
        let D := natCx (contCochains ℤ G (L k))
        let := hzero k
        have hd : D.toCC.ExactAt n :=
          (D.toCC.exactAt_iff_isZero_homology n).2 (ModuleCat.isZero_of_subsingleton _)
        have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
          ((D.toCC.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).1 hd)
        change Function.Exact (D.toCC.sc' (n - 1) n (n + 1)).f.hom
          (D.toCC.sc' (n - 1) n (n + 1)).g.hom at hex
        rw [sc'_f_hom D (n - 1) n (n + 1) (by omega), sc'_g_hom D (n - 1) n (n + 1) rfl] at hex
        change Function.Exact (D.d (n - 1) n (by omega)) (D.d n (n + 1) rfl) at hex
        have hdx : D.d n (n + 1) rfl (red G p hp k n x) = 0 := by
          rw [← red_comm hp hG k n (n + 1) rfl x]
          change red G p hp k (n + 1) (C.d n (n + 1) rfl x) = 0
          rw [hx, map_zero]
        obtain ⟨w', hw'⟩ := (hex (red G p hp k n x)).1 hdx
        obtain ⟨w, rfl⟩ := red_surjective hp k (n - 1) w'
        obtain ⟨y, hy⟩ := red_ker hp k n (x - C.d (n - 1) n (by omega) w) (by
          rw [map_sub, red_comm hp hG k (n - 1) n (by omega) w, hw', sub_self])
        exact ⟨y, w, hy⟩
      obtain ⟨w, hw⟩ := exists_eq_of_forall_two_pow
        (C.d (n - 1 - 1) (n - 1) (by omega)) (C.d (n - 1) n (by omega))
        (fun y => C.d_d _ _ _ _ _ y) (cochains_separated hp n)
        (cochains_complete hp (n - 1))
        (fun k => twoPowResidualFinite_of_levels hp hG k (n - 1 - 1) (n - 1) n
          (by omega) (by omega) (hfin k (n - 1))) x happrox
      exact ⟨w, hw⟩
    · rintro ⟨y, rfl⟩
      exact C.d_d _ _ _ _ _ y
  exact ModuleCat.isZero_iff_subsingleton.1 ((C.toCC.exactAt_iff_isZero_homology n).1 he)

end LimitVanishing

section TateSupport

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic]
  (hFull : ∀ k : ℕ, FullTorsion K S W (2 ^ k))

attribute [local instance] levTop continuousSMul_lev

include hFull in
/-- Global finite-level dimension bounds give the global integral Tate dimension bound. -/
theorem globalTate_homology_high (hglob : MilneGlobalFiniteness)
    (hcd : MilneGlobalDimensionTwo) (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (n : ℤ) (hn : 2 < n) :
    Subsingleton ((natCx (contCochains ℤ_[2] (GKS K S) (TateS K S W))).toCC.homology n) := by
  let : HasFullTwoTorsion K S W := ⟨hFull⟩
  exact twoAdic_homology_subsingleton (isTwoAdicLimit_tate K S W)
    (isEquivariantLevels_tate K S W)
    (fun k m => hglob K S hS ℤ (Lev K S W k) inferInstance (natCard_lev_mem h2 k) m)
    n (fun k => hcd K hK S hS (Lev K S W k) inferInstance (natCard_lev_mem h2 k) n hn)

include hFull in
/-- Local finite-level dimension bounds give the local integral Tate dimension bound. -/
theorem localTate_homology_high (hloc : MilneLocalFiniteness)
    (hcd : MilneLocalDimensionTwo) (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) (hn : 2 < n) :
    Subsingleton ((natCx (contCochains ℤ_[2] (Gloc K v)
      (ResMod (locMap K S v) (TateS K S W)))).toCC.homology n) := by
  let : HasFullTwoTorsion K S W := ⟨hFull⟩
  exact twoAdic_homology_subsingleton (isTwoAdicLimit_tateRes K S W (locMap K S v))
    (isEquivariantLevels_tateRes K S W (locMap K S v))
    (fun k m => hloc K v ℤ (ResMod (locMap K S v) (Lev K S W k))
      (inferInstanceAs (Finite (Lev K S W k))) m)
    n (fun k => hcd K v (ResMod (locMap K S v) (Lev K S W k))
      (inferInstanceAs (Finite (Lev K S W k))) n hn)

/-- The local Kummer condition has zero terms above degree one. -/
theorem tateKummerCondition_high_term (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) (hn : 1 < n) :
    Subsingleton ((tateKummerCondition W hFull v).X n) := by
  cases n with
  | negSucc j => omega
  | ofNat j =>
    rcases j with _ | _ | j
    · norm_num at hn
    · norm_num at hn
    · change Subsingleton ↥(⊥ : Submodule ℤ_[2]
        (contCochain ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) (j + 2)))
      infer_instance

/-- The compact Kummer complex has no cohomology in degrees at least four. -/
theorem compactKummer_homology_high (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (n : ℤ) (hn : 3 < n) : Subsingleton ((compactKummerComplex S W hFull).homology n) := by
  refine selmer_homology_subsingleton (tateKummerSelData S W hFull) n
    (globalTate_homology_high W hFull hglob hglobal hK hS h2 n (by omega)) ?_ ?_
  · apply pi_homology_subsingleton
    intro v
    exact homology_subsingleton_of_term _ n (tateKummerCondition_high_term W hFull v.1 n (by omega))
  · apply pi_homology_subsingleton
    intro v
    exact localTate_homology_high W hFull hloc hlocal v.1 (n - 1) (by omega)

/-- The compact Kummer complex has zero terms in negative degrees. -/
theorem compactKummer_negative_term (n : ℤ) (hn : n < 0) :
    Subsingleton ((compactKummerComplex S W hFull).X n) := by
  let D := tateKummerSelData S W hFull
  let : Subsingleton (D.G.X n) := natCx_negative_term _ n hn
  let : ∀ v : Places K S, Subsingleton ((tateKummerCondition W hFull v.1).X n) :=
    fun v => natCx_negative_term _ n hn
  let : Subsingleton (D.U.X n) := by
    change Subsingleton (∀ v : Places K S, (tateKummerCondition W hFull v.1).X n)
    infer_instance
  let : ∀ v : Places K S, Subsingleton ((locAt K S ℤ_[2] (TateS K S W) v).X (n - 1)) :=
    fun v => natCx_negative_term _ (n - 1) (by omega)
  let : Subsingleton (D.L.X (n - 1)) := by
    change Subsingleton (∀ v : Places K S, (locAt K S ℤ_[2] (TateS K S W) v).X (n - 1))
    infer_instance
  change Subsingleton (D.G.X n × D.U.X n × D.L.X (n - 1))
  infer_instance

/-- Consequently its cohomology vanishes in all negative degrees. -/
theorem compactKummer_homology_negative (n : ℤ) (hn : n < 0) :
    Subsingleton ((compactKummerComplex S W hFull).homology n) :=
  homology_subsingleton_of_term _ n (compactKummer_negative_term W hFull n hn)

end TateSupport

/-!
# Zeroth compact Kummer cohomology

A Tate vector fixed by the global Galois group has every coordinate in the
rational two-primary torsion subgroup.  Finiteness of that subgroup therefore
annihilates the vector, which is zero because the Tate module is torsion-free.
The degree-zero local Kummer inclusions are injective, so the same argument
applies to the full Selmer cone.
-/

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Contrib.RC53Assist.Finiteness
open scoped Classical

section RationalPoints

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K)

/-- The rational point map into the field unramified outside the support. -/
def basePointS : W.toAffine.Point →+ (W.baseChange (KS K S)).toAffine.Point :=
  (Affine.Point.map (W' := W.toAffine) (Algebra.ofId K (KS K S))).comp
    (Affine.Point.equivBaseChangeSelf W.toAffine).toAddMonoidHom

/-- The rational point map is injective. -/
theorem basePointS_injective : Function.Injective (basePointS (S := S) W) :=
  (Affine.Point.map_injective _).comp (Affine.Point.equivBaseChangeSelf W.toAffine).injective

/-- The map retains the coordinates of a rational nonsingular point. -/
theorem basePointS_some {x y : K} (h : W.toAffine.Nonsingular x y) :
    basePointS (S := S) W (.some x y h) = .some
      (algebraMap K (KS K S) x) (algebraMap K (KS K S) y)
      ((W.toAffine.baseChange_nonsingular (Algebra.ofId K (KS K S)).injective x y).2 h) := by
  simp only [basePointS, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    Affine.Point.equivBaseChangeSelf_some, Affine.Point.map_some]
  rfl

/-- Galois descent for a point over the unramified-outside-support field. -/
theorem exists_basePointS_of_fixed (P : (W.baseChange (KS K S)).toAffine.Point)
    (hP : ∀ σ : GKS K S, Affine.Point.map (galS K S σ).toAlgHom P = P) :
    ∃ Q : W.toAffine.Point, basePointS W Q = P := by
  letI : Normal K (KS K S) := ZInQ.Contrib.CloudB3RC53.RankCounts.normal_unramifiedOutside K S
  letI : IsGalois K (KS K S) := ⟨⟩
  rcases P with _ | ⟨x, y, hxy⟩
  · exact ⟨0, by rw [map_zero, ← Affine.Point.zero_def]⟩
  · have hfixed (σ : KS K S ≃ₐ[K] KS K S) : σ x = x ∧ σ y = y := by
      have h := hP (show GKS K S from σ)
      rw [Affine.Point.map_some, Affine.Point.some.injEq] at h
      change σ x = x ∧ σ y = y at h
      exact h
    obtain ⟨x₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2
      (fun σ => (hfixed σ).1)
    obtain ⟨y₀, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).2
      (fun σ => (hfixed σ).2)
    have h₀ : W.toAffine.Nonsingular x₀ y₀ :=
      (W.toAffine.baseChange_nonsingular (Algebra.ofId K (KS K S)).injective x₀ y₀).1 hxy
    exact ⟨.some x₀ y₀ h₀, basePointS_some W h₀⟩

end RationalPoints

section TateInvariants

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic]
  (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  [Finite (AddCommGroup.primaryComponent W.toAffine.Point 2)]

attribute [local instance] levTop continuousSMul_lev

include hFull in
/-- A global invariant Tate vector is zero when rational two-primary torsion is finite. -/
theorem globalFixedTate_zero (t : TateS K S W) (ht : ∀ σ : GKS K S, σ • t = t) : t = 0 := by
  let : HasFullTwoTorsion K S W := ⟨hFull⟩
  let P := AddCommGroup.primaryComponent W.toAffine.Point 2
  let N := Nat.card P
  have hN : N ≠ 0 := Nat.ne_of_gt Nat.card_pos
  have hpt (n : ℕ) : N • t.pt n = 0 := by
    have hfixed (σ : GKS K S) : Affine.Point.map (galS K S σ).toAlgHom (t.pt n) = t.pt n :=
      congrArg (fun s : TateS K S W => s.pt n) (ht σ)
    obtain ⟨Q, hQ⟩ := exists_basePointS_of_fixed W (t.pt n) hfixed
    have htor : (2 ^ n : ℕ) • Q = 0 := by
      apply basePointS_injective W
      rw [map_nsmul, hQ, map_zero]
      exact two_pow_nsmul_lev (projLev n t)
    have hmem : Q ∈ P := AddCommGroup.mem_primaryComponent.2 ⟨n, htor⟩
    have hz : N • Q = 0 := by
      have h : N • (⟨Q, hmem⟩ : P) = 0 := card_nsmul_eq_zero'
      exact congrArg Subtype.val h
    calc
      N • t.pt n = N • basePointS W Q := congrArg (N • ·) hQ.symm
      _ = basePointS W (N • Q) := (map_nsmul (basePointS W) N Q).symm
      _ = 0 := by rw [hz, map_zero]
  have hz : (N : ℤ_[2]) • t = 0 := by
    apply TateS.ext'
    intro n
    change resN n (N : ℤ_[2]) • t.pt n = 0
    have hlev : (2 ^ n : ℕ) • t.pt n = 0 := two_pow_nsmul_lev (projLev n t)
    rw [resN_natCast, nsmul_mod_eq hlev]
    exact hpt n
  exact (smul_eq_zero.1 hz).resolve_left (Nat.cast_ne_zero.2 hN)

include hFull in
/-- The global compact Tate cochain complex has zero zeroth cohomology. -/
theorem globalTate_homology_zero :
    Subsingleton ((natCx (contCochains ℤ_[2] (GKS K S) (TateS K S W))).toCC.homology 0) := by
  let C := natCx (contCochains ℤ_[2] (GKS K S) (TateS K S W))
  have he : C.toCC.ExactAt 0 := by
    apply (C.toCC.exactAt_iff' (-1) 0 1 (by simp) (by simp)).2
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    change Function.Exact (C.toCC.sc' (-1) 0 1).f.hom (C.toCC.sc' (-1) 0 1).g.hom
    rw [sc'_f_hom C (-1) 0 1 (by decide), sc'_g_hom C (-1) 0 1 rfl]
    change Function.Exact (C.d (-1) 0 (by decide)) (C.d 0 1 rfl)
    intro c
    constructor
    · intro hc
      have hinv := (contD_zero_eq_zero_iff c).1 hc
      have ht := globalFixedTate_zero W hFull (cfun c default) hinv
      have hc0 : c = 0 := by
        rw [eq_constCochain c, ht]
        rfl
      exact ⟨0, by rw [hc0, map_zero]⟩
    · rintro ⟨y, rfl⟩
      exact C.d_d _ _ _ _ _ y
  exact ModuleCat.isZero_iff_subsingleton.1 ((C.toCC.exactAt_iff_isZero_homology 0).1 he)

/-- The compact Kummer Selmer cone has zero zeroth cohomology. -/
theorem compactKummer_homology_zero : Subsingleton ((compactKummerComplex S W hFull).homology 0) := by
  let D := tateKummerSelData S W hFull
  let C := selCx D
  let : Subsingleton (D.G.toCC.homology 0) := globalTate_homology_zero W hFull
  have hGexact := (D.G.toCC.exactAt_iff_isZero_homology 0).2 (ModuleCat.isZero_of_subsingleton _)
  have hG := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((D.G.toCC.exactAt_iff' (-1) 0 1 (by simp) (by simp)).1 hGexact)
  change Function.Exact (D.G.toCC.sc' (-1) 0 1).f.hom (D.G.toCC.sc' (-1) 0 1).g.hom at hG
  rw [sc'_f_hom D.G (-1) 0 1 (by decide), sc'_g_hom D.G (-1) 0 1 rfl] at hG
  change Function.Exact (D.G.d (-1) 0 (by decide)) (D.G.d 0 1 rfl) at hG
  let : Subsingleton (D.G.X (-1)) := inferInstanceAs (Subsingleton PUnit.{1})
  let : Subsingleton (D.L.X (0 - 1)) := by
    change Subsingleton (∀ v : Places K S, PUnit.{1})
    infer_instance
  have he : C.toCC.ExactAt 0 := by
    apply (C.toCC.exactAt_iff' (-1) 0 1 (by simp) (by simp)).2
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    change Function.Exact (C.toCC.sc' (-1) 0 1).f.hom (C.toCC.sc' (-1) 0 1).g.hom
    rw [sc'_f_hom C (-1) 0 1 (by decide), sc'_g_hom C (-1) 0 1 rfl]
    change Function.Exact (C.d (-1) 0 (by decide)) (C.d 0 1 rfl)
    intro x
    constructor
    · intro hx
      have hg : D.G.d 0 1 rfl x.1 = 0 := congrArg Prod.fst hx
      obtain ⟨y, hy⟩ := (hG x.1).1 hg
      have hy0 : y = 0 := Subsingleton.elim _ _
      have hg0 : x.1 = 0 := by simpa only [hy0, map_zero] using hy.symm
      have hl0 : x.2.2 = 0 := Subsingleton.elim _ _
      have hu := congrArg (fun z : C.X 1 => z.2.2) hx
      change D.res.f 0 0 rfl x.1 - D.ι.f 0 0 rfl x.2.1 - D.L.d (-1) 0 (by decide) x.2.2 = 0 at hu
      simp only [hg0, hl0, map_zero, zero_sub, sub_zero, neg_eq_zero] at hu
      have hu0 : x.2.1 = 0 := by
        funext v
        apply tateKummerLocalConditions_injective S W hFull v 0
        exact (congrFun hu v).trans (map_zero _).symm
      have hx0 : x = 0 := Prod.ext hg0 (Prod.ext hu0 hl0)
      exact ⟨0, by rw [hx0, map_zero]⟩
    · rintro ⟨y, rfl⟩
      exact C.d_d _ _ _ _ _ y
  exact ModuleCat.isZero_iff_subsingleton.1 ((C.toCC.exactAt_iff_isZero_homology 0).1 he)

end TateInvariants

/-!
# Integral ranks of dual complexes

Over a principal ideal domain, Smith normal form proves that a map between
finite free modules and its dual have equal image ranks.  Rank-nullity then
identifies the cohomology ranks of a dual complex, without choosing or
assuming the ranks of any cohomology group.
-/

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.Finiteness

section DualMaps

variable {R M N : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Free R N] [Module.Finite R N]

/-- Smith normal form gives equality of the integral image ranks of a map
and its dual.  The source need not be finite or free. -/
theorem finrank_range_dualMap_pid (f : M →ₗ[R] N) :
    Module.finrank R (LinearMap.range f.dualMap) = Module.finrank R (LinearMap.range f) := by
  classical
  let I := LinearMap.range f
  let B := I.smithNormalForm (Module.finBasis R N)
  have ha (j : Fin B.1) : B.2.a j ≠ 0 := by
    intro hj
    have h := B.2.snf j
    rw [hj, zero_smul] at h
    exact B.2.bN.ne_zero j (Subtype.ext h)
  let L : (Fin B.1 → R) →ₗ[R] (Fin (Module.finrank R N) → R) :=
    LinearMap.pi fun k => if h : ∃ j, B.2.f j = k then LinearMap.proj h.choose else 0
  have hL (r : Fin B.1 → R) (j : Fin B.1) : L r (B.2.f j) = r j := by
    have h : ∃ k, B.2.f k = B.2.f j := ⟨j, rfl⟩
    have hj : h.choose = j := B.2.f.injective h.choose_spec
    simp only [L, LinearMap.pi_apply]
    rw [dif_pos h, hj]
    rfl
  let F : (Fin B.1 → R) →ₗ[R] Module.Dual R N := (B.2.bM.constr R).toLinearMap.comp L
  let E := I.subtype.dualMap
  have hF (r : Fin B.1 → R) (j : Fin B.1) : E (F r) (B.2.bN j) = B.2.a j * r j := by
    change (B.2.bM.constr R (L r)) ((B.2.bN j : I) : N) = _
    rw [B.2.snf j, map_smul, Module.Basis.constr_basis, hL]
    rfl
  have hinj : Function.Injective (E.comp F) := by
    apply (injective_iff_map_eq_zero _).2
    intro r hr
    funext j
    have h := congrArg (fun q : Module.Dual R I => q (B.2.bN j)) hr
    change E (F r) (B.2.bN j) = 0 at h
    rw [hF] at h
    exact (mul_eq_zero.1 h).resolve_left (ha j)
  have hI : Module.finrank R I = B.1 := by
    rw [Module.finrank_eq_card_basis B.2.bN, Fintype.card_fin]
  have hdual : Module.finrank R (Module.Dual R I) = B.1 :=
    B.2.bN.toDualEquiv.finrank_eq.symm.trans hI
  have hupper : Module.finrank R (LinearMap.range E) ≤ B.1 :=
    (Submodule.finrank_le _).trans_eq hdual
  have hlower : B.1 ≤ Module.finrank R (LinearMap.range E) := by
    calc
      B.1 = Module.finrank R (LinearMap.range (E.comp F)) := by
        rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi, Fintype.card_fin]
      _ ≤ Module.finrank R (LinearMap.range E) :=
        Submodule.finrank_mono (LinearMap.range_comp_le_range F E)
  let D := f.rangeRestrict.dualMap
  have hD : Function.Injective D := by
    intro a b hab
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := f.surjective_rangeRestrict x
    exact LinearMap.congr_fun hab y
  have hfactor : f.dualMap = D.comp E := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro x
    rfl
  rw [hfactor, LinearMap.range_comp]
  calc
    Module.finrank R (Submodule.map D (LinearMap.range E)) = Module.finrank R (LinearMap.range E) :=
      (Submodule.equivMapOfInjective D hD (LinearMap.range E)).finrank_eq.symm
    _ = B.1 := le_antisymm hupper hlower
    _ = Module.finrank R (LinearMap.range f) := hI.symm

end DualMaps

section Signs

variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Multiplying a differential by its dual-complex sign leaves its image unchanged. -/
theorem range_dual_sign (f : M →ₗ[R] N) (n : ℤ) :
    LinearMap.range ((-(sgn n)) • f) = LinearMap.range f := by
  ext y
  rw [LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(-(sgn n)) • x, by rw [map_zsmul]; rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(-(sgn n)) • x, ?_⟩
    change (-(sgn n)) • f ((-(sgn n)) • x) = f x
    rw [map_zsmul, smul_smul, neg_mul_neg, sgn_mul_self, one_smul]

end Signs

section CohomologyRanks

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Re-indexing a differential along equal degrees preserves its image rank. -/
theorem differential_range_finrank_congr (C : GCx R) {i j i' j' : ℤ}
    (hi : i = i') (hj : j = j') (h : i + 1 = j) (h' : i' + 1 = j') :
    Module.finrank R (LinearMap.range (C.d i j h)) =
      Module.finrank R (LinearMap.range (C.d i' j' h')) := by
  cases hi
  cases hj
  rfl

/-- Rank-nullity for cohomology over a principal ideal domain. -/
theorem homology_finrank_sum (C : GCx R) (n : ℤ) [Module.Finite R (C.X n)] :
    Module.finrank R (C.toCC.homology n) +
      Module.finrank R (LinearMap.range (C.d (n - 1) n (by omega))) +
      Module.finrank R (LinearMap.range (C.d n (n + 1) rfl)) = Module.finrank R (C.X n) := by
  let f := C.d (n - 1) n (by omega)
  let g := C.d n (n + 1) rfl
  let B := LinearMap.range f
  let K := LinearMap.ker g
  have hBK : B ≤ K := by
    rintro x ⟨y, rfl⟩
    exact C.d_d _ _ _ _ _ y
  have hB : Module.finrank R (B.comap K.subtype) = Module.finrank R B :=
    (Submodule.comapSubtypeEquivOfLe hBK).finrank_eq
  have hQ := (B.comap K.subtype).finrank_quotient_add_finrank
  change Module.finrank R (K ⧸ B.comap K.subtype) + Module.finrank R (B.comap K.subtype) =
    Module.finrank R K at hQ
  have hg := g.finrank_range_add_finrank_ker
  have hH : Module.finrank R (C.toCC.homology n) = Module.finrank R (K ⧸ B.comap K.subtype) := by
    let e := gcxHomologyEquiv C (n - 1) n (n + 1) (by omega) rfl
    rw [sc'_f_hom C (n - 1) n (n + 1) (by omega), sc'_g_hom C (n - 1) n (n + 1) rfl] at e
    exact e.finrank_eq
  rw [hH]
  change Module.finrank R (K ⧸ B.comap K.subtype) + Module.finrank R B +
    Module.finrank R (LinearMap.range g) = Module.finrank R (C.X n)
  calc
    Module.finrank R (K ⧸ B.comap K.subtype) + Module.finrank R B +
        Module.finrank R (LinearMap.range g) =
      Module.finrank R (K ⧸ B.comap K.subtype) + Module.finrank R (B.comap K.subtype) +
        Module.finrank R (LinearMap.range g) := by rw [hB]
    _ = Module.finrank R K + Module.finrank R (LinearMap.range g) := by rw [hQ]
    _ = Module.finrank R (LinearMap.range g) + Module.finrank R K := Nat.add_comm _ _
    _ = Module.finrank R (C.X n) := by simpa only [K] using hg

/-- The integral cohomology ranks of the dual complex are the reflected
ranks of the original finite free complex. -/
theorem dualCx_homology_finrank (C : GCx R)
    [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)] (m n : ℤ) :
    Module.finrank R ((dualCx C m).toCC.homology n) = Module.finrank R (C.toCC.homology (m - n)) := by
  let : ∀ j, Module.Free R ((dualCx C m).X j) := fun j =>
    inferInstanceAs (Module.Free R (Module.Dual R (C.X (m - j))))
  let : ∀ j, Module.Finite R ((dualCx C m).X j) := fun j =>
    inferInstanceAs (Module.Finite R (Module.Dual R (C.X (m - j))))
  have hprev : Module.finrank R (LinearMap.range ((dualCx C m).d (n - 1) n (by omega))) =
      Module.finrank R (LinearMap.range (C.d (m - n) (m - n + 1) rfl)) := by
    change Module.finrank R (LinearMap.range ((-(sgn (n - 1))) •
      (C.d (m - n) (m - (n - 1)) (by omega)).dualMap)) = _
    rw [range_dual_sign, finrank_range_dualMap_pid]
    have hj : m - (n - 1) = m - n + 1 := by omega
    exact differential_range_finrank_congr C rfl hj _ _
  have hnext : Module.finrank R (LinearMap.range ((dualCx C m).d n (n + 1) rfl)) =
      Module.finrank R (LinearMap.range (C.d (m - n - 1) (m - n) (by omega))) := by
    change Module.finrank R (LinearMap.range ((-(sgn n)) •
      (C.d (m - (n + 1)) (m - n) (by omega)).dualMap)) = _
    rw [range_dual_sign, finrank_range_dualMap_pid]
    have hi : m - (n + 1) = m - n - 1 := by omega
    exact differential_range_finrank_congr C hi rfl _ _
  have hterm : Module.finrank R ((dualCx C m).X n) = Module.finrank R (C.X (m - n)) := by
    change Module.finrank R (Module.Dual R (C.X (m - n))) = _
    exact (Module.finBasis R (C.X (m - n))).toDualEquiv.finrank_eq.symm
  have hD := homology_finrank_sum (dualCx C m) n
  rw [hprev, hnext, hterm] at hD
  have hC := homology_finrank_sum C (m - n)
  omega

end CohomologyRanks

/-!
# The central cohomology shape and its integral calibration model

The rank-one assumption is the full Selmer assumption of
`diophantine_zq.tex`, lines 4332--4352 and 5264--5312, not a Mordell--Weil
rank assertion and not a finiteness assumption on the Shafarevich--Tate group.
The specified curve is bound to the actual central twist before the
universal-coefficient comparison is used.

The remaining integral-duality comparison is stated on the constructed
finite free model of the genuine compact complex.  Its mathematical
content is the integral Kummer self-duality
C_K ≃ RHom_Z₂(C_K,Z₂)[-3], after the Weil pairing and the derived Kummer
orthogonality identifications.  The locator is Nekovář, Selmer complexes,
Theorem 6.3.4, p. 143, in the setting of 6.2.5(B), pp. 139--140.
The finite-coefficient global duality statement alone does not construct
this integral comparison.  Neither a cohomology rank nor a disk order is
included in the comparison input.
-/

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Manuscript.RC53Assist.CentralUniversal
open ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.BaseZeroLimit
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.RC53Assist.Finiteness
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open scoped Classical

section CurveTransport

variable {K : Type} [Field K] [NumberField K]

/-- Equal geometric curves give the same compact Kummer complex;
ellipticity and full-torsion witnesses are proofs. -/
theorem compactKummerComplex_curve_congr (S : Set (HeightOneSpectrum (𝓞 K)))
    (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic] (hW : W = W')
    (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
    (hFull' : ∀ n : ℕ, FullTorsion K S W' (2 ^ n)) :
    compactKummerComplex S W hFull = compactKummerComplex S W' hFull' := by
  cases hW
  rfl

end CurveTransport

/-- Equal cohomological degrees have equal integral ranks. -/
theorem cohomology_finrank_degree_congr {R : Type} [CommRing R]
    (C : CochainComplex (ModuleCat.{0} R) ℤ) {i j : ℤ} (h : i = j) :
    Module.finrank R (C.homology i) = Module.finrank R (C.homology j) := by
  cases h
  rfl

section CentralModel

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (D : GenuineKummerData K E₀ hZ)

/-- Finite generation for the actual compact central twist, from the two finiteness prints. -/
theorem centralCohomologyFinite (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S) :
    ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n) :=
  moduleFinite_compactKummer_homology D.S (centralCurve D) (centralFullTorsion D)
    hloc hglob D.hSfin h2

/-- The integral compact central cohomology is supported in degrees one through three. -/
theorem compactCentral_outside (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve D).toAffine.Point 2)]
    (n : ℤ) (hn : n < 1 ∨ 3 < n) : Subsingleton ((compactCentralComplex D).homology n) := by
  rw [compactCentralComplex_eq]
  rcases hn with hn | hn
  · by_cases hneg : n < 0
    · exact compactKummer_homology_negative (centralCurve D) (centralFullTorsion D) n hneg
    · have hzero : n = 0 := by omega
      subst n
      exact compactKummer_homology_zero (centralCurve D) (centralFullTorsion D)
  · exact compactKummer_homology_high (centralCurve D) (centralFullTorsion D)
      hloc hglob hlocal hglobal hK D.hSfin h2 n hn

variable (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))

/-- The relation-indexed version of the retained integral central model. -/
abbrev centralRetainedGCx : GCx ℤ_[2] :=
  resolutionGCx (compactCentralComplex D)
    (fun n => (chosenPresentations (compactCentralComplex D) hfinite n).toFreeResolution)

/-- Its cochain-complex form is exactly the retained central complex. -/
theorem centralRetainedGCx_toCC : (centralRetainedGCx D hfinite).toCC =
    retainedCentralComplex D hfinite := rfl

/-- Every term of this model is finite free. -/
theorem centralRetainedGCx_terms (n : ℤ) :
    Module.Free ℤ_[2] ((centralRetainedGCx D hfinite).X n) ∧
      Module.Finite ℤ_[2] ((centralRetainedGCx D hfinite).X n) :=
  retainedCentralComplex_finite_free D hfinite n

/-- Cohomological support gives the bounded support of the retained free model. -/
theorem centralRetainedGCx_bounded
    (hout : ∀ n : ℤ, n < 1 ∨ 3 < n → Subsingleton ((compactCentralComplex D).homology n))
    (n : ℤ) (hn : n < 0 ∨ 3 < n) : Subsingleton ((centralRetainedGCx D hfinite).X n) := by
  have h₁ := (chosenDiagonalResolution_zero (hfinite n) (hout n (by omega))).1
  have h₂ := (chosenDiagonalResolution_zero (hfinite (n + 1)) (hout (n + 1) (by omega))).2
  change Subsingleton ((Fin (chosenPresentations (compactCentralComplex D) hfinite n).generators → ℤ_[2]) ×
    (Fin (chosenPresentations (compactCentralComplex D) hfinite (n + 1)).relations → ℤ_[2]))
  dsimp only [chosenPresentations]
  rw [h₁, h₂]
  infer_instance

/-- The termwise dual of the bounded retained free model computes derived Hom. -/
theorem centralRetainedGCx_computesRHom
    (hout : ∀ n : ℤ, n < 1 ∨ 3 < n → Subsingleton ((compactCentralComplex D).homology n)) :
    TermwiseDualComputesRHom ℤ_[2] (centralRetainedGCx D hfinite) := by
  refine Or.inr ⟨0, 3, centralRetainedGCx_bounded D hfinite hout, fun n => ?_⟩
  let := (centralRetainedGCx_terms D hfinite n).1
  exact ⟨inferInstance, (centralRetainedGCx_terms D hfinite n).2⟩

/-- The precise remaining integral Kummer-duality comparison.
It identifies the entire retained integral complex with its derived dual,
not merely its rational dimensions. -/
def IntegralCentralKummerDuality : Prop :=
  Nonempty (HomotopyEquiv (centralRetainedGCx D hfinite).toCC
    (dualCx (centralRetainedGCx D hfinite) 3).toCC)

/-- Integral Kummer self-duality identifies the reflected integral cohomology ranks. -/
theorem integralCentralDuality_ranks (hdual : IntegralCentralKummerDuality D hfinite) (n : ℤ) :
    Module.finrank ℤ_[2] ((compactCentralComplex D).homology n) =
      Module.finrank ℤ_[2] ((compactCentralComplex D).homology (3 - n)) := by
  obtain ⟨e⟩ := hdual
  let : ∀ j, Module.Free ℤ_[2] ((centralRetainedGCx D hfinite).X j) :=
    fun j => (centralRetainedGCx_terms D hfinite j).1
  let : ∀ j, Module.Finite ℤ_[2] ((centralRetainedGCx D hfinite).X j) :=
    fun j => (centralRetainedGCx_terms D hfinite j).2
  have := retainedCentralComparison_quasiIso D hfinite
  have := e.quasiIso_hom
  calc
    Module.finrank ℤ_[2] ((compactCentralComplex D).homology n) =
        Module.finrank ℤ_[2] ((centralRetainedGCx D hfinite).toCC.homology n) :=
      (asIso (HomologicalComplex.homologyMap (retainedCentralComparison D hfinite) n)).toLinearEquiv.finrank_eq.symm
    _ = Module.finrank ℤ_[2] ((dualCx (centralRetainedGCx D hfinite) 3).toCC.homology n) :=
      (asIso (HomologicalComplex.homologyMap e.hom n)).toLinearEquiv.finrank_eq
    _ = Module.finrank ℤ_[2] ((centralRetainedGCx D hfinite).toCC.homology (3 - n)) :=
      dualCx_homology_finrank (centralRetainedGCx D hfinite) 3 n
    _ = Module.finrank ℤ_[2] ((compactCentralComplex D).homology (3 - n)) :=
      (asIso (HomologicalComplex.homologyMap (retainedCentralComparison D hfinite) (3 - n))).toLinearEquiv.finrank_eq

end CentralModel

section ArithmeticRank

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (D : GenuineKummerData (QuadraticField k) E₀ hZ)
  (hcurve : centralCurve D = (Ecurve ℓ).baseChange (QuadraticField k))

local instance (priority := 10000) arithmeticFieldDecidableEq : DecidableEq (QuadraticField k) :=
  fun a b => Classical.propDecidable (a = b)

include hcurve

/-- Full torsion transported along the actual geometric curve binding. -/
theorem arithmeticCentralFull : ∀ n : ℕ, FullTorsion (QuadraticField k) D.S
    ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n) :=
  fun n => hcurve ▸ centralFullTorsion D n

/-- The compact central complex is the genuine arithmetic compact Kummer complex. -/
theorem compactCentral_eq_arithmetic : compactCentralComplex D =
    arithmeticCompactComplex ℓ k D.S (arithmeticCentralFull ℓ k D hcurve) := by
  rw [compactCentralComplex_eq]
  exact compactKummerComplex_curve_congr D.S (centralCurve D)
    ((Ecurve ℓ).baseChange (QuadraticField k)) hcurve (centralFullTorsion D)
      (arithmeticCentralFull ℓ k D hcurve)

variable (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))

include hfinite

/-- The two finite-generation inputs of the universal-coefficient map are supplied integrally. -/
theorem arithmeticCentralFinite :
    KummerCohomologyFinite ℓ k D.S (arithmeticCentralFull ℓ k D hcurve) where
  finite_one := by rw [← compactCentral_eq_arithmetic ℓ k D hcurve]; exact hfinite 1
  finite_two := by rw [← compactCentral_eq_arithmetic ℓ k D hcurve]; exact hfinite 2

include hfinite in
/-- Under full Selmer corank one, the actual integral central first-cohomology rank is one. -/
theorem compactCentral_rank_one (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparison ℓ k D.S (arithmeticCentralFull ℓ k D hcurve))
    (hSel : SelmerCorankOneOverK ℓ k) :
    Module.finrank ℤ_[2] ((compactCentralComplex D).homology 1) = 1 := by
  have h := arithmeticRank_eq_one ℓ k D.S (arithmeticCentralFull ℓ k D hcurve) hk I
    (arithmeticCentralFinite ℓ k D hcurve hfinite) hSel
  have hr : arithmeticRank ℓ k D.S (arithmeticCentralFull ℓ k D hcurve) =
      Module.finrank ℤ_[2] ((arithmeticCompactComplex ℓ k D.S
        (arithmeticCentralFull ℓ k D hcurve)).homology 1) :=
    finrank_quotient_eq_of_le_torsion (le_refl _)
  rw [compactCentral_eq_arithmetic ℓ k D hcurve]
  exact hr.symm.trans h

/-- The two calibration inputs are reduced to named arithmetic statements,
with no calibration shape and no canonical-reduction quasi-isomorphism as inputs. -/
theorem calibrationShape_of_arithmetic (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex (QuadraticField k))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ D.S)
    [hpt : Finite (AddCommGroup.primaryComponent (centralCurve D).toAffine.Point 2)]
    (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparison ℓ k D.S (arithmeticCentralFull ℓ k D hcurve))
    (hSel : SelmerCorankOneOverK ℓ k) (hdual : IntegralCentralKummerDuality D hfinite) :
    CalibrationCohomologyShape (compactCentralComplex D) := by
  let : Finite (AddCommGroup.primaryComponent (centralCurve D).toAffine.Point 2) := hpt
  have hout : ∀ n : ℤ, n < 1 ∨ 3 < n → Subsingleton ((compactCentralComplex D).homology n) :=
    @compactCentral_outside (QuadraticField k) _ _ E₀ hZ D hloc hglob hlocal hglobal hK h2 hpt
  refine ⟨hout, compactCentral_rank_one ℓ k D hcurve hfinite hk I hSel, ?_, ?_⟩
  · have h : Module.finrank ℤ_[2] ((compactCentralComplex D).homology 2) =
        Module.finrank ℤ_[2] ((compactCentralComplex D).homology 1) :=
      (integralCentralDuality_ranks D hfinite hdual 2).trans
        (cohomology_finrank_degree_congr (compactCentralComplex D) (by decide))
    exact h.trans (compactCentral_rank_one ℓ k D hcurve hfinite hk I hSel)
  · have h : Module.finrank ℤ_[2] ((compactCentralComplex D).homology 3) =
        Module.finrank ℤ_[2] ((compactCentralComplex D).homology 0) :=
      (integralCentralDuality_ranks D hfinite hdual 3).trans
        (cohomology_finrank_degree_congr (compactCentralComplex D) (by decide))
    let : Subsingleton ((compactCentralComplex D).homology 0) := hout 0 (by omega)
    exact h.trans Module.finrank_zero_of_subsingleton

/-- Assemble the retained integral block model, using the proved canonical reductions. -/
def integralCentralModel_of_arithmetic (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex (QuadraticField k))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ D.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve D).toAffine.Point 2)]
    (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparison ℓ k D.S (arithmeticCentralFull ℓ k D hcurve))
    (hSel : SelmerCorankOneOverK ℓ k) (hdual : IntegralCentralKummerDuality D hfinite) :
    IntegralBlockCentralModel D (centralDiskMatrix D hfinite 1) (centralDiskMatrix D hfinite 2)
      (centralDiskMatrix D hfinite 3) :=
  integralBlockCentralModel D hfinite
    (calibrationShape_of_arithmetic ℓ k D hcurve hfinite hloc hglob hlocal hglobal hK h2 hk I hSel hdual)
    (fun i _ => canonicalCentralReductionMap_quasiIso D i)

/-- The resulting DiskTie statement for the actual finite central Selmer complexes. -/
theorem diskTie_of_arithmetic (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex (QuadraticField k))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ D.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve D).toAffine.Point 2)]
    (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparison ℓ k D.S (arithmeticCentralFull ℓ k D hcurve))
    (hSel : SelmerCorankOneOverK ℓ k) (hdual : IntegralCentralKummerDuality D hfinite) :
    DiskTie D (centralDiskMatrix D hfinite 1).det (centralDiskMatrix D hfinite 2).det
      (centralDiskMatrix D hfinite 3).det :=
  (integralCentralModel_of_arithmetic ℓ k D hcurve hfinite hloc hglob hlocal hglobal hK h2 hk I hSel hdual).diskTie

end ArithmeticRank

end ZInQ.Contrib.RC53Assist.CalibrationShape
