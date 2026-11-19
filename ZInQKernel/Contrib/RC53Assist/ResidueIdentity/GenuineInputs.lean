import ZInQKernel.Contrib.RC53Assist.ResidueIdentity.Arithmetic
import ZInQKernel.Contrib.RC53Assist.ResidueIdentity.Characters
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.ArithLabel
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.FiniteLevel

/-!
# Arithmetic inputs on the actual local coefficient modules

The coefficient-stage Frobenius congruence supplies trivial local action
through the actual unramified quotient. A degree-two coordinate on the
rank-two module supplies the scalar twist coordinate by a coefficient
retraction. Both maps use the same tame orientation. The original local
invariant can therefore be produced rather than separately postulated
(tex 2723–2727, 2762–2767, 3090–3096, 4385–4451, 4860–4863, 5027–5043).
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.ResidueIdentity.Genuine

open CategoryTheory Module Filter NumberField IsDedekindDomain
open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.RC53Assist.ResidueIdentity
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open scoped Matrix TensorProduct WeierstrassCurve PowerSeries.WithPiTopology

section CoefficientRetract

variable {R G M N : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [AddCommGroup N] [Module R N] [DistribMulAction G N] [SMulCommClass G R N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Kind: proved theorem. Applying coefficient homomorphisms twice is
pointwise composition on the actual continuous cochains
(tex 2762–2767, 4860–4863). -/
theorem coefficientMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] M) (p : ℕ)
    (z : (contCochains R G N).X p) :
    coefficientMap f p (coefficientMap g p z) = coefficientMap (f.comp g) p z := by
  apply contCochains_ext
  intro v
  rfl

/-- Kind: definition. A coefficient retraction of the original degree-two
coordinate gives the scalar twist coordinate on actual local cochains
(tex 2762–2767, 4860–4863). -/
def retractCoordinate (cM : (contCochains R G M).X 2 →ₗ[R] M)
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) : (contCochains R G N).X 2 →ₗ[R] N :=
  f.comp (cM.comp (coefficientMap g 2))

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Kind: proved theorem. The coefficient retraction preserves the
positive uniformizer-cup normalization (tex 2762–2767, 4860–4863). -/
theorem retractCoordinate_normalized
    (cM : (contCochains R G M).X 2 →ₗ[R] M)
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (hfg : ∀ x, f (g x) = x)
    (u κ : G → R) (hn : LocalDegreeTwoNormalized cM u κ) :
    LocalDegreeTwoNormalized (retractCoordinate cM f g) u κ := by
  intro m z hz
  change f (cM (coefficientMap g 2 z)) = m
  rw [hn (g m) (coefficientMap g 2 z) (by
    intro a b
    change g (evalTwo R N a b z) = (u a * κ b) • g m
    rw [hz, map_smul]), hfg]

/-- Kind: proved theorem. A coefficient direct summand inherits the
actual degree-two coordinate, including kernel exactness and surjectivity
on two-cocycles. No scalar coordinate is assumed
(tex 2762–2767, 4860–4863). -/
theorem retractCoordinate_spec
    (cM : (contCochains R G M).X 2 →ₗ[R] M) (hc : LocalDegreeTwoCoordinate cM)
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (hfg : ∀ x, f (g x) = x)
    (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (hua : ∀ a b, u (a * b) = u a + u b)
    (hκa : ∀ a b, κ (a * b) = κ a + κ b)
    (hM : ∀ (a : G) (m : M), a • m = m)
    (hN : ∀ (a : G) (m : N), a • m = m)
    (hn : LocalDegreeTwoNormalized cM u κ) :
    LocalDegreeTwoCoordinate (retractCoordinate cM f g) := by
  have hfgMap (p : ℕ) (z : (contCochains R G N).X p) :
      coefficientMap f p (coefficientMap g p z) = z := by
    apply contCochains_ext
    intro v
    exact hfg _
  have hnorm := retractCoordinate_normalized cM f g hfg u κ hn
  refine ⟨?_, ?_, ?_⟩
  · intro a
    change f (cM (coefficientMap g 2 (((contCochains R G N).d 1 2).hom a))) = 0
    rw [coefficientMap_d12 g hN hM, hc.1, map_zero]
  · intro z hz hzero
    let zm := coefficientMap g 2 z
    have hzm : ((contCochains R G M).d 2 3).hom zm = 0 := by
      rw [← coefficientMap_d23 g hN hM, hz, map_zero]
    have hfix : cM zm = g (f (cM zm)) := by
      have he : coefficientMap (g.comp f) 2 zm = zm := by
        apply contCochains_ext
        intro v
        change g (f (g (contFun z v))) = g (contFun z v)
        rw [hfg]
      have hv := coefficientMap_coordinate cM cM hc hc.1 u κ hu hκ hua hκa hM hM
        hn hn (g.comp f) zm hzm
      rw [he] at hv
      exact hv
    have hmzero : cM zm = 0 := by
      change f (cM zm) = 0 at hzero
      rw [hfix, hzero, map_zero]
    obtain ⟨a, ha⟩ := hc.2.1 zm hzm hmzero
    refine ⟨coefficientMap f 1 a, ?_⟩
    rw [← coefficientMap_d12 f hM hN, ha]
    exact hfgMap 2 z
  · intro m
    refine ⟨characterProduct u κ hu hκ m,
      characterProduct_cycle u κ hu hκ hN hua hκa m, ?_⟩
    exact hnorm m _ (characterProduct_eval u κ hu hκ m)

/-- Kind: definition. Projection from the actual rank-two coefficient
frame to the scalar twist frame (tex 2762–2767, 4860–4863). -/
def scalarProjection (eM : M ≃ₗ[R] (Fin 2 → R)) (eN : N ≃ₗ[R] R) : M →ₗ[R] N :=
  eN.symm.toLinearMap.comp ((LinearMap.proj 0).comp eM.toLinearMap)

/-- Kind: definition. The first coefficient axis embeds the scalar twist
as a direct summand of the actual coefficient module
(tex 2762–2767, 4860–4863). -/
def scalarInclusion (eM : M ≃ₗ[R] (Fin 2 → R)) (eN : N ≃ₗ[R] R) : N →ₗ[R] M :=
  eM.symm.toLinearMap.comp ((LinearMap.single R (fun _ : Fin 2 => R) 0).comp eN.toLinearMap)

omit [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace M] [DiscreteTopology M]
  [TopologicalSpace N] [DiscreteTopology N] in
/-- Kind: proved theorem. The scalar coefficient maps are an exact
coefficient retraction (tex 2762–2767, 4860–4863). -/
theorem scalarProjection_inclusion (eM : M ≃ₗ[R] (Fin 2 → R)) (eN : N ≃ₗ[R] R) (m : N) :
    scalarProjection eM eN (scalarInclusion eM eN m) = m := by
  change eN.symm ((eM (eM.symm (Pi.single 0 (eN m)))) 0) = m
  rw [eM.apply_symm_apply, Pi.single_eq_same, eN.symm_apply_apply]

/-- Kind: definition. The scalar degree-two coordinate constructed from
the original rank-two coordinate (tex 2762–2767, 4860–4863). -/
def scalarCoordinateFromPlane
    (cM : (contCochains R G M).X 2 →ₗ[R] M)
    (eM : M ≃ₗ[R] (Fin 2 → R)) (eN : N ≃ₗ[R] R) :
    (contCochains R G N).X 2 →ₗ[R] N :=
  retractCoordinate cM (scalarProjection eM eN) (scalarInclusion eM eN)

/-- Kind: definition. The scalar local trace read through the actual
scalar twist frame and constructed coordinate
(tex 2762–2767, 4385–4388, 4860–4863). -/
def scalarTraceFromPlane
    (cM : (contCochains R G M).X 2 →ₗ[R] M)
    (eM : M ≃ₗ[R] (Fin 2 → R)) (eN : N ≃ₗ[R] R) :
    (contCochains R G N).X 2 →ₗ[R] R :=
  eN.toLinearMap.comp (scalarCoordinateFromPlane cM eM eN)

/-- Kind: proved theorem. The constructed original local trace kills
coboundaries and is onto on actual two-cocycles
(tex 2762–2767, 4385–4388, 4860–4863). -/
theorem scalarTraceFromPlane_spec
    (cM : (contCochains R G M).X 2 →ₗ[R] M) (hc : LocalDegreeTwoCoordinate cM)
    (eM : M ≃ₗ[R] (Fin 2 → R)) (eN : N ≃ₗ[R] R)
    (u κ : G → R) (hu : Continuous u) (hκ : Continuous κ)
    (hua : ∀ a b, u (a * b) = u a + u b)
    (hκa : ∀ a b, κ (a * b) = κ a + κ b)
    (hM : ∀ (a : G) (m : M), a • m = m)
    (hN : ∀ (a : G) (m : N), a • m = m)
    (hn : LocalDegreeTwoNormalized cM u κ) :
    (∀ a, scalarTraceFromPlane cM eM eN (((contCochains R G N).d 1 2).hom a) = 0) ∧
      ∀ r : R, ∃ z, ((contCochains R G N).d 2 3).hom z = 0 ∧
        scalarTraceFromPlane cM eM eN z = r := by
  have hcoord := retractCoordinate_spec cM hc (scalarProjection eM eN) (scalarInclusion eM eN)
    (scalarProjection_inclusion eM eN) u κ hu hκ hua hκa hM hN hn
  constructor
  · intro a
    change eN (retractCoordinate cM (scalarProjection eM eN) (scalarInclusion eM eN)
      (((contCochains R G N).d 1 2).hom a)) = 0
    rw [hcoord.1, map_zero]
  · intro r
    obtain ⟨z, hz, ht⟩ := hcoord.2.2 (eN.symm r)
    refine ⟨z, hz, ?_⟩
    change eN (retractCoordinate cM (scalarProjection eM eN) (scalarInclusion eM eN) z) = r
    rw [ht, eN.apply_symm_apply]

end CoefficientRetract

section ScalarCoefficient

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- Kind: proved theorem. The actual scalar twist coefficient module is
killed by its stage exponent (tex 2723–2727, 2762–2767). -/
theorem actualScalar_nsmul (i : ℕ) (q : HeightOneSpectrum (𝓞 K))
    (hμ : HasRootsOfUnity K S (2 ^ i)) (m : actualN i q hμ) : (2 ^ i) • m = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (Acoef i)]
  have hz : ((2 ^ i : ℕ) : Acoef i) = 0 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, acoef_two_pow_eq_zero]
  rw [hz]
  exact zero_smul (Acoef i) m

end ScalarCoefficient

section BrauerNaturality

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n]
  {R M N : Type} [CommRing R] [Algebra (ZMod n) R]
  [TopologicalSpace R] [DiscreteTopology R]
  [AddCommGroup M] [Module R M] [Module (ZMod n) M] [IsScalarTower (ZMod n) R M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) R M] [SMulCommClass R (ZMod n) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  [AddCommGroup N] [Module R N] [Module (ZMod n) N] [IsScalarTower (ZMod n) R N]
  [DistribMulAction (Field.absoluteGaloisGroup F) N]
  [SMulCommClass (Field.absoluteGaloisGroup F) R N] [SMulCommClass R (ZMod n) N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul (Field.absoluteGaloisGroup F) N]

omit [NeZero n] [TopologicalSpace R] [DiscreteTopology R]
  [SMulCommClass R (ZMod n) M] [SMulCommClass R (ZMod n) N] in
/-- Kind: proved theorem. A coefficient retraction preserves the actual
Brauer-invariant formula on every two-cocycle. The constructed scalar
coordinate is therefore an arithmetic invariant, not just an abstract
coordinate of the same dimension (tex 2762–2767, 4860–4863). -/
theorem retractCoordinate_brauerFormula
    (η : ZMod n ≃+ KummerCoeff F n)
    (hμ : ∀ (g : AbsoluteGaloisGroup F) (x : KummerCoeff F n), g • x = x)
    (hM : ∀ (g : Field.absoluteGaloisGroup F) (m : M), g • m = m)
    (hN : ∀ (g : Field.absoluteGaloisGroup F) (m : N), g • m = m)
    (cM : (contCochains R (Field.absoluteGaloisGroup F) M).X 2 →ₗ[R] M)
    (hbr : BrauerCoordinateFormula η hμ hM cM)
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (hfg : ∀ x, f (g x) = x) :
    BrauerCoordinateFormula η hμ hN (retractCoordinate cM f g) := by
  intro φ z hz
  let ψ : M →ₗ[ZMod n] ZMod n := φ.comp (f.restrictScalars (ZMod n))
  let zm := coefficientMap (G := Field.absoluteGaloisGroup F) g 2 z
  have hzm : ((contCochains R (Field.absoluteGaloisGroup F) M).d 2 3).hom zm = 0 := by
    rw [← coefficientMap_d23 g hN hM, hz, map_zero]
  have hs : scalarCochain ψ zm = scalarCochain φ z := by
    apply contCochains_ext
    intro v
    change φ (f (g (contFun z v))) = φ (contFun z v)
    rw [hfg]
  have hc := hbr ψ zm hzm
  have hker :
      (⟨scalarCochain ψ zm, scalarCochain_cycle hM ψ zm hzm⟩ :
        LinearMap.ker ((contCochains (ZMod n) (Field.absoluteGaloisGroup F)
          (ScalarCoeff (ZMod n))).d 2 3).hom) =
      ⟨scalarCochain φ z, scalarCochain_cycle hN φ z hz⟩ := Subtype.ext hs
  rw [hker] at hc
  exact hc

end BrauerNaturality

section DerivativeAction

open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (eUr frobElt denseRange_zpow)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [DistribMulAction (GKS K S) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]

/-- Kind: proved theorem. Trivial arithmetic Frobenius action on an
unramified actual coefficient module implies trivial action of the full
local Galois group. Both the unramified factor and Frobenius are the
original arithmetic label (tex 3090–3096, 4860–4863, 5027–5032). -/
theorem localAction_trivial_of_frobenius (L : MovingLabel K S) (i : ℕ)
    (hF : ∀ m : M, L.frob i • m = m)
    (g : Gloc K (L.q i)) (m : ResMod (locMap K S (L.q i)) M) : g • m = m := by
  have hp (z : ℤ) : L.ψ i (frobElt (eUr K (L.q i)) ^ z) • (show M from m) = m := by
    rw [map_zpow]
    change (L.frob i) ^ z • (show M from m) = m
    exact MulAction.mem_stabilizer_iff.mp
      (Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.mpr (hF m)) z)
  have he := (denseRange_zpow (eUr K (L.q i))).equalizer
    ((L.ψ i).continuous.smul continuous_const) continuous_const (funext hp)
  change locMap K S (L.q i) g • (show M from m) = m
  rw [L.hψ]
  exact congrFun he (urRes K (L.q i) g)

end DerivativeAction

section FiniteDerivativeAction

open ZInQ.Manuscript.RC.Uniform (Lambda)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (B : WeierstrassCurve ℚ) [B.IsElliptic] [HasFullTwoTorsion K S (B⁄K)]
  (α : GKS K S →* Lambdaˣ) [IsContChar α]
  (L : CompatibleArithmeticLabel B K S α)

omit [NumberField K] in
/-- Kind: proved theorem. Continuity of the original character makes its
actual finite reduction have open kernel (tex 2723–2727, 3090–3096). -/
theorem alphaLev_openKernel (i : ℕ) : IsOpenKer (alphaLev i α) := by
  let : TopologicalSpace (Acoef i) := ⊥
  let : DiscreteTopology (Acoef i) := ⟨rfl⟩
  have hc : Continuous (lamToAcoef i : Lambda → Acoef i) := by
    refine continuous_of_ker_mem_nhds (lamToAcoef i).toAddMonoidHom
      (Filter.mem_of_superset (lamIdeal_mem_nhds i) fun x hx => ?_)
    change lamToAcoef i x = 0
    rw [← RingHom.mem_ker, ker_lamToAcoef]
    exact hx
  have hcomp : Continuous (fun g : GKS K S => lamToAcoef i (α g : Lambda) - 1) :=
    (hc.comp (IsContChar.continuous_coe (α := α))).sub continuous_const
  have he : ((alphaLev i α).ker : Set (GKS K S)) =
      (fun g : GKS K S => lamToAcoef i (α g : Lambda) - 1) ⁻¹' {0} := by
    ext g
    change alphaLev i α g = 1 ↔ lamToAcoef i (α g : Lambda) - 1 = 0
    rw [Units.ext_iff, Units.val_one, coe_alphaLev, sub_eq_zero]
  refine ⟨?_⟩
  rw [he]
  exact (isOpen_discrete ({0} : Set (Acoef i))).preimage hcomp

omit [IsContChar α] in
/-- Kind: proved theorem. The genuine finite-level reduction sends the
actual derivative Frobenius congruence to exact trivial Frobenius action
on `M_i` (tex 2723–2727, 3090–3096, 5027–5032). -/
theorem actualStage_frobenius_trivial (i : ℕ)
    (m : Mcoef K S (B⁄K) i (alphaLev i α)) : L.label.frob i • m = m := by
  obtain ⟨x, rfl⟩ := finLev_surjective α (projLev_surjective i) m
  have hmem := tlamNbhd_le_ker_finLev α i (L.htriv i x)
  rw [LinearMap.mem_ker, map_sub, finLev_smul] at hmem
  exact sub_eq_zero.mp hmem

/-- Kind: proved theorem. The actual arithmetic label supplies trivial
local action on the full actual finite coefficient module, not merely on
its chosen Frobenius generator (tex 2723–2727, 3090–3096, 4860–4863). -/
theorem actualStage_local_action_trivial (i : ℕ)
    (g : Gloc K (L.label.q i))
    (m : actualM (B⁄K) i (alphaLev i α) (L.label.q i)) : g • m = m := by
  have : IsOpenKer (alphaLev i α) := alphaLev_openKernel α i
  exact localAction_trivial_of_frobenius L.label i (actualStage_frobenius_trivial B α L i) g m

end FiniteDerivativeAction

attribute [local instance] alphaLev_openKernel

section DoublePrecision

open ZInQ.Contrib.CloudB3RC53.TameQuotient
open ZInQ.Contrib.RC53Assist.ResidueIdentity.Characters

variable {F : Type} [Field F]

/-- Kind: proved theorem. If the square of a root has exact positive
 two-power order, the root has the next two-power order. This supplies
 compatibility of a chosen inertia generator at the extra precision
 (tex 3090–3096, 4860–4863). -/
theorem primitive_double_of_square (i : ℕ) [NeZero i] (ζ : F)
    (h : IsPrimitiveRoot (ζ ^ 2) (2 ^ i)) : IsPrimitiveRoot ζ (2 * (2 ^ i)) := by
  have hn : 0 < 2 ^ i := pow_pos (by decide) i
  have hpow : ζ ^ (2 * (2 ^ i)) = 1 := by rw [pow_mul, h.pow_eq_one]
  apply IsPrimitiveRoot.mk_of_lt ζ (by positivity) hpow
  intro l hl hlt hone
  have hdvd : 2 ^ i ∣ l := h.dvd_of_pow_eq_one l (by
    rw [← pow_mul, Nat.mul_comm 2 l, pow_mul, hone, one_pow])
  obtain ⟨k, hk⟩ := hdvd
  have hkone : k = 1 := by
    rw [hk] at hl hlt
    nlinarith
  have he : l = 2 ^ i := by simpa [hkone] using hk
  rw [he] at hone
  cases i with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ j =>
    have hne := h.pow_ne_one_of_pos_of_lt (pow_ne_zero j (by decide : (2 : ℕ) ≠ 0))
      (by rw [pow_succ]; nlinarith [pow_pos (by decide : 0 < (2 : ℕ)) j])
    apply hne
    rw [← pow_mul, Nat.mul_comm 2 (2 ^ j), ← pow_succ]
    exact hone

/-- Kind: proved theorem. Larger fixed-root precision supplies the
 retained fixed-root statement (tex 3090–3096, 4860–4863). -/
theorem fixedRoots_of_double (n : ℕ)
    (hμ : ∀ (g : Gal(AlgebraicClosure F/F)) (ζ : AlgebraicClosure F),
      ζ ^ (2 * n) = 1 → g ζ = ζ)
    (g : Gal(AlgebraicClosure F/F)) (ζ : AlgebraicClosure F) (hζ : ζ ^ n = 1) : g ζ = ζ := by
  apply hμ g ζ
  rw [Nat.mul_comm 2 n, pow_mul, hζ, one_pow]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Kind: proved theorem. Every existing normalized two-power tame
 orientation admits a continuous additive lift of its exact uniformizer
 character when roots of unity at twice the exponent are fixed. The
 existing root and inertia generator are preserved, not replaced by an
 unrelated orientation (tex 3090–3096, 4860–4863, 5027–5042). -/
theorem orientation_kummer_doubleLift (i : ℕ) [NeZero i]
    (D : TameOrientation F (2 ^ i))
    (hμ : ∀ (g : Gal(AlgebraicClosure F/F)) (ζ : AlgebraicClosure F),
      ζ ^ (2 * (2 ^ i)) = 1 → g ζ = ζ) :
    ∃ χ : Gal(AlgebraicClosure F/F) → ZMod (2 * (2 ^ i)),
      Continuous χ ∧ (∀ g h, χ (g * h) = χ g + χ h) ∧
        ∀ g, D.kummer g = ((χ g).val : ZMod (2 ^ i)) := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  have : NeZero (2 * (2 ^ i)) := ⟨mul_ne_zero two_ne_zero (pow_ne_zero i two_ne_zero)⟩
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq D.root (by decide : 0 < (2 : ℕ))
  have hγ0 : γ ≠ 0 := by
    intro hz
    rw [hz, zero_pow two_ne_zero] at hγ
    exact D.root_ne_zero hγ.symm
  have hp : γ ^ (2 * (2 ^ i)) =
      algebraMap F (AlgebraicClosure F) (D.uniformizer : F) := by
    rw [pow_mul, hγ]
    exact D.root_pow
  have hprim : IsPrimitiveRoot (kummerVal γ D.inertia) (2 * (2 ^ i)) := by
    apply primitive_double_of_square i
    rw [← kummerVal_square, hγ]
    exact D.primitive
  refine ⟨kummerLog hp hγ0 hprim, continuous_kummerLog hp hγ0 hprim hμ,
    kummerLog_mul hp hγ0 hprim hμ, ?_⟩
  intro g
  have hr := kummerLog_square_reduction hp hγ0 hprim g
  have hleft : kummerLog (squareRoot_power hp) (pow_ne_zero 2 hγ0)
      (squaredKummerPrimitive hprim) g = D.kummer g := by
    simp only [TameOrientation.kummer]
    congr 1
  have hr' : D.kummer g = reduceDouble (2 ^ i) (kummerLog hp hγ0 hprim g) := by
    rw [← hleft]
    exact hr
  exact hr'.trans (reduceDouble_val (2 ^ i) _)

end DoublePrecision

section ScalarLocalAction

open ZInQ.Contrib.CloudB3RC53.RankCounts (resAbs_apply_coe)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (i : ℕ) (q : HeightOneSpectrum (𝓞 K)) (hμ : HasRootsOfUnity K S (2 ^ i))

/-- Kind: proved theorem. The actual local decomposition map carries a
fixed local root to a fixed root in the global coefficient frame
(tex 2762–2767, 3090–3096). -/
theorem local_cyclotomic_eq_one
    (hfixed : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ) (g : Gloc K q) :
    cycS hμ (locMap K S q g) = 1 := by
  have : NeZero (2 ^ i) := ⟨pow_ne_zero i two_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := id hμ
  have hf : galS K S (locMap K S q g) ζ = ζ := by
    apply Subtype.ext
    apply (decompLift K q).injective
    have hl : (galS K S (locMap K S q g) ζ : AlgebraicClosure K) =
        @id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K q g)
          (ζ : AlgebraicClosure K) := by
      exact resAbs_apply_coe K S (decompMap K q g) ζ
    rw [hl, decompLift_decompMap]
    apply hfixed g
    rw [← map_pow]
    have hz : (ζ : AlgebraicClosure K) ^ (2 ^ i) = 1 := by
      exact_mod_cast hζ.pow_eq_one
    rw [hz, map_one]
  have hv := cycS_spec hμ (locMap K S q g) hζ.pow_eq_one
  rw [hf] at hv
  by_cases hn : i = 0
  · subst hn
    apply Units.ext
    have : Subsingleton (ZMod (2 ^ 0)) := by
      simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
    exact Subsingleton.elim _ _
  · have h1 : 1 < 2 ^ i := Nat.one_lt_two_pow hn
    have hc : (((cycS hμ (locMap K S q g) : (ZMod (2 ^ i))ˣ) : ZMod (2 ^ i)).val) = 1 :=
      hζ.pow_inj (ZMod.val_lt _) h1 (hv.symm.trans (pow_one ζ).symm)
    apply Units.ext
    change ((cycS hμ (locMap K S q g) : (ZMod (2 ^ i))ˣ) : ZMod (2 ^ i)) = 1
    have hu := ZMod.natCast_zmod_val
      (((cycS hμ (locMap K S q g) : (ZMod (2 ^ i))ˣ) : ZMod (2 ^ i)))
    rw [hc, Nat.cast_one] at hu
    exact hu.symm

/-- Kind: proved theorem. The actual localized scalar twist has trivial
local Galois action when the required local roots of unity are fixed. It
is not replaced by a separately chosen trivial representation
(tex 2762–2767, 3090–3096, 4860–4863). -/
theorem actualScalar_local_action_trivial
    (hfixed : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (g : Gloc K q) (m : actualN i q hμ) : g • m = m := by
  change ((cycA (Acoef i) hμ (locMap K S q g) : (Acoef i)ˣ) : Acoef i) *
    (show Acoef i from m) = m
  have hc : cycA (Acoef i) hμ (locMap K S q g) = 1 := by
    unfold cycA
    rw [MonoidHom.comp_apply, local_cyclotomic_eq_one i q hμ hfixed g, map_one]
  rw [hc, Units.val_one, one_mul]

end ScalarLocalAction

section ResidueRootPrecision

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Kind: proved theorem. Residue cardinality one modulo the retained
root exponent fixes those roots under the full local Galois group. The
proof uses actual Frobenius and inertia, not a root-fixing assumption
(tex 3090–3096, 4860–4863, 5027–5032). -/
theorem fixedRoots_of_residue_congruence (n : ℕ) [NeZero n]
    (hn : n.Coprime (ringChar (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)))
    (hcard : (Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)) % n = 1)
    (g : Gal(AlgebraicClosure F/F)) (ζ : AlgebraicClosure F) (hζ : ζ ^ n = 1) : g ζ = ζ := by
  obtain ⟨φ, hφ⟩ := exists_isArithFrobeniusLift F
  let φ' : Gal(AlgebraicClosure F/F) := φ
  have hφ' : IsArithFrobeniusLift F φ' := hφ
  let H : Subgroup Gal(AlgebraicClosure F/F) :=
    MulAction.stabilizer Gal(AlgebraicClosure F/F) ζ
  have hF : φ' ∈ H := by
    change φ' ζ = ζ
    have hf := hφ'.apply_of_pow_eq_one hn hζ
    change φ' ζ = ζ ^ Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) at hf
    rw [hf, pow_eq_pow_mod _ hζ, hcard, pow_one]
  have hI : inertiaSubgroup F ≤ H := by
    intro σ hσ
    change @id (Gal(AlgebraicClosure F/F)) σ ζ = ζ
    exact apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one hσ hn hζ
  have hclosed : IsClosed (H : Set Gal(AlgebraicClosure F/F)) :=
    OpenSubgroup.isClosed ⟨H, stabilizer_isOpen_of_isIntegral (K := F) ζ⟩
  have hle := (Subgroup.zpowers φ' ⊔ inertiaSubgroup F).topologicalClosure_minimal
    (sup_le (Subgroup.zpowers_le.mpr hF) hI) hclosed
  have hgen : (Subgroup.zpowers φ' ⊔ inertiaSubgroup F).topologicalClosure = ⊤ :=
    hφ'.topologicalClosure_zpowers_sup_inertiaSubgroup
  rw [hgen] at hle
  exact MulAction.mem_stabilizer_iff.mp (hle (Subgroup.mem_top g))

end ResidueRootPrecision

section ActualCore

open ZInQ.Manuscript.RC.Limits (residualCohomologyAt)
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace (splitLocalRank OrientedLocalRetraction
  exists_stageOrientedLocalRetraction)

/-- Kind: local instance. The finite exponent is nonzero
(tex 2723–2727, 4860–4863). -/
local instance coreExponent_neZero (i : ℕ) : NeZero (2 ^ i) :=
  ⟨pow_ne_zero i two_ne_zero⟩

/-- Kind: local instance. Actual scalar stages use the discrete topology
(tex 2723–2727, 4385–4451). -/
local instance coreScalar_topology (i : ℕ) : TopologicalSpace (Acoef i) := ⊥

/-- Kind: local instance. The scalar-stage topology is discrete
(tex 2723–2727, 4385–4451). -/
local instance coreScalar_discrete (i : ℕ) : DiscreteTopology (Acoef i) := ⟨rfl⟩

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]
  (q : HeightOneSpectrum (𝓞 K)) (hμ : HasRootsOfUnity K S (2 ^ i))

/-- Kind: actual arithmetic data. The normalized local producer retains
its actual coefficient frame, degree-two coordinate, Brauer dictionary,
and exact cochain retraction. Larger root precision is an arithmetic
input, and no scalar trace or residue pairing table is a field
(tex 2723–2727, 3090–3096, 4385–4451, 4860–4863, 5027–5043). -/
structure ActualLocalCore where
  /-- Kind: tame arithmetic orientation data (tex 4860–4863, 5027–5032). -/
  orientation : TameOrientation (q.adicCompletion K) (2 ^ i)
  /-- Kind: actual coefficient basis data (tex 2723–2727, 4860–4863). -/
  eM : actualM W i α q ≃ₗ[Acoef i] (Fin 2 → Acoef i)
  /-- Kind: actual local degree-two coordinate data (tex 4860–4863). -/
  cM : (contCochains (Acoef i) (Gloc K q) (actualM W i α q)).X 2 →ₗ[Acoef i]
    actualM W i α q
  /-- Kind: primitive-root dictionary data (tex 4860–4863). -/
  η : ZMod (2 ^ i) ≃+ KummerCoeff (q.adicCompletion K) (2 ^ i)
  /-- Kind: arithmetic derivative-action input (tex 3090–3096, 4860–4863). -/
  trivialM : ∀ (g : Gloc K q) (m : actualM W i α q), g • m = m
  /-- Kind: arithmetic extra root-precision input (tex 3090–3096). -/
  rootsDouble : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
    (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 * (2 ^ i)) = 1 → g ζ = ζ
  /-- Kind: proved local degree-two coordinate specification
  (tex 4860–4863). -/
  coordinateM : LocalDegreeTwoCoordinate cM
  /-- Kind: proved positive uniformizer normalization (tex 4860–4863). -/
  normalizedM : LocalDegreeTwoNormalized cM
    (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (orientation.unramified g))
    (fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (orientation.kummer g))
  /-- Kind: proved arithmetic Brauer-invariant identification
  (tex 2762–2767, 4860–4863). -/
  brauerM : StageBrauerCoordinateFormula W i α q η
    (fixedRoots_of_double (2 ^ i) rootsDouble) trivialM cM
  /-- Kind: proved primitive-root orientation identification
  (tex 4860–4863, 5027–5032). -/
  rootDictionary : (((η 1).toMul : (SeparableClosure (q.adicCompletion K))ˣ) :
    AlgebraicClosure (q.adicCompletion K)) =
      ZInQ.Contrib.CloudB3RC53.TameQuotient.kummerVal orientation.root orientation.inertia
  /-- Kind: proved actual normalized cochain retraction data
  (tex 4385–4451, 4860–4863). -/
  model : OrientedLocalRetraction (G := Gloc K q) eM orientation.frobenius
    orientation.inertia cM

/-- Kind: proved theorem. The existing arithmetic local producer
constructs the entire actual core, including its normalized retraction
and Brauer dictionary. The inputs are derivative action, larger root
precision, and independent residual local finiteness and dimensions
(tex 3090–3096, 4385–4451, 4860–4863). -/
theorem exists_actualLocalCore
    (h2 : (2 : 𝓞 K) ∉ q.asIdeal) (hFull : FullTorsion K S W (2 ^ i))
    (hM : ∀ (g : Gloc K q) (m : actualM W i α q), g • m = m)
    (hDouble : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 * (2 ^ i)) = 1 → g ζ = ζ)
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (natCx (contCochains (Acoef i) (Gloc K q)
        (actualM W i α q))) n))
    (hdim : ∀ n, Module.finrank (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (natCx (contCochains (Acoef i) (Gloc K q)
        (actualM W i α q))) n) = splitLocalRank n) :
    Nonempty (ActualLocalCore W i α q) := by
  obtain ⟨D, cM, η, eM, model, hc, hn, hbr, hd⟩ :=
    exists_stageOrientedLocalRetraction W i α q h2 hFull hM
      (fixedRoots_of_double (2 ^ i) hDouble) hfin hdim
  exact ⟨⟨D, eM, cM, η, hM, hDouble, hc, hn, hbr, hd, model⟩⟩

variable {W i α q} (X : ActualLocalCore W i α q)

/-- Kind: definition. The same arithmetic unramified character used by
the produced local coordinate (tex 4860–4863, 5027–5032). -/
def ActualLocalCore.u : Gloc K q → Acoef i :=
  fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (X.orientation.unramified g)

/-- Kind: definition. The same exact uniformizer character used by the
produced local coordinate (tex 4860–4863, 5027–5032). -/
def ActualLocalCore.κ : Gloc K q → Acoef i :=
  fun g => algebraMap (ZMod (2 ^ i)) (Acoef i) (X.orientation.kummer g)

omit [W.IsElliptic] [NeZero i] in
/-- Kind: proved theorem. The produced unramified character is continuous
(tex 4860–4863, 5027–5032). -/
theorem ActualLocalCore.continuousU : Continuous X.u := by
  exact (continuous_of_discreteTopology : Continuous
    (algebraMap (ZMod (2 ^ i)) (Acoef i))).comp
      (continuous_urCharN (K := q.adicCompletion K) (n := 2 ^ i))

omit [W.IsElliptic] [NeZero i] in
/-- Kind: proved theorem. The produced uniformizer character is continuous
at the original local orientation (tex 4860–4863, 5027–5032). -/
theorem ActualLocalCore.continuousK : Continuous X.κ := by
  exact (continuous_of_discreteTopology : Continuous
    (algebraMap (ZMod (2 ^ i)) (Acoef i))).comp
      (continuous_kummerLog X.orientation.root_pow X.orientation.root_ne_zero
        X.orientation.primitive (fixedRoots_of_double (2 ^ i) X.rootsDouble))

omit [W.IsElliptic] [NeZero i] in
/-- Kind: proved theorem. The produced unramified character is additive
(tex 4860–4863, 5027–5032). -/
theorem ActualLocalCore.additiveU (g h : Gloc K q) : X.u (g * h) = X.u g + X.u h := by
  change algebraMap (ZMod (2 ^ i)) (Acoef i) (urCharN (q.adicCompletion K) (2 ^ i) (g * h)) =
    algebraMap (ZMod (2 ^ i)) (Acoef i) (urCharN (q.adicCompletion K) (2 ^ i) g) +
      algebraMap (ZMod (2 ^ i)) (Acoef i) (urCharN (q.adicCompletion K) (2 ^ i) h)
  rw [urCharN_mul, map_add]

omit [W.IsElliptic] [NeZero i] in
/-- Kind: proved theorem. The produced uniformizer character is additive
at the original local orientation (tex 4860–4863, 5027–5032). -/
theorem ActualLocalCore.additiveK (g h : Gloc K q) : X.κ (g * h) = X.κ g + X.κ h := by
  change algebraMap (ZMod (2 ^ i)) (Acoef i)
    (kummerLog X.orientation.root_pow X.orientation.root_ne_zero X.orientation.primitive (g * h)) =
      algebraMap (ZMod (2 ^ i)) (Acoef i)
        (kummerLog X.orientation.root_pow X.orientation.root_ne_zero X.orientation.primitive g) +
      algebraMap (ZMod (2 ^ i)) (Acoef i)
        (kummerLog X.orientation.root_pow X.orientation.root_ne_zero X.orientation.primitive h)
  rw [kummerLog_mul _ _ _ (fixedRoots_of_double (2 ^ i) X.rootsDouble), map_add]

omit [W.IsElliptic] [NeZero i] in
include X in
/-- Kind: proved theorem. The original localized scalar twist is trivial
from the produced extra root precision (tex 3090–3096, 4860–4863). -/
theorem ActualLocalCore.trivialN (g : Gloc K q) (m : actualN i q hμ) : g • m = m :=
  actualScalar_local_action_trivial i q hμ (fixedRoots_of_double (2 ^ i) X.rootsDouble) g m

/-- Kind: definition. The scalar coordinate is constructed from the
actual rank-two coordinate in the same root frame (tex 2762–2767, 4860–4863). -/
def ActualLocalCore.cN :
    (contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).X 2 →ₗ[Acoef i] actualN i q hμ :=
  scalarCoordinateFromPlane X.cM X.eM (actualScalarFrame i q hμ)

/-- Kind: definition. The original normalized scalar local trace is
constructed from the produced actual coefficient coordinate
(tex 2762–2767, 4385–4388, 4860–4863). -/
def ActualLocalCore.τ :
    (contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).X 2 →ₗ[Acoef i] Acoef i :=
  scalarTraceFromPlane X.cM X.eM (actualScalarFrame i q hμ)

omit [W.IsElliptic] [NeZero i] in
/-- Kind: proved theorem. The scalar coordinate is a genuine local
coordinate and has the same positive uniformizer normalization; neither
property is a new input (tex 2762–2767, 4860–4863). -/
theorem ActualLocalCore.coordinateN :
    LocalDegreeTwoCoordinate (X.cN hμ) ∧ LocalDegreeTwoNormalized (X.cN hμ) X.u X.κ := by
  exact ⟨retractCoordinate_spec X.cM X.coordinateM
      (scalarProjection X.eM (actualScalarFrame i q hμ))
      (scalarInclusion X.eM (actualScalarFrame i q hμ))
      (scalarProjection_inclusion _ _) X.u X.κ X.continuousU X.continuousK
      X.additiveU X.additiveK X.trivialM (X.trivialN hμ) X.normalizedM,
    retractCoordinate_normalized X.cM _ _ (scalarProjection_inclusion _ _) X.u X.κ X.normalizedM⟩

omit [W.IsElliptic] [NeZero i] in
/-- Kind: proved theorem. The constructed actual local trace kills
coboundaries and is onto on two-cocycles; no trace-isomorphism hypothesis
is added (tex 2762–2767, 4385–4388, 4860–4863). -/
theorem ActualLocalCore.trace_spec :
    (∀ a, X.τ hμ (((contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).d 1 2).hom a) = 0) ∧
      ∀ r : Acoef i, ∃ z,
        ((contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).d 2 3).hom z = 0 ∧ X.τ hμ z = r := by
  exact scalarTraceFromPlane_spec X.cM X.coordinateM X.eM (actualScalarFrame i q hμ)
    X.u X.κ X.continuousU X.continuousK X.additiveU X.additiveK X.trivialM
    (X.trivialN hμ) X.normalizedM

/-- Kind: definition. The constructed scalar coordinate is compared
with the actual local Brauer invariant in every residue-linear functional
using the canonical scalar-module dictionary
(tex 2762–2767, 4860–4863). -/
def ActualLocalCore.scalarBrauerFormula
    (cN : (contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).X 2 →ₗ[Acoef i]
      actualN i q hμ) : Prop := by
  let N := actualN i q hμ
  let : Module (ZMod (2 ^ i)) N := AddCommGroup.zmodModule (actualScalar_nsmul i q hμ)
  let : SMulCommClass (Acoef i) (ZMod (2 ^ i)) N := residueScalarComm (Acoef i) N
  let : IsScalarTower (ZMod (2 ^ i)) (Acoef i) N := residueScalarTower (Acoef i) N
  exact BrauerCoordinateFormula (R := Acoef i) (M := N) X.η
    (kummerCoefficients_fixed (fixedRoots_of_double (2 ^ i) X.rootsDouble)) (X.trivialN hμ) cN

omit [W.IsElliptic] [NeZero i] in
/-- Kind: proved theorem. The constructed scalar local coordinate has
exactly the actual Brauer-invariant formula. Its scalar trace is therefore
fixed arithmetically, not merely chosen as an abstract cohomology isomorphism
(tex 2762–2767, 4385–4388, 4860–4863). -/
theorem ActualLocalCore.scalar_brauerFormula : X.scalarBrauerFormula hμ (X.cN hμ) := by
  let M := actualM W i α q
  let N := actualN i q hμ
  let : Module (ZMod (2 ^ i)) M := AddCommGroup.zmodModule (localizedMcoef_nsmul W i α q)
  let : Module (ZMod (2 ^ i)) N := AddCommGroup.zmodModule (actualScalar_nsmul i q hμ)
  let : SMulCommClass (Acoef i) (ZMod (2 ^ i)) M := residueScalarComm (Acoef i) M
  let : SMulCommClass (Acoef i) (ZMod (2 ^ i)) N := residueScalarComm (Acoef i) N
  let : IsScalarTower (ZMod (2 ^ i)) (Acoef i) M := residueScalarTower (Acoef i) M
  let : IsScalarTower (ZMod (2 ^ i)) (Acoef i) N := residueScalarTower (Acoef i) N
  let hμs := kummerCoefficients_fixed (fixedRoots_of_double (2 ^ i) X.rootsDouble)
  have hm : BrauerCoordinateFormula (R := Acoef i) (M := M) X.η hμs X.trivialM X.cM :=
    X.brauerM
  change BrauerCoordinateFormula (R := Acoef i) (M := N) X.η hμs (X.trivialN hμ) (X.cN hμ)
  exact retractCoordinate_brauerFormula X.η hμs X.trivialM (X.trivialN hμ) X.cM hm
    (scalarProjection X.eM (actualScalarFrame i q hμ))
    (scalarInclusion X.eM (actualScalarFrame i q hμ)) (scalarProjection_inclusion _ _)

omit [W.IsElliptic] [NeZero i] in
/-- Kind: proved theorem. Every original boundary-killing local trace
that is onto on two-cocycles differs from the constructed arithmetic
Brauer trace by one unit, with its exact factor on every two-cocycle.
This retains an already selected original trace without asserting a
pairing-table identity (tex 2762–2767, 4385–4388, 4860–4863). -/
theorem ActualLocalCore.originalTrace_factor
    (τ' : (contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).X 2 →ₗ[Acoef i] Acoef i)
    (hτ' : ∀ a, τ' (((contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).d 1 2).hom a) = 0)
    (honto : ∀ r : Acoef i, ∃ z,
      ((contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).d 2 3).hom z = 0 ∧ τ' z = r) :
    ∃ δ : (Acoef i)ˣ, ∀ z : (contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).X 2,
      ((contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).d 2 3).hom z = 0 →
        τ' z = (δ : Acoef i) * X.τ hμ z := by
  have hunit := traceScale_isUnit τ' hτ' (X.cN hμ) (X.coordinateN hμ).1
    (actualScalarFrame i q hμ) X.u X.κ X.continuousU X.continuousK X.additiveU X.additiveK
    (X.trivialN hμ) (X.coordinateN hμ).2 honto
  refine ⟨hunit.unit, ?_⟩
  intro z hz
  have h := trace_cycle_formula τ' hτ' (X.cN hμ) (X.coordinateN hμ).1
    (actualScalarFrame i q hμ) X.u X.κ X.continuousU X.continuousK X.additiveU X.additiveK
    (X.trivialN hμ) (X.coordinateN hμ).2 z hz
  rw [← hunit.unit_spec] at h
  exact h

/-- Kind: definition with proved arithmetic fields. The actual local
core supplies all coordinates, character lifts, trace and retraction of
`StageArithmeticData`. Only the actual local representative and its
unramified/tame pullback identities are added. No local pairing identity
is supplied as an input (tex 3090–3096, 4385–4451, 4860–4863, 5027–5043). -/
def ActualLocalCore.toArithmetic (Cn : ActualConj K S)
    (hW : W.map (Cn.κ : K →+* K) = W) (hFull : FullTorsion K S W (2 ^ i))
    (θ : Gloc K q →ₜ* Gloc K q) (s : Acoef i)
    (hθu : ∀ g, X.orientation.unramified (θ g) = X.orientation.unramified g)
    (hθκ : ∀ g, algebraMap (ZMod (2 ^ i)) (Acoef i) (X.orientation.kummer (θ g)) =
      s * algebraMap (ZMod (2 ^ i)) (Acoef i) (X.orientation.kummer g)) : StageArithmeticData i := by
  let hu := Characters.exists_unramified_doubleLift (F := q.adicCompletion K) (2 ^ i)
  let hk := orientation_kummer_doubleLift i X.orientation X.rootsDouble
  let χu := Classical.choose hu
  let χκ := Classical.choose hk
  exact actualLocalArithmetic W i α q hμ Cn hW hFull X.orientation
    (fixedRoots_of_double (2 ^ i) X.rootsDouble) X.eM X.cM (X.cN hμ)
    X.coordinateM (X.coordinateN hμ).1 X.normalizedM (X.coordinateN hμ).2 X.model
    X.trivialM (X.trivialN hμ) χu χκ (Classical.choose_spec hu).1 (Classical.choose_spec hk).1
    (Classical.choose_spec hu).2.1 (Classical.choose_spec hk).2.1
    (Classical.choose_spec hu).2.2 (Classical.choose_spec hk).2.2 θ s hθu hθκ
    (X.τ hμ) (X.trace_spec hμ).1 (X.trace_spec hμ).2

/-- Kind: definition with proved arithmetic fields. An already selected
original local trace can be retained while all coordinate, character-lift,
and retraction fields are constructed from the actual core. Its only
trace inputs are boundary vanishing and surjectivity on two-cocycles
(tex 2762–2767, 4385–4388, 4860–4863, 5027–5043). -/
def ActualLocalCore.toArithmeticWithOriginalTrace (Cn : ActualConj K S)
    (hW : W.map (Cn.κ : K →+* K) = W) (hFull : FullTorsion K S W (2 ^ i))
    (θ : Gloc K q →ₜ* Gloc K q) (s : Acoef i)
    (hθu : ∀ g, X.orientation.unramified (θ g) = X.orientation.unramified g)
    (hθκ : ∀ g, algebraMap (ZMod (2 ^ i)) (Acoef i) (X.orientation.kummer (θ g)) =
      s * algebraMap (ZMod (2 ^ i)) (Acoef i) (X.orientation.kummer g))
    (τ' : (contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).X 2 →ₗ[Acoef i] Acoef i)
    (hτ' : ∀ a, τ' (((contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).d 1 2).hom a) = 0)
    (honto : ∀ r : Acoef i, ∃ z,
      ((contCochains (Acoef i) (Gloc K q) (actualN i q hμ)).d 2 3).hom z = 0 ∧ τ' z = r) :
    StageArithmeticData i :=
  { X.toArithmetic hμ Cn hW hFull θ s hθu hθκ with
    τ := τ'
    trace_kills := hτ'
    trace_onto := honto }

end ActualCore

section LabelCore

open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Limits (residualCohomologyAt)
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace (splitLocalRank)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (B : WeierstrassCurve ℚ) [B.IsElliptic] [HasFullTwoTorsion K S (B⁄K)]
  (α : GKS K S →* Lambdaˣ) [IsContChar α]
  (L : CompatibleArithmeticLabel B K S α)

/-- Kind: proved theorem. Odd derivative primes have residue characteristic
prime to the full extra two-power exponent (tex 3090–3096, 4860–4863). -/
theorem extraExponent_coprime (i : ℕ) (q : HeightOneSpectrum (𝓞 K))
    (h2 : (2 : 𝓞 K) ∉ q.asIdeal) :
    (2 * (2 ^ i)).Coprime (ringChar (IsLocalRing.ResidueField
      (ValuativeRel.valuation (q.adicCompletion K)).integer)) := by
  let Fp := IsLocalRing.ResidueField (ValuativeRel.valuation (q.adicCompletion K)).integer
  have hp : (ringChar Fp).Prime :=
    (CharP.char_is_prime_or_zero Fp (ringChar Fp)).resolve_right
      (CharP.char_ne_zero_of_finite Fp (ringChar Fp))
  have hd : ¬ ringChar (IsLocalRing.ResidueField
      (ValuativeRel.valuation (q.adicCompletion K)).integer) ∣ 2 := by
    rw [HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff]
    exact_mod_cast h2
  have hc := Nat.Coprime.pow_left (i + 1) ((hp.coprime_iff_not_dvd.mpr hd).symm)
  simpa only [pow_succ, Nat.mul_comm (2 ^ i) 2] using hc

/-- Kind: proved theorem. The actual arithmetic label supplies the local
core without derivative-action, coordinate, tame-generator, scalar-trace,
or retraction hypotheses. The remaining local assumptions are oddness,
extra residue precision, and independent residual finiteness and ranks
(tex 3090–3096, 4385–4451, 4860–4863, 5027–5043). -/
theorem exists_actualLocalCore_of_label (i : ℕ) [NeZero i]
    (h2 : (2 : 𝓞 K) ∉ (L.label.q i).asIdeal)
    (hcard : (Nat.card (IsLocalRing.ResidueField
      (ValuativeRel.valuation ((L.label.q i).adicCompletion K)).integer)) % (2 * (2 ^ i)) = 1)
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (natCx (contCochains (Acoef i) (Gloc K (L.label.q i))
        (actualM (B⁄K) i (alphaLev i α) (L.label.q i)))) n))
    (hdim : ∀ n, Module.finrank (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (natCx (contCochains (Acoef i) (Gloc K (L.label.q i))
        (actualM (B⁄K) i (alphaLev i α) (L.label.q i)))) n) = splitLocalRank n) :
    Nonempty (ActualLocalCore (B⁄K) i (alphaLev i α) (L.label.q i)) := by
  have : IsOpenKer (alphaLev i α) := alphaLev_openKernel α i
  have : NeZero (2 * (2 ^ i)) := ⟨mul_ne_zero two_ne_zero (pow_ne_zero i two_ne_zero)⟩
  exact exists_actualLocalCore (B⁄K) i (alphaLev i α) (L.label.q i) h2
    (HasFullTwoTorsion.full i) (actualStage_local_action_trivial B α L i)
    (fixedRoots_of_residue_congruence (2 * (2 ^ i))
      (extraExponent_coprime i (L.label.q i) h2) hcard) hfin hdim

omit [HasFullTwoTorsion K S (B⁄K)] [IsContChar α] in
/-- Kind: proved theorem. The retained congruence on the inert rational
prime gives exactly the extra root precision in its local residue field
(tex 3090–3096, 5027–5032). -/
theorem label_residue_extra_precision (i : ℕ)
    (hdiv : (2 * (2 ^ i)) ∣ L.primes.ell i + 1) :
    (Nat.card (IsLocalRing.ResidueField
      (ValuativeRel.valuation ((L.label.q i).adicCompletion K)).integer)) % (2 * (2 ^ i)) = 1 := by
  have : NeZero (2 * (2 ^ i)) := ⟨mul_ne_zero two_ne_zero (pow_ne_zero i two_ne_zero)⟩
  have hn : 1 < 2 * (2 ^ i) := by
    nlinarith [pow_pos (by decide : 0 < (2 : ℕ)) i]
  have hzero : ((L.primes.ell i + 1 : ℕ) : ZMod (2 * (2 ^ i))) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  rw [Nat.cast_add, Nat.cast_one] at hzero
  have he : ((L.primes.ell i : ℕ) : ZMod (2 * (2 ^ i))) = -1 :=
    eq_neg_iff_add_eq_zero.mpr hzero
  have hs : ((L.primes.ell i ^ 2 : ℕ) : ZMod (2 * (2 ^ i))) = 1 := by
    rw [Nat.cast_pow, he]
    ring
  have hval := congrArg ZMod.val hs
  rw [ZMod.val_natCast, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn] at hval
  have hc : Nat.card (𝓞 K ⧸ (L.label.q i).asIdeal) =
      Nat.card (IsLocalRing.ResidueField
        (ValuativeRel.valuation ((L.label.q i).adicCompletion K)).integer) :=
    Nat.card_congr ((L.label.q i).residueFieldEquivAdicCompletion (K := K)).toEquiv
  rw [← hc, L.inert]
  exact hval

/-- Kind: proved theorem. The actual arithmetic label supplies the local
core from the integer extra-precision congruence of (H12), without a
root-fixing, coordinate, character-lift, trace, or retraction hypothesis.
Residual local finiteness and ranks remain independent arithmetic inputs
(tex 3090–3096, 4385–4451, 4860–4863, 5027–5043). -/
theorem exists_actualLocalCore_of_label_precision (i : ℕ) [NeZero i]
    (h2 : (2 : 𝓞 K) ∉ (L.label.q i).asIdeal)
    (hdiv : (2 * (2 ^ i)) ∣ L.primes.ell i + 1)
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (natCx (contCochains (Acoef i) (Gloc K (L.label.q i))
        (actualM (B⁄K) i (alphaLev i α) (L.label.q i)))) n))
    (hdim : ∀ n, Module.finrank (IsLocalRing.ResidueField (Acoef i))
      (residualCohomologyAt (natCx (contCochains (Acoef i) (Gloc K (L.label.q i))
        (actualM (B⁄K) i (alphaLev i α) (L.label.q i)))) n) = splitLocalRank n) :
    Nonempty (ActualLocalCore (B⁄K) i (alphaLev i α) (L.label.q i)) :=
  exists_actualLocalCore_of_label B α L i h2 (label_residue_extra_precision B α L i hdiv)
    hfin hdim

end LabelCore

end ZInQ.Contrib.RC53Assist.ResidueIdentity.Genuine
