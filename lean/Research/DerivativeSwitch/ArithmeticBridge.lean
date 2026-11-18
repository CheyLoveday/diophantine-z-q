import Research.DerivativeSwitch.BoundaryCup

/-!
# From retained duality and local transport to the unit-normalizer adapter

This module proves a conditional arithmetic-facing bridge. It does not construct
Galois cohomology, Selmer complexes, Poitou--Tate duality or determinant functors.
The paired-functional/localization interface below records those source inputs
without assuming the normalized boundary identities or the desired unit relation.
The frozen 39-target sources and specification are unchanged.
-/

namespace Research.DerivativeSwitch.ArithmeticBridge

open Matrix
open scoped Matrix
open ScalarRatio

section Cocycle

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- The full crossed-cocycle conjugation formula, with its coboundary term. -/
theorem cocycle_conjugation (rho : G →* Module.End K V) (p : G → V)
    (hp : ∀ g h, p (g * h) = p g + rho g (p h)) (a x : G) :
    p (a⁻¹ * x * a) = rho a⁻¹ (p x + rho x (p a) - p a) := by
  have h := hp a (a⁻¹ * x * a)
  have hx := hp x a
  have ha : a * (a⁻¹ * x * a) = x * a := by group
  rw [ha, hx] at h
  have hh : rho a (p (a⁻¹ * x * a)) = p x + rho x (p a) - p a := by
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using h.symm
  have hh' := congrArg (rho a⁻¹) hh
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply] using hh'

/-- Trivial local action removes the coboundary. A specified integral unit,
not an arbitrary nonzero field element, gives the shared transport factor. -/
theorem cocycle_transport_shared_unit (rho : G →* Module.End K V) (p : G → V)
    (hp : ∀ g h, p (g * h) = p g + rho g (p h))
    (R : Subring K) (u : Rˣ) (a x : G)
    (ha : ∀ y, rho a y = unitValue R u • y)
    (hx : rho x (p a) = p a) :
    p (a⁻¹ * x * a) = unitValue R u⁻¹ • p x := by
  rw [cocycle_conjugation rho p hp, hx, add_sub_cancel_right]
  have h : rho a (unitValue R u⁻¹ • p x) = p x := by
    rw [ha, smul_smul]
    have hu : unitValue R u * unitValue R u⁻¹ = 1 := by
      rw [mul_comm, unitValue_inv_mul]
    rw [hu, one_smul]
  have h' := congrArg (rho a⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply] using h'.symm

end Cocycle

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

abbrev LocalPair (K : Type*) := Local K × Local K

/-- Raw cup before the conjugate cochain argument is inserted. The coefficient
J is already included here. -/
def rawCup (d : CommonStrictData K I) (epsilon : K)
    (l r : LocalPair K) : K :=
  epsilon * (area l.1 ((d.J : Matrix _ _ K) *ᵥ r.2) -
    area l.2 ((d.J : Matrix _ _ K) *ᵥ r.1))

/-- The common coefficient-transport scalar and the distinct tame sign. -/
def localTransport (u : K) (l : LocalPair K) : LocalPair K :=
  (u • l.1, -(u • l.2))

lemma area_smul_left (u : K) (v x : Local K) :
    area (u • v) x = u * area v x := by
  simp only [area, Pi.smul_apply, smul_eq_mul]
  ring

lemma area_smul_right (u : K) (v x : Local K) :
    area v (u • x) = u * area v x := by
  simp only [area, Pi.smul_apply, smul_eq_mul]
  ring

/-- Symmetry of the coefficient form follows without eigenspace projectors. -/
theorem coefficient_pairing_symmetric (d : CommonStrictData K I)
    (hinv : (d.J : Matrix (Fin 2) (Fin 2) K) * (d.J : Matrix _ _ K) = 1)
    (hdet : d.delta = -1) (v x : Local K) :
    area x ((d.J : Matrix _ _ K) *ᵥ v) =
      area v ((d.J : Matrix _ _ K) *ᵥ x) := by
  have h := area_action (d.J : Matrix _ _ K) x
    ((d.J : Matrix _ _ K) *ᵥ v)
  rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h
  change area ((d.J : Matrix _ _ K) *ᵥ x) v =
    d.delta * area x ((d.J : Matrix _ _ K) *ᵥ v) at h
  rw [hdet, neg_one_mul, area_swap] at h
  exact (neg_injective h).symm

section ConeProduct

variable {AG AU BG BU L2 L0 : Type*}
  [AddCommGroup AG] [Module K AG] [AddCommGroup AU] [Module K AU]
  [AddCommGroup BG] [Module K BG] [AddCommGroup BU] [Module K BU]
  [AddCommGroup L2] [Module K L2] [AddCommGroup L0] [Module K L0]

/-- Degree (2,1), r=0 third component of the cone cup product. `hG` and `hU`
are the retained bilinear compatibility/isotropy homotopies. -/
def coneProductThird (d : CommonStrictData K I) (epsilon : K)
    (locG : AG →ₗ[K] L2) (incU : BU →ₗ[K] LocalPair K)
    (cup20 : L2 →ₗ[K] L0 →ₗ[K] K)
    (hG : AG →ₗ[K] BG →ₗ[K] K) (hU : AU →ₗ[K] BU →ₗ[K] K)
    (g : AG) (u : AU) (l : LocalPair K)
    (g' : BG) (u' : BU) (l' : L0) : K :=
  rawCup d epsilon l (incU u') + cup20 (locG g) l' -
    hG g g' + hU u u'

/-- The boundary calculation actually kills the homotopy terms; no normalized
boundary evaluation is assumed in this elementary identity. -/
theorem cone_pure_boundary (d : CommonStrictData K I) (epsilon : K)
    (locG : AG →ₗ[K] L2) (incU : BU →ₗ[K] LocalPair K)
    (cup20 : L2 →ₗ[K] L0 →ₗ[K] K)
    (hG : AG →ₗ[K] BG →ₗ[K] K) (hU : AU →ₗ[K] BU →ₗ[K] K)
    (l : LocalPair K) (g' : BG) (u' : BU) (l' : L0) :
    coneProductThird d epsilon locG incU cup20 hG hU 0 0 l g' u' l' =
      rawCup d epsilon l (incU u') := by
  simp [coneProductThird, rawCup, area]

end ConeProduct

/-- One condition's actual paired functional interface. The inverse comparison
is between orthogonal and conjugate carriers, never between finite and singular
Selmer complexes. The general boundary adjunction is an inherited arithmetic
input. It does not assume the derivative relation or normalized cup identities. -/
structure PairedBoundaryData (d : CommonStrictData K I)
    (epsilon kappa transport : K) where
  Class : Type*
  Orthogonal : Type*
  Conjugate : Type*
  actual : Class
  realize : Class → (Index I → K)
  conjugate : Class → Conjugate
  comparison : Orthogonal ≃ Conjugate
  locClass : Class → LocalPair K
  locOrthogonal : Orthogonal → LocalPair K
  locConjugate : Conjugate → LocalPair K
  comparison_local : ∀ y, locConjugate (comparison y) = locOrthogonal y
  conjugate_local : ∀ z,
    locConjugate (conjugate z) = localTransport transport (locClass z)
  boundary : LocalPair K → (Index I → K)
  pairing : (Index I → K) → Orthogonal → K
  boundary_adjoint : ∀ l y,
    pairing (boundary l) y = kappa * rawCup d epsilon l (locOrthogonal y)

namespace PairedBoundaryData

def partner {d : CommonStrictData K I} {epsilon kappa transport : K}
    (p : PairedBoundaryData d epsilon kappa transport) : p.Orthogonal :=
  p.comparison.symm (p.conjugate p.actual)

def functional {d : CommonStrictData K I} {epsilon kappa transport : K}
    (p : PairedBoundaryData d epsilon kappa transport) (w : Index I → K) : K :=
  p.pairing w p.partner

/-- Localizing the specified inverse comparison determines the actual partner. -/
theorem partner_local {d : CommonStrictData K I} {epsilon kappa transport : K}
    (p : PairedBoundaryData d epsilon kappa transport) :
    p.locOrthogonal p.partner = localTransport transport (p.locClass p.actual) := by
  rw [← p.comparison_local, partner, Equiv.apply_symm_apply]
  exact p.conjugate_local p.actual

end PairedBoundaryData

/-- The bridge derives the SAME-row all-vector identities from the unnormalized
cup, actual partner construction, class coordinates and boundary realizations. -/
theorem transported_boundary_cup (d : CommonStrictData K I)
    (epsilon kappa transport : K)
    (pF pS : PairedBoundaryData d epsilon kappa transport)
    (hinv : (d.J : Matrix (Fin 2) (Fin 2) K) * (d.J : Matrix _ _ K) = 1)
    (hdet : d.delta = -1)
    (hA : pF.locClass pF.actual = (d.v, 0))
    (hB : pS.locClass pS.actual = (0, (d.J : Matrix _ _ K) *ᵥ d.v))
    (hboundaryF : ∀ s, pF.boundary (0, s) = d.AS *ᵥ s)
    (hboundaryS : ∀ f, pS.boundary (f, 0) = d.AF *ᵥ f)
    (hrowF : ∀ w, d.lamF ⬝ᵥ w = pF.functional w)
    (hrowS : ∀ w, d.lamS ⬝ᵥ w = pS.functional w) :
    BoundaryCupIdentity d epsilon (-(kappa * transport)) (kappa * transport) := by
  refine ⟨hinv, ?_, ?_⟩
  · intro s
    rw [hrowF, ← hboundaryF]
    change pF.pairing (pF.boundary (0, s)) pF.partner = _
    rw [pF.boundary_adjoint, pF.partner_local, hA]
    simp only [rawCup, localTransport, smul_zero,
      neg_zero, Matrix.mulVec_smul, area_smul_right]
    rw [coefficient_pairing_symmetric d hinv hdet d.v s]
    simp only [beta, area, Pi.zero_apply, Matrix.mulVec_zero]
    ring
  · intro f
    rw [hrowS, ← hboundaryS]
    change pS.pairing (pS.boundary (f, 0)) pS.partner = _
    rw [pS.boundary_adjoint, pS.partner_local, hB]
    simp only [rawCup, localTransport, smul_zero,
      Matrix.mulVec_neg, Matrix.mulVec_smul]
    simp only [beta, area, Pi.zero_apply, Pi.neg_apply, Matrix.mulVec_zero,
      Pi.smul_apply, smul_eq_mul]
    ring

/-- End-to-end conditional arithmetic-facing consumer. Both class/functional
tensors are the stored ones. The common trace factor may vanish or be nonunit. -/
theorem arithmetic_unit_comparison (d : CommonStrictData K I) (R : Subring K)
    (epsilon kappa : K) (transport : Rˣ)
    (pF pS : PairedBoundaryData d epsilon kappa (unitValue R transport))
    (hinv : (d.J : Matrix (Fin 2) (Fin 2) K) * (d.J : Matrix _ _ K) = 1)
    (hdet : d.delta = -1)
    (hA : pF.locClass pF.actual = (d.v, 0))
    (hB : pS.locClass pS.actual = (0, (d.J : Matrix _ _ K) *ᵥ d.v))
    (hboundaryF : ∀ s, pF.boundary (0, s) = d.AS *ᵥ s)
    (hboundaryS : ∀ f, pS.boundary (f, 0) = d.AF *ᵥ f)
    (hrowF : ∀ w, d.lamF ⬝ᵥ w = pF.functional w)
    (hrowS : ∀ w, d.lamS ⬝ᵥ w = pS.functional w)
    (hclassF : pF.realize pF.actual = cycle d.hF d.v)
    (hclassS : pS.realize pS.actual = cycle d.hS ((d.J : Matrix _ _ K) *ᵥ d.v))
    (uF uS : K)
    (huF : HasCoordinate (join d.D0 d.AF) (pF.realize pF.actual) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (pS.realize pS.actual) d.lamS uS) :
    UnitRelated R uF uS := by
  rw [hclassF] at huF
  rw [hclassS] at huS
  have hc := transported_boundary_cup d epsilon kappa (unitValue R transport)
    pF pS hinv hdet hA hB hboundaryF hboundaryS hrowF hrowS
  apply integral_boundary_cup_adapter d R (-1) (-1)
    (by simpa using hdet) epsilon (-(kappa * unitValue R transport))
    (kappa * unitValue R transport) uF uS hc _ huF huS
  simp

end Research.DerivativeSwitch.ArithmeticBridge
