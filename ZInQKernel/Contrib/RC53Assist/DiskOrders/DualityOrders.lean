import ZInQKernel.Contrib.RC53Assist.DiskOrders.DegreeZero

/-!
# The degree-three and degree-two disk orders of the calibration

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141); its proof,
tex 4007–4018 and (5.7b) at tex 5293–5302: integral Kummer self-duality
`C_K ≃ RHom(C_K, ℤ₂)[−3]` gives `H³(C_K) ≅ Ext¹(H¹(C_K), ℤ₂)`, `length H³(C_K) = t_K`;
universal coefficients give `0 → H¹(C_K) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞} → H²(C_K)_tors → 0`.

The order tie of the constructed Smith disks `δ₁, δ₂, δ₃` of the integral compact central complex
(`DiskTie`, from the canonical reductions and the calibration shape) reduces the fields of
`DiskArith` to the valuations of the three disks. Here:

* `card_diag_cokernel`, `card_diskCokernel`: `|ℤ₂^r / diag(c)| = 2^{v₂ ∏ c_j}`;
  `card_of_coreRank_zero`, `card_torsion_eq_diskCokernel`: a module in Smith form has the order
  of its disk cokernel when it has no free core, and its torsion is the disk cokernel.
* `card_dual_H3`: `H³` of the termwise dual `Hom(P, ℤ₂)[−3]` of the Smith resolution model `P`
  is the cokernel of the transposed degree-zero differential, i.e. the disk cokernel of `H¹`.
* `disk3_valuation_eq_disk1`: from the integral self-duality `P ≃ Hom(P, ℤ₂)[−3]` of the
  retained model, `v₂ δ₃ = v₂ δ₁` (the order form of (5.7b)).
* **`arith3_central`**: the field `arith3` of `DiskArith` for the actual rational `2`-primary
  torsion order `t`, from integral self-duality, the Milne finiteness and dimension statements,
  rank one, finite torsion and `arith0_central`.
* **`arith2_central`**: the field `arith2`, from the same inputs and the identity
  `|H²(C_K)_tors| = 2^{v₂ shaA}` (`hsha`, the order form of tex 4010–4014: `H²(C_K)_tors` is
  Selmer modulo its maximal divisible subgroup).
* `diskArith_central`: `DiskArith G t shaA` under `hsha`; `diskArith_central_actual`:
  `DiskArith G t |H²(C_K)_tors|` with no further input; `diskArith_congr_valuation`;
  `diskArith_of_declared_orders`: `DiskArith G tA shaA` for declared orders whose `2`-parts are
  those two actual orders.

Kinds: PROVED from the named inputs (the PRINT statements `MilneLocalFiniteness`,
`MilneGlobalFiniteness`, `MilneLocalDimensionTwo`, `MilneGlobalDimensionTwo`; the integral
duality `IntegralCentralKummerDuality`; the address hypotheses; and, for `arith2_central`
and `diskArith_central` only, `hsha`).
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.DiskOrders

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open scoped TensorProduct

section DiskCards

open ZInQ.Contrib.RC53Assist.CalibrationModel

attribute [local instance] Nat.fact_prime_two

/-- `|ℤ₂/(c)| = 2^{v₂ c}` for `c ≠ 0`. Kind: PROVED. -/
theorem card_padic_quot {c : ℤ_[2]} (hc : c ≠ 0) :
    Nat.card (ℤ_[2] ⧸ Ideal.span {c}) = 2 ^ c.valuation := by
  have hspan : (Ideal.span {c} : Ideal ℤ_[2]) = Ideal.span {((2 : ℕ) : ℤ_[2]) ^ c.valuation} := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hc]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff hc).isUnit _
  rw [hspan, ← PadicInt.ker_toZModPow,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := 2) c.valuation))).toEquiv,
    Nat.card_zmod]

/-- The valuation of a finite product of nonzero `2`-adic integers. Kind: PROVED. -/
theorem valuation_prod_fin : ∀ {r : ℕ} (c : Fin r → ℤ_[2]), (∀ j, c j ≠ 0) →
    (∏ j, c j).valuation = ∑ j, (c j).valuation
  | 0, _, _ => by simp
  | r + 1, c, hc => by
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, PadicInt.valuation_mul (hc 0)
      (Finset.prod_ne_zero_iff.2 fun j _ => hc j.succ),
      valuation_prod_fin (fun j => c j.succ) (fun j => hc j.succ)]

/-- The order of the cokernel of a diagonal matrix with nonzero entries. Kind: PROVED. -/
theorem card_diag_cokernel {r : ℕ} (c : Fin r → ℤ_[2]) (hc : ∀ j, c j ≠ 0) :
    Nat.card ((Fin r → ℤ_[2]) ⧸ LinearMap.range
      (LinearMap.pi fun j => (c j) • (LinearMap.proj j : (Fin r → ℤ_[2]) →ₗ[ℤ_[2]] ℤ_[2]))) =
      2 ^ (∏ j, c j).valuation := by
  let Q : Submodule ℤ_[2] (Fin r → ℤ_[2]) :=
    Submodule.pi Set.univ (fun j => (Ideal.span {c j} : Submodule ℤ_[2] ℤ_[2]))
  have hQ : LinearMap.range (LinearMap.pi fun j =>
      (c j) • (LinearMap.proj j : (Fin r → ℤ_[2]) →ₗ[ℤ_[2]] ℤ_[2])) = Q := by
    ext x
    simp only [LinearMap.mem_range, Q, Submodule.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · rintro ⟨y, rfl⟩ j
      exact Ideal.mem_span_singleton'.2 ⟨y j, by simp [mul_comm]⟩
    · intro hx
      choose b hb using fun j => Ideal.mem_span_singleton'.1 (hx j)
      refine ⟨b, ?_⟩
      funext j
      simp [← hb j, mul_comm]
  rw [hQ, Nat.card_congr (Submodule.quotientPi
    (fun j : Fin r => (Ideal.span {c j} : Submodule ℤ_[2] ℤ_[2]))).toEquiv, Nat.card_pi]
  have hj : ∀ j, Nat.card (ℤ_[2] ⧸ (Ideal.span {c j} : Submodule ℤ_[2] ℤ_[2])) =
      2 ^ (c j).valuation := fun j => card_padic_quot (hc j)
  simp only [hj]
  rw [Finset.prod_pow_eq_pow_sum, valuation_prod_fin c hc]

/-- The disk cokernel of a Smith presentation over `ℤ₂` has order `2^{v₂ det}`.
Kind: PROVED. -/
theorem card_diskCokernel {H : Type} [AddCommGroup H] [Module ℤ_[2] H]
    (T : DiagonalResolution (R := ℤ_[2]) H) :
    Nat.card T.DiskCokernel = 2 ^ (Matrix.diagonal T.coefficient).det.valuation := by
  rw [Matrix.det_diagonal]
  have h : T.diskMap = LinearMap.pi fun j =>
      (T.coefficient j) • (LinearMap.proj j : (Fin T.relations → ℤ_[2]) →ₗ[ℤ_[2]] ℤ_[2]) := by
    ext x j
    rfl
  change Nat.card ((Fin T.relations → ℤ_[2]) ⧸ LinearMap.range T.diskMap) = _
  rw [h]
  exact card_diag_cokernel T.coefficient T.coefficient_ne_zero

/-- A module whose Smith presentation has no free core has the order of its disk cokernel.
Kind: PROVED. -/
theorem card_of_coreRank_zero {H : Type} [AddCommGroup H] [Module ℤ_[2] H]
    (T : DiagonalResolution (R := ℤ_[2]) H) (h0 : T.coreRank = 0) :
    Nat.card H = Nat.card T.DiskCokernel := by
  have : IsEmpty T.Core := Fintype.card_eq_zero_iff.1 h0
  rw [Nat.card_congr T.moduleEquiv.toEquiv, Nat.card_prod, Nat.card_unique, one_mul]

/-- The torsion of a module presented in Smith form is its disk cokernel. Kind: PROVED. -/
theorem card_torsion_eq_diskCokernel {H : Type} [AddCommGroup H] [Module ℤ_[2] H]
    (T : DiagonalResolution (R := ℤ_[2]) H) :
    Nat.card (Submodule.torsion ℤ_[2] H) = Nat.card T.DiskCokernel := by
  let e := T.moduleEquiv
  have hfree : ∀ (a : ℤ_[2]), a ≠ 0 → ∀ f : T.Core → ℤ_[2], a • f = 0 → f = 0 := by
    intro a ha f h
    funext j
    have := congrFun h j
    simp only [Pi.smul_apply, Pi.zero_apply] at this
    exact (smul_eq_zero.1 this).resolve_left ha
  have hfst : ∀ x : H, x ∈ Submodule.torsion ℤ_[2] H → (e x).1 = 0 := by
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha' : (a : ℤ_[2]) • x = 0 := ha
    apply hfree (a : ℤ_[2]) (nonZeroDivisors.coe_ne_zero a)
    have := congrArg (fun z => (e z).1) ha'
    simpa only [map_smul, Prod.smul_fst, map_zero, Prod.fst_zero] using this
  refine Nat.card_eq_of_bijective (fun x => (e x.1).2) ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    apply Subtype.ext
    apply e.injective
    exact Prod.ext ((hfst x hx).trans (hfst y hy).symm) h
  · intro q
    obtain ⟨a, ha⟩ := T.diskCokernel_torsion (x := q)
    have ha' : (a : ℤ_[2]) • q = 0 := ha
    refine ⟨⟨e.symm (0, q), (Submodule.mem_torsion_iff _).2 ⟨a, ?_⟩⟩, ?_⟩
    · change (a : ℤ_[2]) • e.symm (0, q) = 0
      rw [← map_smul, Prod.smul_mk, smul_zero, ha']
      exact map_zero _
    · change (e (e.symm (0, q))).2 = q
      rw [LinearEquiv.apply_symm_apply]

end DiskCards

section DualTop

open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {R : Type} [CommRing R] {C : CochainComplex (ModuleCat.{0} R) ℤ}
  (T : ∀ n : ℤ, DiagonalResolution (R := R) (C.homology n))

/-- The degree-zero term of the Smith resolution model. Kind: definition. -/
abbrev term0 : Type := (Fin (T 0).generators → R) × (Fin (T 1).relations → R)

/-- The degree-one term of the Smith resolution model. Kind: definition. -/
abbrev term1 : Type := (Fin (T 1).generators → R) × (Fin (T 2).relations → R)

/-- The degree-zero differential of the Smith resolution model. Kind: definition. -/
def diff01 : term0 T →ₗ[R] term1 T :=
  ((T 1).differential.comp (LinearMap.snd R _ _)).prod 0

/-- The linear forms on the degree-zero term, read on the relation coordinates of `H¹`.
Kind: definition. -/
def dualZeroCoord : Module.Dual R (term0 T) →ₗ[R] (Fin (T 1).relations → R) where
  toFun ψ j := ψ (0, Pi.single j 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- With no degree-zero generators the coordinates are bijective. Kind: PROVED. -/
theorem dualZeroCoord_bijective (h0 : (T 0).generators = 0) :
    Function.Bijective (dualZeroCoord T) := by
  have hE : IsEmpty (Fin (T 0).generators) := by rw [h0]; infer_instance
  constructor
  · intro ψ ψ' h
    apply LinearMap.ext
    rintro ⟨x, y⟩
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    have hxy : ((0, y) : term0 T) = ∑ j, y j • ((0, Pi.single j 1) : term0 T) := by
      ext m
      · exact (hE.elim m)
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hxy, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul]
    exact congrArg (y j • ·) (congrFun h j)
  · intro a
    refine ⟨∑ j, a j • ((LinearMap.proj j : (Fin (T 1).relations → R) →ₗ[R] R).comp
        (LinearMap.snd R (Fin (T 0).generators → R) (Fin (T 1).relations → R))), ?_⟩
    funext j
    simp [dualZeroCoord, Pi.single_apply]

/-- The coordinates carry the transposed degree-zero differential onto the Smith disks of `H¹`.
Kind: PROVED. -/
theorem dualZeroCoord_range :
    (LinearMap.range (diff01 T).dualMap).map (dualZeroCoord T) =
      LinearMap.range (T 1).diskMap := by
  have hb (j : Fin (T 1).relations) : (T 1).differential (Pi.single j 1) =
      (T 1).coefficient j • Pi.single ((T 1).embedding j) 1 := by
    have h := (T 1).differential_basis j
    rw [Pi.basisFun_apply, Pi.basisFun_apply] at h
    exact h
  ext b
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
    refine ⟨fun j => φ (Pi.single ((T 1).embedding j) 1, 0), ?_⟩
    funext j
    change (T 1).coefficient j * φ (Pi.single ((T 1).embedding j) 1, 0) =
      φ ((T 1).differential (Pi.single j 1), 0)
    rw [hb]
    have : (((T 1).coefficient j • Pi.single ((T 1).embedding j) 1, 0) : term1 T) =
        (T 1).coefficient j • ((Pi.single ((T 1).embedding j) 1, 0) : term1 T) := by
      ext <;> simp
    rw [this, map_smul, smul_eq_mul]
  · rintro ⟨c, rfl⟩
    let φ : Module.Dual R (term1 T) :=
      ∑ j, c j • ((LinearMap.proj ((T 1).embedding j) :
        (Fin (T 1).generators → R) →ₗ[R] R).comp
          (LinearMap.fst R (Fin (T 1).generators → R) (Fin (T 2).relations → R)))
    refine ⟨_, ⟨φ, rfl⟩, ?_⟩
    funext j
    change φ ((T 1).differential (Pi.single j 1), 0) = (T 1).coefficient j * c j
    rw [hb]
    simp only [φ, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.proj_apply, Pi.smul_apply,
      Pi.single_apply, (T 1).embedding.injective.eq_iff, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

/-- **The top cohomology of the dual of the Smith model is the disk cokernel of `H¹`**
(the cokernel of the transposed degree-zero differential). Kind: PROVED. -/
theorem card_dualCoker (h0 : (T 0).generators = 0) :
    Nat.card (Module.Dual R (term0 T) ⧸ LinearMap.range (diff01 T).dualMap) =
      Nat.card (T 1).DiskCokernel := by
  let e := LinearEquiv.ofBijective (dualZeroCoord T) (dualZeroCoord_bijective T h0)
  exact Nat.card_congr (Submodule.Quotient.equiv _ _ e (dualZeroCoord_range T)).toEquiv

/-- Cycles modulo boundaries with all elements cycles. Kind: definition. -/
def subquotTopEquiv {X : Type} [AddCommGroup X] [Module R X] (B : Submodule R X) :
    ZInQ.Contrib.RC53Assist.InnerLimitArith.subquot B ⊤ ≃ₗ[R] X ⧸ B :=
  Submodule.Quotient.equiv _ _ Submodule.topEquiv (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, trivial⟩, hx, rfl⟩)

/-- **`H³` of the termwise dual `Hom(P, R)[−3]` of the Smith resolution model** is the cokernel of
the transposed degree-zero differential, i.e. the disk cokernel of `H¹`, when the model vanishes
in degree `−1` and has no degree-zero generators. Kind: PROVED. -/
theorem card_dual_H3 (h0 : (T 0).generators = 0) (hm1 : (T (-1)).generators = 0)
    (h0r : (T 0).relations = 0) :
    Nat.card ((dualCx (resolutionGCx C (fun n => (T n).toFreeResolution)) 3).toCC.homology 3) =
      Nat.card (T 1).DiskCokernel := by
  set P := resolutionGCx C (fun n => (T n).toFreeResolution)
  set D := dualCx P 3
  rw [Nat.card_congr (rawHomologyEquiv D 2 3 4 (by norm_num) (by norm_num)).toEquiv]
  have hP : Subsingleton (P.X (3 - 4)) := by
    have e1 : IsEmpty (Fin (T (-1)).generators) := by rw [hm1]; infer_instance
    have e2 : IsEmpty (Fin (T 0).relations) := by rw [h0r]; infer_instance
    change Subsingleton ((Fin (T (-1)).generators → R) × (Fin (T 0).relations → R))
    infer_instance
  have hX4 : Subsingleton (D.X 4) := by
    change Subsingleton (Module.Dual R (P.X (3 - 4)))
    constructor
    intro f g
    apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0, map_zero, map_zero]
  have hker : LinearMap.ker (D.d 3 4 (by norm_num)) = ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact Subsingleton.elim _ _
  rw [hker, Nat.card_congr (subquotTopEquiv _).toEquiv]
  have hs : -(sgn (2 : ℤ)) = -1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, sgn_ofNat]
    norm_num
  have hr : LinearMap.range (D.d 2 3 (by norm_num)) =
      LinearMap.range (P.d (3 - 3) (3 - 2) (by norm_num)).dualMap := by
    change LinearMap.range ((-(sgn 2)) • (P.d (3 - 3) (3 - 2) (by norm_num)).dualMap) = _
    rw [hs, neg_one_smul, LinearMap.range_neg]
  rw [hr]
  exact card_dualCoker T h0

end DualTop

section Arith3

open scoped Classical
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness MilneGlobalFiniteness)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The calibration shape of the compact central complex from the Milne statements, integral
self-duality and rank one (as in the literature route of the calibration leaf). Kind: PROVED. -/
theorem shape_of_duality (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hdual : IntegralCentralKummerDuality G hfinite)
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)]
    (hrank : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1) :
    CalibrationCohomologyShape (compactCentralComplex G) := by
  have hout : ∀ n : ℤ, n < 1 ∨ 3 < n → Subsingleton ((compactCentralComplex G).homology n) :=
    compactCentral_outside G hloc hglob hlocal hglobal hK h2
  refine ⟨hout, hrank, ?_, ?_⟩
  · exact ((integralCentralDuality_ranks G hfinite hdual 2).trans
      (cohomology_finrank_degree_congr (compactCentralComplex G) (by decide))).trans hrank
  · have h : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 3) =
        Module.finrank ℤ_[2] ((compactCentralComplex G).homology 0) :=
      (integralCentralDuality_ranks G hfinite hdual 3).trans
        (cohomology_finrank_degree_congr (compactCentralComplex G) (by decide))
    have : Subsingleton ((compactCentralComplex G).homology 0) := hout 0 (by omega)
    exact h.trans Module.finrank_zero_of_subsingleton

/-- **Self-duality identifies the degree-three torsion with the degree-one torsion** (tex
4014–4015), at the level of the constructed Smith disks: `v₂ δ₃ = v₂ δ₁`. From the integral
Kummer self-duality `P ≃ Hom(P, ℤ₂)[−3]` of the retained model. Kind: PROVED. -/
theorem disk3_valuation_eq_disk1 (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hdual : IntegralCentralKummerDuality G hfinite)
    (H : CalibrationCohomologyShape (compactCentralComplex G)) :
    (centralDiskMatrix G hfinite 3).det.valuation =
      (centralDiskMatrix G hfinite 1).det.valuation := by
  let C := compactCentralComplex G
  let T := chosenPresentations C hfinite
  obtain ⟨e⟩ := hdual
  have : QuasiIso e.hom := e.quasiIso_hom
  have := retainedCentralComparison_quasiIso G hfinite
  have h0 := (chosenDiagonalResolution_zero (hfinite 0) (H.outside 0 (by omega)))
  have hm := (chosenDiagonalResolution_zero (hfinite (-1)) (H.outside (-1) (by omega)))
  have hc3 : (T 3).coreRank = 0 := (chosenPresentations_coreRank C hfinite 3).trans H.rank_three
  have a1 := card_of_coreRank_zero (T 3) hc3
  have a2 : Nat.card ((retainedCentralComplex G hfinite).homology 3) = Nat.card (C.homology 3) :=
    Nat.card_congr (asIso (HomologicalComplex.homologyMap
      (retainedCentralComparison G hfinite) 3)).toLinearEquiv.toEquiv
  have a3 : Nat.card ((centralRetainedGCx G hfinite).toCC.homology 3) =
      Nat.card ((dualCx (centralRetainedGCx G hfinite) 3).toCC.homology 3) :=
    Nat.card_congr (asIso (HomologicalComplex.homologyMap e.hom 3)).toLinearEquiv.toEquiv
  have a4 := card_dual_H3 T h0.1 hm.1 h0.2
  have e3 : Nat.card (T 3).DiskCokernel = Nat.card (T 1).DiskCokernel :=
    calc Nat.card (T 3).DiskCokernel = Nat.card (C.homology 3) := a1.symm
      _ = Nat.card ((retainedCentralComplex G hfinite).homology 3) := a2.symm
      _ = Nat.card ((dualCx (centralRetainedGCx G hfinite) 3).toCC.homology 3) := a3
      _ = Nat.card (T 1).DiskCokernel := a4
  have e3' := e3
  rw [card_diskCokernel, card_diskCokernel] at e3'
  exact Nat.pow_right_injective (le_refl 2) e3'

/-- **The field `arith3` of `DiskArith`, PROVED for the actual torsion from integral
self-duality** (tex 4014–4015): with the order tie of the constructed disks (DiskTie, from the
canonical reductions and the calibration shape), the integral Kummer self-duality of the
retained model, the Milne finiteness and dimension statements, rank one and finite rational
`2`-primary torsion of order `t`, one has `|H³| = 2^{i v₂ t}` for all large `i`.
Kind: PROVED. -/
theorem arith3_central (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hdual : IntegralCentralKummerDuality G hfinite)
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)]
    (hrank : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, Nat.card (G.selH i 3) =
      2 ^ (padicValNat 2 (Nat.card (AddCommGroup.primaryComponent
        (centralCurve G).toAffine.Point 2)) * i) := by
  have H := shape_of_duality G hfinite hdual hloc hglob hlocal hglobal hK h2 hrank
  have Tie := diskTie_of_finite_cohomology G hfinite H
    (fun i _ => canonicalCentralReductionMap_quasiIso G i)
  have hv := disk3_valuation_eq_disk1 G hfinite hdual H
  set δ₁ := (centralDiskMatrix G hfinite 1).det with hδ₁
  set δ₃ := (centralDiskMatrix G hfinite 3).det with hδ₃
  have h₁ : δ₁ ≠ 0 := centralDiskMatrix_det_ne_zero G hfinite 1
  have h₃ : δ₃ ≠ 0 := centralDiskMatrix_det_ne_zero G hfinite 3
  set a := padicValNat 2 (Nat.card (AddCommGroup.primaryComponent
    (centralCurve G).toAffine.Point 2)) with ha
  obtain ⟨i₁, hi₁⟩ := Tie.tie0
  obtain ⟨i₂, hi₂⟩ := arith0_central G
  obtain ⟨i₃, hi₃⟩ := Tie.tie3
  have hva : δ₁.valuation = a := by
    set i := i₁ + i₂ + δ₁.valuation + 1
    have hi : i ≠ 0 := by omega
    have h := (hi₁ i (by omega)).symm.trans (hi₂ i (by omega))
    rw [cycOrder_eq hi h₁ (by omega)] at h
    exact two_pow_mul_inj hi h
  refine ⟨i₃ + δ₃.valuation + 1, fun i hi => ?_⟩
  have hi0 : i ≠ 0 := by omega
  rw [hi₃ i (by omega), cycOrder_eq hi0 h₃ (by omega), hv, hva]

end Arith3

section Arith2

open scoped Classical
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness MilneGlobalFiniteness)

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The second constructed disk has the length of the integral degree-two torsion.
Kind: PROVED. -/
theorem card_torsion_two (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n)) :
    Nat.card (Submodule.torsion ℤ_[2] ((compactCentralComplex G).homology 2)) =
      2 ^ (centralDiskMatrix G hfinite 2).det.valuation := by
  rw [card_torsion_eq_diskCokernel (chosenPresentations (compactCentralComplex G) hfinite 2),
    card_diskCokernel]
  rfl

/-- **The field `arith2` of `DiskArith`, PROVED from the integral identity of the degree-two
torsion with the declared `Ш`-order** (`hsha`: `|H²(C_K)_tors| = 2^{v₂ shaA}`, the order form of
tex 4010–4012, `H²(C_K)_tors` = Selmer modulo its maximal divisible subgroup), with the inputs of
`arith3_central`: `|H²| = 2^{i (i + v₂ shaA + v₂ t)}` for all large `i`. Kind: PROVED. -/
theorem arith2_central (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hdual : IntegralCentralKummerDuality G hfinite)
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)]
    (hrank : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (shaA : ℕ) (hsha : Nat.card (Submodule.torsion ℤ_[2] ((compactCentralComplex G).homology 2)) =
      2 ^ padicValNat 2 shaA) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, Nat.card (G.selH i 2) =
      2 ^ ((i + padicValNat 2 shaA + padicValNat 2 (Nat.card (AddCommGroup.primaryComponent
        (centralCurve G).toAffine.Point 2))) * i) := by
  have H := shape_of_duality G hfinite hdual hloc hglob hlocal hglobal hK h2 hrank
  have Tie := diskTie_of_finite_cohomology G hfinite H
    (fun i _ => canonicalCentralReductionMap_quasiIso G i)
  have hv := disk3_valuation_eq_disk1 G hfinite hdual H
  set δ₁ := (centralDiskMatrix G hfinite 1).det with hδ₁
  set δ₂ := (centralDiskMatrix G hfinite 2).det with hδ₂
  set δ₃ := (centralDiskMatrix G hfinite 3).det with hδ₃
  have h₁ : δ₁ ≠ 0 := centralDiskMatrix_det_ne_zero G hfinite 1
  have h₂ : δ₂ ≠ 0 := centralDiskMatrix_det_ne_zero G hfinite 2
  have h₃ : δ₃ ≠ 0 := centralDiskMatrix_det_ne_zero G hfinite 3
  have hv2 : δ₂.valuation = padicValNat 2 shaA :=
    Nat.pow_right_injective (le_refl 2) ((card_torsion_two G hfinite).symm.trans hsha)
  set a := padicValNat 2 (Nat.card (AddCommGroup.primaryComponent
    (centralCurve G).toAffine.Point 2)) with ha
  obtain ⟨i₁, hi₁⟩ := Tie.tie0
  obtain ⟨i₂, hi₂⟩ := arith0_central G
  obtain ⟨i₃, hi₃⟩ := Tie.tie2
  have hva : δ₁.valuation = a := by
    set i := i₁ + i₂ + δ₁.valuation + 1
    have hi : i ≠ 0 := by omega
    have h := (hi₁ i (by omega)).symm.trans (hi₂ i (by omega))
    rw [cycOrder_eq hi h₁ (by omega)] at h
    exact two_pow_mul_inj hi h
  refine ⟨i₃ + δ₂.valuation + δ₃.valuation + 1, fun i hi => ?_⟩
  have hi0 : i ≠ 0 := by omega
  rw [hi₃ i (by omega), cycOrder_eq hi0 h₂ (by omega), cycOrder_eq hi0 h₃ (by omega), hv, hva,
    hv2, ← pow_add, ← pow_add]
  congr 1
  ring

/-- **`DiskArith` for the genuine central Kummer complexes**, with `tA` the actual order of the
rational `2`-primary torsion of the central twist and any `shaA` whose `2`-part is the order of
the integral degree-two torsion (`hsha`). Kind: PROVED (from the named inputs). -/
theorem diskArith_central (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hdual : IntegralCentralKummerDuality G hfinite)
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)]
    (hrank : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (shaA : ℕ) (hsha : Nat.card (Submodule.torsion ℤ_[2] ((compactCentralComplex G).homology 2)) =
      2 ^ padicValNat 2 shaA) :
    DiskArith G (Nat.card (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
      shaA where
  arith0 := arith0_central G
  arith2 := arith2_central G hfinite hdual hloc hglob hlocal hglobal hK h2 hrank shaA hsha
  arith3 := arith3_central G hfinite hdual hloc hglob hlocal hglobal hK h2 hrank

end Arith2

section Actual

open scoped Classical
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness MilneGlobalFiniteness)

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- `DiskArith` depends on its two orders only through their `2`-adic valuations.
Kind: PROVED. -/
theorem diskArith_congr_valuation {G : GenuineKummerData K E₀ hZ} {tA shaA tA' shaA' : ℕ}
    (A : DiskArith G tA shaA) (ht : padicValNat 2 tA = padicValNat 2 tA')
    (hs : padicValNat 2 shaA = padicValNat 2 shaA') : DiskArith G tA' shaA' where
  arith0 := ht ▸ A.arith0
  arith2 := ht ▸ hs ▸ A.arith2
  arith3 := ht ▸ A.arith3

/-- **`DiskArith` for the actual orders**: `tA` the order of the rational `2`-primary torsion of
the central twist `E^{(h)}/K`, `shaA` the order of the torsion of the second integral compact
Kummer cohomology `H²(C_K)_tors` (Selmer modulo its maximal divisible subgroup, tex 4010–4012),
for the genuine finite central Kummer complexes. Kind: PROVED (from the named inputs). -/
theorem diskArith_central_actual (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hdual : IntegralCentralKummerDuality G hfinite)
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)]
    (hrank : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1) :
    DiskArith G (Nat.card (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
      (Nat.card (Submodule.torsion ℤ_[2] ((compactCentralComplex G).homology 2))) := by
  refine diskArith_central G hfinite hdual hloc hglob hlocal hglobal hK h2 hrank _ ?_
  rw [card_torsion_two G hfinite, padicValNat.prime_pow]

/-- **`DiskArith` for declared orders**: the field `arith` of the Kummer block holds for
declared orders `tA`, `shaA` as soon as their `2`-parts are the actual ones, the order of the
rational `2`-primary torsion of the central twist and the order of `H²(C_K)_tors`.
Kind: PROVED (from the named inputs). -/
theorem diskArith_of_declared_orders (G : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hdual : IntegralCentralKummerDuality G hfinite)
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)]
    (hrank : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1) (tA shaA : ℕ)
    (htA : padicValNat 2 tA = padicValNat 2
      (Nat.card (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)))
    (hsha : padicValNat 2 shaA = padicValNat 2
      (Nat.card (Submodule.torsion ℤ_[2] ((compactCentralComplex G).homology 2)))) :
    DiskArith G tA shaA :=
  diskArith_congr_valuation (diskArith_central_actual G hfinite hdual hloc hglob hlocal hglobal
    hK h2 hrank) htA.symm hsha.symm

end Actual

section NonVacuity

/-- Non-vacuity of the coordinate count: the trivial group acting on `ℤ/4`.
Kind: PROVED (non-vacuity). -/
example : Nat.card {x : (Fin 2 → ZMod 4) ⊗[ℤ] ZMod 4 //
    ∀ σ : Unit, rightAct (n := 4) σ x = x} = 4 ^ 2 := by
  have : NeZero (4 : ℕ) := ⟨by norm_num⟩
  rw [card_rightInvariants, Fintype.card_fin]
  have h : Nat.card {t : ZMod 4 // ∀ σ : Unit, σ • t = t} = Nat.card (ZMod 4) :=
    Nat.card_congr ⟨fun t => t.1, fun t => ⟨t, fun _ => rfl⟩, fun _ => rfl, fun _ => rfl⟩
  rw [h, Nat.card_zmod]

/-- Non-vacuity of the primary-component statements: `ℤ/4` has `2`-primary component of order
`4 = 2²`, reached by its `4`-torsion. Kind: PROVED (non-vacuity). -/
example : Nat.card (AddCommGroup.primaryComponent (ZMod 4) 2) =
    2 ^ padicValNat 2 (Nat.card (AddCommGroup.primaryComponent (ZMod 4) 2)) :=
  card_primaryComponent_two

/-- Non-vacuity of the disk orders: `|ℤ₂²/diag(2, 2)| = 2^{v₂ 4}`. Kind: PROVED (non-vacuity). -/
example : Nat.card ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range
    (LinearMap.pi fun j => ((fun _ => (2 : ℤ_[2])) j) •
      (LinearMap.proj j : (Fin 2 → ℤ_[2]) →ₗ[ℤ_[2]] ℤ_[2]))) =
    2 ^ (∏ _j : Fin 2, (2 : ℤ_[2])).valuation :=
  card_diag_cokernel (fun _ => (2 : ℤ_[2])) (fun _ => two_ne_zero)

end NonVacuity

end ZInQ.Contrib.RC53Assist.DiskOrders
