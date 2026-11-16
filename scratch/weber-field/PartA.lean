import ZInQKernel.Contrib.OneProof.X1Igusa
import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Roots
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality

noncomputable section

namespace X1Igusa.Weber

open LeafModCurves WeierstrassCurve T5Glue

/-- The kernel-model expression of Weber's function at `P`: `w(P) = (α x(P) − 3/2)/(g_j − 27)`. -/
def wOf (P : EjBar.toAffine.Point) : Kbar :=
  (algebraMap Qj Kbar alpha * xCoord P + algebraMap Qj Kbar (-3 / 2)) / algebraMap Qj Kbar (gDS - 27)

/-- `F(J, T)` at `(J, T) = (j, w(P))` in `\overline{ℚ(j)}`. -/
def evAlg (F : Polynomial (Polynomial ℚ)) (P : EjBar.toAffine.Point) : Kbar :=
  (F.map ((algebraMap Qj Kbar).comp (algebraMap (Polynomial ℚ) Qj))).eval (wOf P)

/-! ## A. The algebraic lemma -/

/-- `ℚ[J] → \overline{ℚ(j)}`. -/
abbrev phiK : Polynomial ℚ →+* Kbar := (algebraMap Qj Kbar).comp (algebraMap (Polynomial ℚ) Qj)

/-- Evaluation `ℚ[J][T] → \overline{ℚ(j)}` at `(j, θ)`. -/
def evK (θ : Kbar) : Polynomial (Polynomial ℚ) →+* Kbar := Polynomial.eval₂RingHom phiK θ

theorem evAlg_eq (F : Polynomial (Polynomial ℚ)) (P : EjBar.toAffine.Point) :
    evAlg F P = evK (wOf P) F := by
  simp only [evAlg, evK, Polynomial.eval_map, Polynomial.coe_eval₂RingHom]

section
attribute [local instance] Polynomial.algebra Polynomial.isLocalization

/-- **A prime ideal of `ℚ[J][T]` meeting `ℚ[J]` only in `0` and containing a nonzero element is the kernel of
`T ↦ θ` for some `θ ∈ \overline{ℚ(j)}`.** -/
theorem exists_root_of_isPrime {I : Ideal (Polynomial (Polynomial ℚ))} (hI : I.IsPrime)
    (hdisj : ∀ c : Polynomial ℚ, Polynomial.C c ∈ I → c = 0) {Φ : Polynomial (Polynomial ℚ)}
    (hΦ : Φ ∈ I) (hΦ0 : Φ ≠ 0) : ∃ θ : Kbar, ∀ F, F ∈ I ↔ evK θ F = 0 := by
  set M := (nonZeroDivisors (Polynomial ℚ)).map (Polynomial.C : Polynomial ℚ →+* _) with hM
  have : IsLocalization M (Polynomial Qj) := Polynomial.isLocalization _ _
  have hd : Disjoint (M : Set (Polynomial (Polynomial ℚ))) I := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ hcI
    exact nonZeroDivisors.ne_zero hc (hdisj c hcI)
  set J := I.map (algebraMap (Polynomial (Polynomial ℚ)) (Polynomial Qj)) with hJdef
  have hJp : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ I hI hd
  have hJI : J.under _ = I := IsLocalization.under_map_of_isPrime_disjoint M _ hI hd
  have hmapinj : Function.Injective (algebraMap (Polynomial (Polynomial ℚ)) (Polynomial Qj)) :=
    Polynomial.map_injective _ (IsFractionRing.injective (Polynomial ℚ) Qj)
  have hJ0 : J ≠ ⊥ := by
    intro h
    have : algebraMap _ (Polynomial Qj) Φ ∈ J := Ideal.mem_map_of_mem _ hΦ
    rw [h, Ideal.mem_bot, map_eq_zero_iff _ hmapinj] at this
    exact hΦ0 this
  have hJm : J.IsMaximal := Ideal.IsPrime.isMaximal hJp hJ0
  set p := Submodule.IsPrincipal.generator J with hpdef
  have hJsp : J = Ideal.span {p} := (Ideal.span_singleton_generator J).symm
  have hp0 : p ≠ 0 := by
    intro h; apply hJ0; rw [hJsp, h, Ideal.span_singleton_eq_bot]
  have hpu : ¬ IsUnit p := by
    intro h; apply hJm.ne_top; rw [hJsp, Ideal.span_singleton_eq_top]; exact h
  have hdeg : p.degree ≠ 0 := by
    intro h
    exact hpu (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_aeval_eq_zero Kbar p hdeg
  refine ⟨θ, fun F => ?_⟩
  have hker : J = RingHom.ker (Polynomial.aeval θ : Polynomial Qj →ₐ[Qj] Kbar) := by
    apply hJm.eq_of_le
    · rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]; exact one_ne_zero
    · rw [hJsp, Ideal.span_le, Set.singleton_subset_iff]; exact hθ
  have h1 : evK θ F = Polynomial.aeval θ (algebraMap _ (Polynomial Qj) F) := by
    rw [Polynomial.aeval_def]
    show _ = Polynomial.eval₂ (algebraMap Qj Kbar) θ (F.map (algebraMap (Polynomial ℚ) Qj))
    rw [Polynomial.eval₂_map]; rfl
  rw [h1, ← RingHom.mem_ker, ← hker, ← hJI, Ideal.mem_comap]

end

/-! ## B. Clearing denominators: `(G, x) ↦ (27J/D, 46656 T/D)` -/

open Polynomial in
/-- `D = J − 1728`, a constant of `ℚ[J][T]`. -/
abbrev DJ : Polynomial (Polynomial ℚ) := C (X - C 1728)

/-- Evaluation `ℚ[G][x] → L` at `(G, x) = (a, b)`. -/
def ev2 {L : Type} [Field L] [CharZero L] (a b : L) : Polynomial (Polynomial ℚ) →+* L :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Rat.castHom L) a) b

open Polynomial in
/-- `Φ = D^k · P(27J/D, 46656T/D)` under every evaluation with `D ≠ 0`. -/
def Clears (P Φ : Polynomial (Polynomial ℚ)) (k : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [CharZero L] (e : Polynomial (Polynomial ℚ) →+* L), e DJ ≠ 0 →
    e Φ = e DJ ^ k * ev2 (27 * e (C X) / e DJ) (46656 * e X / e DJ) P

open Polynomial in
theorem clears_add {P Q Φ Ψ : Polynomial (Polynomial ℚ)} {k l : ℕ} (hP : Clears P Φ k)
    (hQ : Clears Q Ψ l) : Clears (P + Q) (Φ * DJ ^ l + Ψ * DJ ^ k) (k + l) := by
  intro L _ _ e he
  rw [map_add, map_mul, map_mul, map_pow, map_pow, hP L e he, hQ L e he, map_add]
  ring

open Polynomial in
theorem clears_mul {P Q Φ Ψ : Polynomial (Polynomial ℚ)} {k l : ℕ} (hP : Clears P Φ k)
    (hQ : Clears Q Ψ l) : Clears (P * Q) (Φ * Ψ) (k + l) := by
  intro L _ _ e he
  rw [map_mul, hP L e he, hQ L e he, map_mul]
  ring

open Polynomial in
theorem clears_CC (q : ℚ) : Clears (C (C q)) (C (C q)) 0 := by
  intro L _ _ e he
  have h1 : e (C (C q)) = (q : L) := eq_ratCast (e.comp (C.comp C)) q
  simp only [ev2, coe_eval₂RingHom, eval₂_C, pow_zero, one_mul, h1]
  rfl

open Polynomial in
theorem clears_CX : Clears (C X) (C (C 27 * X)) 1 := by
  intro L _ _ e he
  have h27 : e (C (C 27)) = 27 := by
    have := eq_ratCast (e.comp (C.comp C)) 27
    rwa [RingHom.comp_apply, RingHom.comp_apply, Rat.cast_ofNat] at this
  simp only [ev2, coe_eval₂RingHom, eval₂_C, eval₂_X, pow_one, map_mul, h27]
  field_simp

open Polynomial in
theorem clears_X : Clears X (C (C 46656) * X) 1 := by
  intro L _ _ e he
  have h : e (C (C 46656)) = 46656 := by
    have := eq_ratCast (e.comp (C.comp C)) 46656
    rwa [RingHom.comp_apply, RingHom.comp_apply, Rat.cast_ofNat] at this
  simp only [ev2, coe_eval₂RingHom, eval₂_X, pow_one, map_mul, h]
  field_simp

open Polynomial in
theorem exists_clears (P : Polynomial (Polynomial ℚ)) : ∃ Φ k, Clears P Φ k := by
  induction P using Polynomial.induction_on with
  | C a =>
    induction a using Polynomial.induction_on with
    | C q => exact ⟨_, _, clears_CC q⟩
    | add a b ha hb =>
      obtain ⟨Φ, k, h1⟩ := ha
      obtain ⟨Ψ, l, h2⟩ := hb
      rw [C_add]; exact ⟨_, _, clears_add h1 h2⟩
    | monomial n q ih =>
      obtain ⟨Φ, k, h1⟩ := ih
      rw [pow_succ, ← mul_assoc, C_mul]; exact ⟨_, _, clears_mul h1 clears_CX⟩
  | add P Q hP hQ =>
    obtain ⟨Φ, k, h1⟩ := hP
    obtain ⟨Ψ, l, h2⟩ := hQ
    exact ⟨_, _, clears_add h1 h2⟩
  | monomial n a ih =>
    obtain ⟨Φ, k, h1⟩ := ih
    rw [pow_succ, ← mul_assoc]; exact ⟨_, _, clears_mul h1 clears_X⟩

/-! ## C. The universal curve `y² = x³ − (G/4)x − G/4` and its two specializations -/

/-- `y² = x³ − (a/4)x − a/4` over a field. -/
def curveG {L : Type*} [Field L] (a : L) : WeierstrassCurve L := ⟨0, 0, 0, -(a / 4), -(a / 4)⟩

open Polynomial in
/-- The universal curve over `ℚ[G]`. -/
def WG : WeierstrassCurve (Polynomial ℚ) := ⟨0, 0, 0, C (-1 / 4) * X, C (-1 / 4) * X⟩

theorem WG_map {L : Type} [Field L] [CharZero L] (a : L) :
    WG.map (Polynomial.eval₂RingHom (Rat.castHom L) a) = curveG a := by
  ext <;> simp [WG, curveG] <;> ring

/-- `ev2 a b ΨSqₙ(WG) = ΨSqₙ(curveG a)(b)`. -/
theorem ev2_ΨSq {L : Type} [Field L] [CharZero L] (a b : L) (n : ℤ) :
    ev2 a b (WG.ΨSq n) = ((curveG a).ΨSq n).eval b := by
  rw [← WG_map, map_ΨSq, Polynomial.eval_map]; rfl

theorem EDSBar_eq : EDSBar = curveG (algebraMap Qj Kbar gDS) := by
  ext <;> simp [EDSBar, EDS, curveG, baseChange, map_div₀, map_ofNat]

theorem evK_CX (θ : Kbar) : evK θ (Polynomial.C Polynomial.X) = algebraMap Qj Kbar RatFunc.X := by
  simp [evK, RatFunc.algebraMap_X]

theorem evK_DJ (θ : Kbar) : evK θ DJ = algebraMap Qj Kbar (RatFunc.X - 1728) := by
  simp [evK, DJ, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem evK_DJ_ne (θ : Kbar) : evK θ DJ ≠ 0 := by
  rw [evK_DJ, ne_eq, map_eq_zero_iff _ (algebraMap Qj Kbar).injective]; exact X_sub_1728_ne_zero

/-- On the `\overline{ℚ(j)}` side a clearing of `ΨSqₙ(WG)` is `D^k · ΨSqₙ(E_j^{DS})((g_j − 27)θ)`. -/
theorem evK_clears {n : ℤ} {Φ : Polynomial (Polynomial ℚ)} {k : ℕ} (h : Clears (WG.ΨSq n) Φ k)
    (θ : Kbar) : evK θ Φ = evK θ DJ ^ k * (EDSBar.ΨSq n).eval (algebraMap Qj Kbar (gDS - 27) * θ) := by
  have h1 : 27 * evK θ (Polynomial.C Polynomial.X) / evK θ DJ = algebraMap Qj Kbar gDS := by
    rw [evK_CX, evK_DJ, gDS, map_div₀, map_mul, map_ofNat]
  have hX : evK θ Polynomial.X = θ := by simp [evK]
  have h2 : 46656 * evK θ Polynomial.X / evK θ DJ = algebraMap Qj Kbar (gDS - 27) * θ := by
    rw [hX, evK_DJ, gDS_sub, map_div₀, map_mul, map_ofNat, map_ofNat]
    ring
  rw [h Kbar (evK θ) (evK_DJ_ne θ), ev2_ΨSq, EDSBar_eq, h1, h2]


/-! ## C'. Points: the `\overline{ℚ(j)}` side -/

/-- A root `θ` of `ΨSqₙ(E_j^{DS})((g_j − 27)·)` is `w(P)` for a nonzero `n`-torsion point `P` of the kernel's
`E_j`; and `ΨSq_d` vanishes there for every `d` killing `P`. -/
theorem exists_point_of_root {n : ℕ} (θ : Kbar)
    (h : (EDSBar.ΨSq n).eval (algebraMap Qj Kbar (gDS - 27) * θ) = 0) :
    ∃ P : EjBar.toAffine.Point, P ≠ 0 ∧ n • P = 0 ∧ wOf P = θ ∧
      ∀ d : ℕ, d • P = 0 → (EDSBar.ΨSq d).eval (algebraMap Qj Kbar (gDS - 27) * θ) = 0 := by
  obtain ⟨y, hns, hz⟩ := EDSBar.eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero.mp h
  set Q : EDSBar.toAffine.Point := Affine.Point.some _ _ hns with hQdef
  have hQ0 : Q ≠ 0 := Affine.Point.some_ne_zero hns
  have hQn : n • Q = 0 := zsmul_fromAffine_eq_zero_iff.mp hz
  obtain ⟨u, hu2⟩ := exists_u
  have hu : u ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap Qj Kbar).injective] at hu2
    exact alpha_ne_zero hu2
  obtain ⟨ψ, hψ⟩ := exists_addEquiv_xCoord EjBar EDSBar (cDS u hu) (cDS_smul u hu2 hu)
  have hP0 : ψ.symm Q ≠ 0 := by rw [ne_eq, AddEquiv.map_eq_zero_iff]; exact hQ0
  refine ⟨ψ.symm Q, hP0, ?_, ?_, ?_⟩
  · rw [← map_nsmul, hQn, map_zero]
  · have hx := hψ (ψ.symm Q) hP0
    rw [AddEquiv.apply_symm_apply] at hx
    have hc : ((cDS u hu).u : Kbar) ^ 2 = algebraMap Qj Kbar alpha := hu2
    have hr : (cDS u hu).r = algebraMap Qj Kbar (-3 / 2) := rfl
    rw [hc, hr] at hx
    have hxQ : xCoord Q = algebraMap Qj Kbar (gDS - 27) * θ := rfl
    have hg : algebraMap Qj Kbar (gDS - 27) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (algebraMap Qj Kbar).injective, gDS_sub]
      exact div_ne_zero (by norm_num) X_sub_1728_ne_zero
    unfold wOf
    rw [← hx, hxQ]
    field_simp
  · intro d hd
    have : d • Q = 0 := by rw [← AddEquiv.apply_symm_apply ψ Q, ← map_nsmul, hd, map_zero]
    exact (EDSBar.eval_ΨSq_eq_zero_iff_zsmul_eq_zero hns d).mpr (zsmul_fromAffine_eq_zero_iff.mpr this)

/-! ## C''. Points: the complex side (the uniformization) -/

/-- `(u, 0, 0, 0) · y² = x³ − (g/4)x − g/4` with `g = g₂³/g₃²`, `u² = g₂/g₃`, is `ℂ/Λ`'s curve. -/
theorem curveC_smul (L : PeriodPair) (h2 : L.g₂ ≠ 0) (h3 : L.g₃ ≠ 0) (u : ℂ)
    (hu2 : u ^ 2 = L.g₂ / L.g₃) (hu : u ≠ 0) :
    (⟨Units.mk0 u hu, 0, 0, 0⟩ : VariableChange ℂ) • curveG (L.g₂ ^ 3 / L.g₃ ^ 2) =
      L.weierstrassCurve := by
  have hu2' : u ^ 2 * L.g₃ = L.g₂ := by rw [hu2]; field_simp
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, curveG, PeriodPair.weierstrassCurve_a₁, PeriodPair.weierstrassCurve_a₂,
    PeriodPair.weierstrassCurve_a₃, PeriodPair.weierstrassCurve_a₄, PeriodPair.weierstrassCurve_a₆,
    Units.val_inv_eq_inv_val, Units.val_mk0]
  all_goals field_simp
  · ring
  · ring
  · ring
  · linear_combination (L.g₂ * (u ^ 2 * L.g₃ + L.g₂)) * hu2'
  · linear_combination ((u ^ 2 * L.g₃) ^ 2 + u ^ 2 * L.g₃ * L.g₂ + L.g₂ ^ 2) * hu2'

/-- `n • toPoint z = toPoint (n z)`. -/
theorem nsmul_toPoint (L : PeriodPair) (hΔ : L.DiscriminantNeZero) (z : ℂ) (n : ℕ) :
    n • L.toPoint hΔ z = L.toPoint hΔ (n * z) := by
  have hU := L.isUniformization_toPoint hΔ
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ih, ← hU.1]
    congr 1; push_cast; ring

theorem toPoint_eq_zero_iff (L : PeriodPair) (hΔ : L.DiscriminantNeZero) (z : ℂ) :
    L.toPoint hΔ z = 0 ↔ z ∈ L.lattice :=
  ⟨(L.isUniformization_toPoint hΔ).2.2 z, L.toPoint_of_mem hΔ⟩

theorem discNeZero_pp (τ : UpperHalfPlane) : (pp τ).DiscriminantNeZero := disc_ppD_ne_zero τ

/-- **The division polynomial at Weber's point.** On `ℂ/⟨1, τ⟩` with `g₂g₃ ≠ 0`, `x = (g₂/g₃)℘(1/N)` is a root of
`ΨSqₙ(y² = x³ − (g/4)x − g/4)`, `g = g₂³/g₃²`, iff `n/N ∈ ⟨1, τ⟩`. -/
theorem eval_ΨSq_weber_eq_zero_iff (τ : UpperHalfPlane) (h2 : (pp τ).g₂ ≠ 0) (h3 : (pp τ).g₃ ≠ 0)
    {N : ℕ} (hN : 2 ≤ N) (n : ℕ) :
    ((curveG ((pp τ).g₂ ^ 3 / (pp τ).g₃ ^ 2)).ΨSq n).eval
        ((pp τ).g₂ / (pp τ).g₃ * (pp τ).weierstrassP (1 / N)) = 0 ↔
      (n : ℂ) * (1 / N) ∈ (pp τ).lattice := by
  set L := pp τ with hL
  have hΔ : L.DiscriminantNeZero := discNeZero_pp τ
  have hz : (1 / (N : ℂ)) ∉ L.lattice := by
    have := div_nat_not_mem τ (a := 1) (N := N) one_pos (by omega)
    rwa [Nat.cast_one] at this
  obtain ⟨u, hu2⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ / L.g₃) two_pos
  have hu : u ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, div_eq_zero_iff] at hu2
    rcases hu2 with h | h
    · exact h2 h
    · exact h3 h
  obtain ⟨e, he⟩ := exists_addEquiv_xCoord L.weierstrassCurve (curveG (L.g₂ ^ 3 / L.g₃ ^ 2)) _
    (curveC_smul L h2 h3 u hu2 hu)
  set Q₀ := L.toPoint hΔ (1 / N) with hQ₀
  have hQ₀0 : Q₀ ≠ 0 := by rw [hQ₀, ne_eq, toPoint_eq_zero_iff]; exact hz
  have hxQ₀ : xCoord Q₀ = L.weierstrassP (1 / N) := by
    rw [hQ₀, L.toPoint_of_notMem hΔ hz]; rfl
  have hQ0 : e Q₀ ≠ 0 := by rw [ne_eq, AddEquiv.map_eq_zero_iff]; exact hQ₀0
  obtain ⟨x, y, hns, hQ⟩ : ∃ x y, ∃ hns : (curveG (L.g₂ ^ 3 / L.g₃ ^ 2)).toAffine.Nonsingular x y,
      e Q₀ = Affine.Point.some x y hns := by
    cases h : e Q₀ with
    | zero => exact absurd h hQ0
    | some x y hns => exact ⟨x, y, hns, rfl⟩
  have hx : x = L.g₂ / L.g₃ * L.weierstrassP (1 / N) := by
    have := he Q₀ hQ₀0
    have h' : xCoord (Affine.Point.some x y hns) = x := rfl
    rw [hQ, hxQ₀, h'] at this
    simpa [hu2] using this
  rw [← hx, eval_ΨSq_eq_zero_iff_zsmul_eq_zero _ hns, zsmul_fromAffine_eq_zero_iff, ← hQ,
    ← map_nsmul, AddEquiv.map_eq_zero_iff, hQ₀, nsmul_toPoint, toPoint_eq_zero_iff]

end X1Igusa.Weber
