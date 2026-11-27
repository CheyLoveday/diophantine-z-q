import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCompQuot
import ZInQKernel.Contrib.RC53Assist.Finiteness.GaloisFiniteness

/-!
# Theorem 5.3, Lane RC37: the coefficient part of the Kummer comparison

Manuscript `diophantine_zq.tex`, the coefficient comparison behind the universal-coefficient
step `H¹(C_K) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(E/K)` (tex 4005–4014). The compact Kummer complex `C_K`
(`compactKummerComplex S W hFull`) has the Tate module `T₂E` as coefficients; the target Selmer
group lives on the discrete module `E[2^∞]`. The comparison of coefficients is

`C¹_cont(G_{K,S}, T₂E) ⊗ ℚ₂/ℤ₂ → C¹_cont(G_{K,S}, E[2^∞])`,   `c ⊗ 2^{-m} ↦ (c mod 2^m)`,

followed by inflation to the group `G'` of the target (for the arithmetic application,
`G' = G_K` inside `Gal(ℚˢ/ℚ)` and the coefficient module `E(ℚˢ)[2^∞]`).

This file works with an abstract **level datum** `KcLevelData`: a continuous homomorphism
`ρ : G' → G_{K,S}` and additive maps `J m : E(K_S)[2^m] → M'`, equivariant along `ρ`, compatible
with the inclusions of the levels, injective, jointly surjective, with `ρ` surjective. From it:

* `kcTheta D m n : C_K^n → C^n_cont(G', M')`, the level-`m` reduction (`red`, lane RC53's
  reduction of continuous Tate cochains) of the global component followed by inflation;
  `kcTheta_d` (a cochain map), `kcTheta_shift` (`θ_{m+j}(2^j x) = θ_m(x)`), `kcTheta_zero_level`;
* `kcGamma D n : C_K^n ⊗ ℚ₂ → C^n_cont(G', M')`, `2^{-m} ⊗ x ↦ θ_m(x)` (`kcGamma_frac`);
* **`kcPsi D : C_K ⊗ ℚ₂/ℤ₂ → C^•_cont(G', M')`**, a morphism of complexes of abelian groups out
  of the RC53 group's coefficient quotient, with `kcPsi_frac : ψ [x/2^m] = θ_m(x)`.

Kinds: definitions and PROVED.
-/

noncomputable section

set_option maxHeartbeats 1600000

namespace ZInQ.Manuscript.RC

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ZInQ.Manuscript.RC53Assist.CentralUniversal ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.Finiteness
open scoped TensorProduct

attribute [local instance] levTop continuousSMul_lev

/-! ### The level datum -/

section Data

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K)
  (G' : Type) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  (M' : Type) [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M']

/-- **A level datum for the coefficient comparison**: a continuous surjective homomorphism
`ρ : G' → G_{K,S}` and additive maps `J m : E(K_S)[2^m] → M'`, equivariant along `ρ`, compatible
with the inclusions of the levels (they depend only on the underlying point of `E(K_S)`),
injective, and jointly surjective. For the arithmetic application `ρ` is restriction along an
embedding `K_S ⊂ ℚˢ` and `J m` the induced point map into `E(ℚˢ)[2^∞]` (the identification
`T₂E ⊗ ℚ₂/ℤ₂ = E[2^∞]` in the limit). Kind: definition. -/
structure KcLevelData where
  /-- The homomorphism of Galois groups. -/
  ρ : G' →ₜ* GKS K S
  /-- The level maps. -/
  J : ∀ m : ℕ, Lev K S W m →+ M'
  J_smul : ∀ (m : ℕ) (g : G') (P : Lev K S W m), J m (ρ g • P) = g • J m P
  J_compat : ∀ (m m' : ℕ) (P : Lev K S W m) (P' : Lev K S W m'),
    (P : Pt K S W) = (P' : Pt K S W) → J m P = J m' P'
  J_inj : ∀ (m : ℕ) (P : Lev K S W m), J m P = 0 → P = 0
  J_surj : ∀ x : M', ∃ (m : ℕ) (P : Lev K S W m), J m P = x
  ρ_surj : Function.Surjective ρ

end Data

/-! ### Tate points of two-power multiples -/

section TatePoints

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K}

/-- `(2^j t)_{m+j} = t_m` in `E(K_S)`. Kind: PROVED. -/
theorem kc_pt_two_pow_smul (t : TateS K S W) (m j : ℕ) :
    ((2 : ℤ_[2]) ^ j • t).pt (m + j) = t.pt m := by
  rw [TateS.pt_padicSmul]
  have hlev : (2 ^ (m + j) : ℕ) • t.pt (m + j) = 0 := two_pow_nsmul_lev (projLev (m + j) t)
  rw [show ((2 : ℤ_[2]) ^ j) = ((2 ^ j : ℕ) : ℤ_[2]) by push_cast; rfl,
    resN_natCast, nsmul_mod_eq hlev, t.two_pow_smul_pt m j]

/-- A level-zero point is zero. Kind: PROVED. -/
theorem kc_lev_zero_eq (P : Lev K S W 0) : P = 0 := by
  apply Subtype.ext
  have h := two_pow_nsmul_lev P
  simpa using h

end TatePoints

/-! ### Reduction and inflation of the global component -/

section Theta

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M']
  (D : KcLevelData S W G' M')

/-- The terms of the compact Kummer complex are torsion-free (the tree's
`compactKummerTerm_isTorsionFree`, as an instance). Kind: PROVED. -/
instance kcCompactTerm_isTorsionFree (n : ℤ) :
    Module.IsTorsionFree ℤ_[2] ((compactKummerComplex S W hFull).X n) :=
  compactKummerTerm_isTorsionFree S W hFull n

include hFull in
/-- The Tate module is the two-adic limit of its levels. Kind: PROVED. -/
theorem kc_isTwoAdicLimit :
    IsTwoAdicLimit (T := TateS K S W) (L := fun k => Lev K S W k) (fun k => projLev k) := by
  have : HasFullTwoTorsion K S W := ⟨hFull⟩
  exact isTwoAdicLimit_tate K S W

/-- **Inflation of level-`m` cochains** along `ρ` and `J m`. Kind: definition. -/
def kcInflate (m : ℕ) : contCochains ℤ (GKS K S) (Lev K S W m) ⟶ contCochains ℤ G' M' :=
  contCochainsMap D.ρ (D.J m).toIntLinearMap continuous_of_discreteTopology
    (fun g P => D.J_smul m g P)

omit [W.IsElliptic] in
/-- The value of an inflated cochain. Kind: PROVED. -/
theorem kcInflate_apply (m : ℕ) (j : ℕ) (c : (contCochains ℤ (GKS K S) (Lev K S W m)).X j)
    (x : Fin j → G') :
    cochainFun (((kcInflate D m).f j).hom c) x = D.J m (cochainFun c (D.ρ ∘ x)) :=
  rfl

/-- The global component of a cochain of `C_K`. Kind: definition. -/
def kcGlob (n : ℤ) : (compactKummerComplex S W hFull).X n →+
    (natCx (contCochains ℤ_[2] (GKS K S) (TateS K S W))).X n where
  toFun x := (show selT (tateKummerSelData S W hFull) n from x).1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The global component is `ℤ₂`-linear. Kind: PROVED. -/
theorem kcGlob_smul (n : ℤ) (a : ℤ_[2]) (x : (compactKummerComplex S W hFull).X n) :
    kcGlob hFull n (a • x) = a • kcGlob hFull n x :=
  rfl

/-- The global component commutes with the differentials. Kind: PROVED. -/
theorem kcGlob_d (n : ℤ) (x : (compactKummerComplex S W hFull).X n) :
    kcGlob hFull (n + 1) (((compactKummerComplex S W hFull).d n (n + 1)).hom x) =
      (natCx (contCochains ℤ_[2] (GKS K S) (TateS K S W))).d n (n + 1) rfl
        (kcGlob hFull n x) := by
  exact congrArg Prod.fst
    (GCx.toCC_d_hom (selCx (tateKummerSelData S W hFull)) n (n + 1) rfl x)

/-- **`θ_m`: reduce the global component modulo `2^m` and inflate.** Kind: definition. -/
def kcTheta (m : ℕ) (n : ℤ) :
    (compactKummerComplex S W hFull).X n →+ (natCx (contCochains ℤ G' M')).X n where
  toFun x := natF (kcInflate D m) n
    (red (GKS K S) (fun k => projLev k) (kc_isTwoAdicLimit hFull) m n (kcGlob hFull n x))
  map_zero' := by
    change natF (kcInflate D m) n (red (GKS K S) (fun k => projLev k)
      (kc_isTwoAdicLimit hFull) m n (kcGlob hFull n 0)) = 0
    rw [map_zero (kcGlob hFull n), map_zero (red (GKS K S) (fun k => projLev k)
      (kc_isTwoAdicLimit hFull) m n)]
    exact map_zero (natF (kcInflate D m) n)
  map_add' x y := by
    change natF (kcInflate D m) n (red (GKS K S) (fun k => projLev k)
      (kc_isTwoAdicLimit hFull) m n (kcGlob hFull n (x + y))) =
      natF (kcInflate D m) n (red (GKS K S) (fun k => projLev k)
        (kc_isTwoAdicLimit hFull) m n (kcGlob hFull n x)) +
      natF (kcInflate D m) n (red (GKS K S) (fun k => projLev k)
        (kc_isTwoAdicLimit hFull) m n (kcGlob hFull n y))
    rw [map_add (kcGlob hFull n), map_add (red (GKS K S) (fun k => projLev k)
      (kc_isTwoAdicLimit hFull) m n)]
    exact map_add (natF (kcInflate D m) n) _ _

/-- `θ_m` in a natural degree, on values. Kind: PROVED. -/
theorem kcTheta_apply (m j : ℕ) (x : (compactKummerComplex S W hFull).X (Int.ofNat j))
    (g : Fin j → G') :
    cochainFun (k := ℤ) (G := G') (M := M') (j := j) (kcTheta hFull D m (Int.ofNat j) x) g =
      D.J m (projLev m (cochainFun (k := ℤ_[2]) (G := GKS K S) (M := TateS K S W) (j := j)
        (kcGlob hFull (Int.ofNat j) x) (D.ρ ∘ g))) :=
  rfl

/-- **`θ_m` is a cochain map.** Kind: PROVED. -/
theorem kcTheta_d (m : ℕ) (n : ℤ) (x : (compactKummerComplex S W hFull).X n) :
    kcTheta hFull D m (n + 1) (((compactKummerComplex S W hFull).d n (n + 1)).hom x) =
      (natCx (contCochains ℤ G' M')).d n (n + 1) rfl (kcTheta hFull D m n x) := by
  change natF (kcInflate D m) (n + 1) (red (GKS K S) (fun k => projLev k)
      (kc_isTwoAdicLimit hFull) m (n + 1)
      (kcGlob hFull (n + 1) (((compactKummerComplex S W hFull).d n (n + 1)).hom x))) =
    natD (contCochains ℤ G' M') n (n + 1) rfl (natF (kcInflate D m) n
      (red (GKS K S) (fun k => projLev k) (kc_isTwoAdicLimit hFull) m n (kcGlob hFull n x)))
  rw [kcGlob_d, red_comm (kc_isTwoAdicLimit hFull) (isEquivariantLevels_tate K S W) m n (n + 1)
    rfl]
  exact natF_comm (kcInflate D m) n (n + 1) rfl _

/-- **`θ_{m+j}(2^j x) = θ_m(x)`.** Kind: PROVED. -/
theorem kcTheta_shift (m j : ℕ) (n : ℤ) (x : (compactKummerComplex S W hFull).X n) :
    kcTheta hFull D (m + j) n ((2 : ℤ_[2]) ^ j • x) = kcTheta hFull D m n x := by
  cases n with
  | negSucc a => rfl
  | ofNat i =>
    apply cochain_ext
    intro g
    refine (kcTheta_apply hFull D (m + j) i _ g).trans
      (Eq.trans ?_ (kcTheta_apply hFull D m i x g).symm)
    apply D.J_compat
    change (((2 : ℤ_[2]) ^ j • cochainFun (k := ℤ_[2]) (G := GKS K S) (M := TateS K S W)
      (j := i) (kcGlob hFull (Int.ofNat i) x) (D.ρ ∘ g)) : TateS K S W).pt (m + j) = _
    exact kc_pt_two_pow_smul _ m j

/-- **`θ_0 = 0`** (the level-zero coefficients vanish). Kind: PROVED. -/
theorem kcTheta_zero_level (n : ℤ) (x : (compactKummerComplex S W hFull).X n) :
    kcTheta hFull D 0 n x = 0 := by
  cases n with
  | negSucc a => rfl
  | ofNat i =>
    apply cochain_ext
    intro g
    refine (kcTheta_apply hFull D 0 i x g).trans ?_
    rw [kc_lev_zero_eq (projLev 0 _), map_zero]
    rfl

end Theta

/-! ### The rational map `2^{-m} ⊗ x ↦ θ_m(x)` -/

section Gamma

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M']
  (D : KcLevelData S W G' M')

/-- The least two-power denominator of a two-adic number. Kind: definition. -/
def kcMu (q : ℚ_[2]) : ℕ := Nat.find (kc_exists_two_pow_mul_norm_le q)

theorem kcMu_spec (q : ℚ_[2]) : ‖(2 : ℚ_[2]) ^ kcMu q * q‖ ≤ 1 :=
  Nat.find_spec (kc_exists_two_pow_mul_norm_le q)

theorem kcMu_le {q : ℚ_[2]} {m : ℕ} (h : ‖(2 : ℚ_[2]) ^ m * q‖ ≤ 1) : kcMu q ≤ m :=
  Nat.find_min' (kc_exists_two_pow_mul_norm_le q) h

/-- Raising the exponent keeps a two-adic multiple integral. Kind: PROVED. -/
theorem kc_norm_le_of_le {q : ℚ_[2]} {a b : ℕ} (h : ‖(2 : ℚ_[2]) ^ a * q‖ ≤ 1) (hab : a ≤ b) :
    ‖(2 : ℚ_[2]) ^ b * q‖ ≤ 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_comm ((2 : ℚ_[2]) ^ a), mul_assoc, norm_mul]
  have h2 : ‖(2 : ℚ_[2]) ^ j‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (by
      rw [show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_num, Padic.norm_p]
      norm_num)
  calc ‖(2 : ℚ_[2]) ^ j‖ * ‖(2 : ℚ_[2]) ^ a * q‖ ≤ 1 * 1 :=
        mul_le_mul h2 h (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The integral numerator at a given exponent. Kind: definition. -/
abbrev kcNum (q : ℚ_[2]) (m : ℕ) (h : ‖(2 : ℚ_[2]) ^ m * q‖ ≤ 1) : ℤ_[2] :=
  Padic.lift ((2 : ℚ_[2]) ^ m * q) h

theorem kcNum_coe (q : ℚ_[2]) (m : ℕ) (h : ‖(2 : ℚ_[2]) ^ m * q‖ ≤ 1) :
    ((kcNum q m h : ℤ_[2]) : ℚ_[2]) = (2 : ℚ_[2]) ^ m * q :=
  PadicInt.coe_lift h

/-- The bilinear value `q ⊗ x ↦ θ_μ(2^μ q · x)`. Kind: definition. -/
def kcB (n : ℤ) (q : ℚ_[2]) (x : (compactKummerComplex S W hFull).X n) :
    (natCx (contCochains ℤ G' M')).X n :=
  kcTheta hFull D (kcMu q) n (kcNum q (kcMu q) (kcMu_spec q) • x)

/-- **Independence of the exponent.** Kind: PROVED. -/
theorem kcB_eq (n : ℤ) (q : ℚ_[2]) (m : ℕ) (h : ‖(2 : ℚ_[2]) ^ m * q‖ ≤ 1)
    (x : (compactKummerComplex S W hFull).X n) :
    kcB hFull D n q x = kcTheta hFull D m n (kcNum q m h • x) := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (kcMu_le h)
  subst hj
  have he : kcNum q (kcMu q + j) h = (2 : ℤ_[2]) ^ j * kcNum q (kcMu q) (kcMu_spec q) := by
    apply PadicInt.ext
    rw [PadicInt.coe_mul, kcNum_coe, kcNum_coe, PadicInt.coe_pow,
      show ((2 : ℤ_[2]) : ℚ_[2]) = 2 from rfl, pow_add]
    ring
  rw [he, mul_smul, add_comm (kcMu q) j, show j + kcMu q = kcMu q + j from add_comm _ _,
    kcTheta_shift]
  rfl

/-- The bilinear map. Kind: definition. -/
def kcGammaBil (n : ℤ) :
    ℚ_[2] →+ (compactKummerComplex S W hFull).X n →+ (natCx (contCochains ℤ G' M')).X n where
  toFun q :=
    { toFun := fun x => kcB hFull D n q x
      map_zero' := by
        rw [kcB, smul_zero, map_zero]
      map_add' := fun x y => by
        rw [kcB, kcB, kcB, smul_add, map_add] }
  map_zero' := by
    ext x
    have h0 : ‖(2 : ℚ_[2]) ^ 0 * 0‖ ≤ 1 := by simp
    change kcB hFull D n 0 x = 0
    rw [kcB_eq hFull D n 0 0 h0 x, kcTheta_zero_level]
  map_add' q q' := by
    ext x
    change kcB hFull D n (q + q') x = kcB hFull D n q x + kcB hFull D n q' x
    have h1 : ‖(2 : ℚ_[2]) ^ (kcMu q + kcMu q') * q‖ ≤ 1 :=
      kc_norm_le_of_le (kcMu_spec q) (Nat.le_add_right _ _)
    have h2 : ‖(2 : ℚ_[2]) ^ (kcMu q + kcMu q') * q'‖ ≤ 1 :=
      kc_norm_le_of_le (kcMu_spec q') (Nat.le_add_left _ _)
    have h3 : ‖(2 : ℚ_[2]) ^ (kcMu q + kcMu q') * (q + q')‖ ≤ 1 := by
      rw [mul_add]
      exact (Padic.nonarchimedean _ _).trans (max_le h1 h2)
    rw [kcB_eq hFull D n _ _ h3, kcB_eq hFull D n _ _ h1, kcB_eq hFull D n _ _ h2, ← map_add,
      ← add_smul]
    congr 2
    apply PadicInt.ext
    rw [PadicInt.coe_add, kcNum_coe, kcNum_coe, kcNum_coe, mul_add]

/-- The bilinear map is `ℤ₂`-balanced. Kind: PROVED. -/
theorem kcGammaBil_balanced (n : ℤ) (r : ℤ_[2]) (q : ℚ_[2])
    (x : (compactKummerComplex S W hFull).X n) :
    kcGammaBil hFull D n (r • q) x = kcGammaBil hFull D n q (r • x) := by
  change kcB hFull D n (r • q) x = kcB hFull D n q (r • x)
  have h1 : ‖(2 : ℚ_[2]) ^ kcMu q * (r • q)‖ ≤ 1 := by
    change ‖(2 : ℚ_[2]) ^ kcMu q * ((r : ℚ_[2]) * q)‖ ≤ 1
    rw [mul_left_comm, norm_mul]
    calc ‖(r : ℚ_[2])‖ * ‖(2 : ℚ_[2]) ^ kcMu q * q‖ ≤ 1 * 1 :=
          mul_le_mul r.2 (kcMu_spec q) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [kcB_eq hFull D n _ _ h1, kcB, smul_smul]
  congr 2
  apply PadicInt.ext
  rw [PadicInt.coe_mul, kcNum_coe, kcNum_coe]
  change (2 : ℚ_[2]) ^ kcMu q * ((r : ℚ_[2]) * q) = (2 : ℚ_[2]) ^ kcMu q * q * (r : ℚ_[2])
  ring

/-- **The rational map** `C_K^n ⊗ ℚ₂ → C^n_cont(G', M')`. Kind: definition. -/
def kcGamma (n : ℤ) :
    (rationalCoefficientComplex (compactKummerComplex S W hFull)).X n →+
      (natCx (contCochains ℤ G' M')).toCC.X n :=
  TensorProduct.liftAddHom (kcGammaBil hFull D n) (kcGammaBil_balanced hFull D n)

theorem kcGamma_tmul (n : ℤ) (q : ℚ_[2]) (x : (compactKummerComplex S W hFull).X n) :
    kcGamma hFull D n (kcTmul _ q x) = kcB hFull D n q x :=
  TensorProduct.liftAddHom_tmul _ _ _ _

/-- **`2^{-m} ⊗ x ↦ θ_m(x)`.** Kind: PROVED. -/
theorem kcGamma_frac (n : ℤ) (m : ℕ) (x : (compactKummerComplex S W hFull).X n) :
    kcGamma hFull D n (kcTmul _ ((2 : ℚ_[2]) ^ m)⁻¹ x) = kcTheta hFull D m n x := by
  have h : ‖(2 : ℚ_[2]) ^ m * ((2 : ℚ_[2]) ^ m)⁻¹‖ ≤ 1 := by
    rw [kc_two_pow_mul_inv, norm_one]
  rw [kcGamma_tmul, kcB_eq hFull D n _ m h]
  have h1 : kcNum ((2 : ℚ_[2]) ^ m)⁻¹ m h = 1 := by
    apply PadicInt.ext
    rw [kcNum_coe, kc_two_pow_mul_inv, PadicInt.coe_one]
  rw [h1, one_smul]

/-- The rational map kills the integral image. Kind: PROVED. -/
theorem kcGamma_unit (n : ℤ) (x : (compactKummerComplex S W hFull).X n) :
    kcGamma hFull D n (kcTmul _ 1 x) = 0 := by
  have h := kcGamma_frac hFull D n 0 x
  rw [pow_zero, inv_one] at h
  rw [h, kcTheta_zero_level]
  rfl

/-- The rational map commutes with the differentials. Kind: PROVED. -/
theorem kcGamma_d (n : ℤ)
    (z : (rationalCoefficientComplex (compactKummerComplex S W hFull)).X n) :
    ((natCx (contCochains ℤ G' M')).toCC.d n (n + 1)).hom (kcGamma hFull D n z) =
      kcGamma hFull D (n + 1)
        (((rationalCoefficientComplex (compactKummerComplex S W hFull)).d n (n + 1)).hom z) := by
  obtain ⟨m, x, rfl⟩ := kc_rat_normal _ n z
  refine (GCx.toCC_d_hom (natCx (contCochains ℤ G' M')) n (n + 1) rfl _).trans ?_
  rw [kc_rat_d_tmul, kcGamma_frac, kcGamma_frac, kcTheta_d]

/-- **The coefficient comparison `ψ : C_K ⊗ ℚ₂/ℤ₂ → C^•_cont(G', M')`**, a morphism of
complexes of abelian groups (`[x/2^m] ↦ θ_m(x)`). Kind: definition. -/
def kcPsi : integerCoefficientComplex (coefficientQuotientComplex
    (compactKummerComplex S W hFull)) ⟶ (natCx (contCochains ℤ G' M')).toCC :=
  kcDesc (compactKummerComplex S W hFull) (natCx (contCochains ℤ G' M')).toCC
    (kcGamma hFull D) (kcGamma_unit hFull D) (kcGamma_d hFull D)

/-- **`ψ [x/2^m] = θ_m(x)`.** Kind: PROVED. -/
theorem kcPsi_frac (n : ℤ) (m : ℕ) (x : (compactKummerComplex S W hFull).X n) :
    ((kcPsi hFull D).f n).hom (kcFrac _ m x) = kcTheta hFull D m n x := by
  rw [kcPsi, kcDesc_frac, kcGamma_frac]

end Gamma

end ZInQ.Manuscript.RC
