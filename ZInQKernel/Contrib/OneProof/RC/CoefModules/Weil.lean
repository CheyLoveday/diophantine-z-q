import ZInQKernel.Contrib.OneProof.RC.CoefModules.Cyclotomic
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Galois
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure
import ZInQKernel.Contrib.CloudB3RC53.Duality.BaseChangePerfect
import ZInQKernel.Contrib.CloudB3RC53.Duality.WeilPerfect

/-!
# Lane RC28 (coefficient modules), part 6: the Weil pairing on `E(K_S)[N]` and on `M_i`

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:arith-conjugate-duality`, tex 2798–2805:

> The Weil pairing gives the following `R_i`-linear perfect pairing: `M_i ⊗_{R_i} τ*M_i → R_i(1)`,
> `(v,w) ↦ e_2(v, ρ_T(τ)w)`. Indeed `ρ_T(τ)² = 1`, the two scalar characters multiply to one, and
> `e_2` transforms by the cyclotomic character. Thus `τ*M_i ≃ M_i^*(1)`.

This file builds the genuine Weil pairing on the genuine `G_{K,S}`-modules and proves the
"two scalar characters multiply to one" and "transforms by the cyclotomic character" parts; the
conjugation `ρ_T(τ)` is added in `Conjugate.lean`.

* `inclTors`: `E(K_S)[N] → E(K̄)[N]` (injective; bijective under `FullTorsion`).
* `weilS hμ`: **the Weil pairing** `E(K_S)[N] × E(K_S)[N] → ℤ/N`, the vendored Tau Ceti Weil
  pairing `e_N` over `K̄` (Silverman III.8.1) read through the discrete logarithm of a primitive
  `N`-th root of unity of `K_S`; `weilS_smul`: `e_N(σP, σQ) = χ_cyc(σ) e_N(P, Q)` for `σ ∈ G_{K,S}`
  (Galois equivariance of `e_N`, through any lift of `σ` to `G_K`); `weilS_bijective`,
  `weilS_flip_bijective`: perfect under `FullTorsion` (nondegeneracy of `e_N` and a count).
* `weilA`: its `A`-bilinear extension `(A ⊗ E[N]) × (A ⊗ E[N]) → A`, perfect for every `ℤ/N`-algebra
  `A` (the other group's `pairingBaseChange_perfect`); equivariant for `id ⊗ σ` up to `χ_cyc`.
* **`weilPairingM`: `M(α) × M(α⁻¹) → A(1)`** on the actual coefficient modules (`CoefMod`), with
  **`weilPairingM_smul`** — lane RC26's equivariance hypothesis `hβ` — and
  **`weilPairingM_bijective`, `weilPairingM_flip_bijective`** — its bijectivity hypotheses.

Kinds: definitions and PROVED (perfectness from the hypothesis `FullTorsion`, GLUE).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain TensorProduct WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside)
open ZInQ.Contrib.CloudB3RC53.Duality (baseChangeAct baseChangeAct_tmul pairingBaseChange
  pairingBaseChange_tmul pairingBaseChange_equivariant pairingBaseChange_perfect
  natCard_addMonoidHom_zmod_le finite_addMonoidHom)
open scoped WeierstrassCurve

/-- Equality in `K̄` is decided classically (needed by the point arithmetic). -/
instance decEqAlgClosure (K : Type) [Field K] : DecidableEq (AlgebraicClosure K) :=
  Classical.decEq _

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- The inclusion `K_S → K̄`. -/
def inclS (K : Type) [Field K] (S : Set (HeightOneSpectrum (𝓞 K))) :
    KS K S →ₐ[K] AlgebraicClosure K :=
  (unramifiedOutside K S).val

section Weil

variable (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N]

/-- `E(K̄)[N]`. -/
abbrev TorsBar : Type :=
  AddSubgroup.torsionBy ((W.baseChange (AlgebraicClosure K)).toAffine.Point) (N : ℤ)

/-- **`E(K_S)[N] → E(K̄)[N]`**, the point map along `K_S ⊂ K̄`. -/
def inclTors : TorsS K S W N →+ TorsBar W N where
  toFun P := ⟨Affine.Point.map (inclS K S) P.1, by
    have hP : (N : ℤ) • P.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp P.2
    change Affine.Point.map (inclS K S) P.1 ∈ Submodule.torsionBy ℤ _ (N : ℤ)
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hP, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

theorem coe_inclTors (P : TorsS K S W N) :
    ((inclTors W N P : TorsBar W N) : (W.baseChange (AlgebraicClosure K)).toAffine.Point) =
      Affine.Point.map (inclS K S) (P : (W.baseChange (KS K S)).toAffine.Point) := rfl

theorem inclTors_injective : Function.Injective (inclTors (S := S) W N) := fun P Q h =>
  Subtype.ext (Affine.Point.map_injective (inclS K S) (congrArg Subtype.val h))

theorem natCast_ne_zero_bar : ((N : ℕ) : AlgebraicClosure K) ≠ 0 :=
  Nat.cast_ne_zero.mpr (NeZero.ne N)

theorem natCard_torsBar : Nat.card (TorsBar W N) = N ^ 2 := by
  have h := (W.baseChange (AlgebraicClosure K)).natCard_torsionBy (n := (N : ℤ))
    (by exact_mod_cast natCast_ne_zero_bar (K := K) N)
  rw [Int.natAbs_natCast] at h
  exact h

instance finite_torsBar : Finite (TorsBar W N) :=
  (W.baseChange (AlgebraicClosure K)).finite_torsionBy (by exact_mod_cast NeZero.ne N)

/-- **Under `FullTorsion`, `E(K_S)[N] = E(K̄)[N]`.** Kind: PROVED. -/
theorem inclTors_bijective (hW : FullTorsion K S W N) : Function.Bijective (inclTors (S := S) W N) :=
  (inclTors_injective W N).bijective_of_nat_card_le (by rw [natCard_torsBar, hW])

/-- The Weil pairing `e_N` over `K̄` (vendored Tau Ceti, Silverman III.8.1). -/
def weilBar : TorsBar W N →+ TorsBar W N →+ Additive (rootsOfUnity N (AlgebraicClosure K)) :=
  TauCeti.Isogeny.weilPairing (W.baseChange (AlgebraicClosure K)) N (natCast_ne_zero_bar N)

theorem weilBar_skew (P Q : TorsBar W N) : weilBar W N P Q = -weilBar W N Q P := by
  have h := TauCeti.Isogeny.weilPairing_self (W.baseChange (AlgebraicClosure K)) N
    (natCast_ne_zero_bar N) (P + Q)
  have h1 := TauCeti.Isogeny.weilPairing_self (W.baseChange (AlgebraicClosure K)) N
    (natCast_ne_zero_bar N) P
  have h2 := TauCeti.Isogeny.weilPairing_self (W.baseChange (AlgebraicClosure K)) N
    (natCast_ne_zero_bar N) Q
  change weilBar W N (P + Q) (P + Q) = 0 at h
  change weilBar W N P P = 0 at h1
  change weilBar W N Q Q = 0 at h2
  have h' : weilBar W N P Q + weilBar W N Q P = 0 := by
    simp only [map_add, AddMonoidHom.add_apply, h1, h2, zero_add, add_zero] at h
    exact (add_comm _ _).trans h
  exact eq_neg_of_add_eq_zero_left h'

/-! ### The discrete logarithm and the roots of unity of `K_S` -/

variable {N}

/-- The `N`-th roots of unity of `K_S` map onto those of `K̄` (`|μ_N(K_S)| = N ≥ |μ_N(K̄)|`).
Kind: PROVED. -/
theorem rootsOfUnity_bijective (hμ : HasRootsOfUnity K S N) :
    Function.Bijective (restrictRootsOfUnity (inclS K S) N) := by
  have hinj : Function.Injective (restrictRootsOfUnity (inclS K S) N) := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    have := congrArg (fun u : rootsOfUnity N (AlgebraicClosure K) =>
      ((u : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) hxy
    simp only [restrictRootsOfUnity_coe_apply] at this
    exact (inclS K S).injective this
  have : Finite (rootsOfUnity N (AlgebraicClosure K)) := inferInstance
  refine hinj.bijective_of_nat_card_le ?_
  rw [card_rootsOfUnity_KS hμ]
  exact card_rootsOfUnity _ _

/-- The primitive `N`-th root of unity of `K̄` coming from `K_S`, as an element of `μ_N(K̄)`. -/
theorem isPrimitiveRoot_bar (hμ : HasRootsOfUnity K S N) :
    IsPrimitiveRoot (inclS K S (Classical.choose hμ)) N :=
  (Classical.choose_spec hμ).map_of_injective (inclS K S).injective

/-- **The discrete logarithm** `μ_N(K̄) ≃ ℤ/N` with respect to the primitive root coming from
`K_S`. -/
def logBar (hμ : HasRootsOfUnity K S N) : Additive (rootsOfUnity N (AlgebraicClosure K)) ≃+ ZMod N :=
  let hu := isPrimitiveRoot_bar hμ
  let u : (AlgebraicClosure K)ˣ := (hu.isUnit (NeZero.ne N)).unit
  have hpu : IsPrimitiveRoot u N := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    exact hu
  ((hpu.zmodEquivZPowers).trans (MulEquiv.subgroupCongr hpu.zpowers_eq).toAdditive).symm

/-- **A lift of `σ ∈ G_{K,S}` to `G_K` acts on `μ_N(K̄)` through the cyclotomic character of
`σ`.** Kind: PROVED. -/
theorem lift_rootsOfUnity (hμ : HasRootsOfUnity K S N) (σ : GKS K S)
    (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ' : ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x))
    (y : rootsOfUnity N (AlgebraicClosure K)) :
    restrictRootsOfUnity σ' N y = y ^ ((cycS hμ σ : (ZMod N)ˣ) : ZMod N).val := by
  obtain ⟨z, rfl⟩ := (rootsOfUnity_bijective hμ).2 y
  apply Subtype.ext
  apply Units.ext
  simp only [restrictRootsOfUnity_coe_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
  rw [hσ']
  have hz : ((z : (KS K S)ˣ) : KS K S) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp z.2, Units.val_one]
  rw [cycS_spec hμ σ hz, map_pow]

end Weil

/-! ### The Weil pairing on `E(K_S)[N]` -/

section WeilS

variable (W : WeierstrassCurve K) [W.IsElliptic] {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N)

/-- **The Weil pairing on `E(K_S)[N]` with values in `ℤ/N`**: `e_N` of the images in `E(K̄)[N]`,
read through the discrete logarithm (tex 2798–2804). -/
def weilS : TorsS K S W N →+ TorsS K S W N →+ ZMod N :=
  (AddMonoidHom.compHom (logBar hμ).toAddMonoidHom).comp
    (((weilBar W N).compl₂ (inclTors W N)).comp (inclTors W N))

theorem weilS_apply (P Q : TorsS K S W N) :
    weilS W hμ P Q = logBar hμ (weilBar W N (inclTors W N P) (inclTors W N Q)) := rfl

/-- The lift of `σ ∈ G_{K,S}` to `G_K = Gal(K̄/K)` (`K_S/K` is normal). -/
def liftGal (σ : GKS K S) : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  (galS K S σ).liftNormal (AlgebraicClosure K)

theorem liftGal_spec (σ : GKS K S) (x : KS K S) :
    liftGal σ (inclS K S x) = inclS K S (galS K S σ x) :=
  AlgEquiv.liftNormal_commutes (galS K S σ) (AlgebraicClosure K) x

/-- `ι(σ P) = σ̃ (ι P)` for the lift `σ̃` (`ι ∘ σ = σ̃ ∘ ι` on coordinates). Kind: PROVED. -/
theorem inclTors_smul (σ : GKS K S) (P : TorsS K S W N) :
    inclTors W N (σ • P) =
      Multiplicative.toAdd (W.torsionGaloisAction (N : ℤ) (liftGal σ)) (inclTors W N P) := by
  have hcomp : (liftGal σ).toAlgHom.comp (inclS K S) = (inclS K S).comp (galS K S σ).toAlgHom := by
    ext x
    exact liftGal_spec σ x
  apply Subtype.ext
  rw [torsionGaloisAction_apply_coe, pointGaloisAction_apply, coe_inclTors, coe_inclTors,
    coe_smul_torsS, Affine.Point.map_map, Affine.Point.map_map, hcomp]

/-- **The Weil pairing transforms by the cyclotomic character** (tex 2803–2804):
`e_N(σP, σQ) = χ_cyc(σ) e_N(P, Q)` for `σ ∈ G_{K,S}`. Kind: PROVED (Tau Ceti's Galois
equivariance of `e_N`, Silverman III.8.1(e), through the lift `σ̃`). -/
theorem weilS_smul (σ : GKS K S) (P Q : TorsS K S W N) :
    weilS W hμ (σ • P) (σ • Q) = ((cycS hμ σ : (ZMod N)ˣ) : ZMod N) * weilS W hμ P Q := by
  rw [weilS_apply, weilS_apply, inclTors_smul, inclTors_smul]
  have h := W.weilPairing_torsionGaloisAction N (natCast_ne_zero_bar N) (liftGal σ)
    (inclTors W N P) (inclTors W N Q)
  change weilBar W N _ _ = Additive.ofMul ((restrictRootsOfUnity (liftGal σ) N)
    (Additive.toMul (weilBar W N (inclTors W N P) (inclTors W N Q)))) at h
  rw [h, lift_rootsOfUnity hμ σ (liftGal σ) (liftGal_spec σ), ofMul_pow, ofMul_toMul, map_nsmul,
    nsmul_eq_mul, ZMod.natCast_zmod_val]

/-- `e_N` is nondegenerate on `E(K_S)[N]` under `FullTorsion`. Kind: PROVED. -/
theorem weilS_injective (hW : FullTorsion K S W N) : Function.Injective (weilS W hμ) := by
  refine (injective_iff_map_eq_zero _).mpr fun P hP => ?_
  apply inclTors_injective W N
  rw [map_zero]
  refine TauCeti.Isogeny.weilPairing_nondegenerate (W.baseChange (AlgebraicClosure K)) N
    (natCast_ne_zero_bar N) fun T => ?_
  obtain ⟨Q, rfl⟩ := (inclTors_bijective W N hW).2 T
  have := congrArg (fun f => f Q) hP
  simp only [AddMonoidHom.zero_apply] at this
  rw [weilS_apply] at this
  exact (logBar hμ).injective (this.trans (map_zero _).symm)

theorem weilS_flip_injective (hW : FullTorsion K S W N) :
    Function.Injective (weilS W hμ).flip := by
  refine (injective_iff_map_eq_zero _).mpr fun Q hQ => ?_
  apply inclTors_injective W N
  rw [map_zero]
  refine TauCeti.Isogeny.eq_zero_of_forall_weilPairing_eq_zero (W.baseChange (AlgebraicClosure K)) N
    (natCast_ne_zero_bar N) fun T => ?_
  obtain ⟨P, rfl⟩ := (inclTors_bijective W N hW).2 T
  have := congrArg (fun f => f P) hQ
  simp only [AddMonoidHom.zero_apply, AddMonoidHom.flip_apply] at this
  rw [weilS_apply] at this
  exact (logBar hμ).injective (this.trans (map_zero _).symm)

/-- **The Weil pairing on `E(K_S)[N]` is perfect** (both adjoints bijective) under `FullTorsion`.
Kind: PROVED (nondegeneracy and `|Hom(E[N], ℤ/N)| ≤ |E[N]|`, the other group's count). -/
theorem weilS_perfect (hW : FullTorsion K S W N) :
    Function.Bijective (weilS W hμ) ∧ Function.Bijective (weilS W hμ).flip := by
  have : Finite (TorsS K S W N) := finite_torsS (by exact_mod_cast NeZero.ne N)
  have := finite_addMonoidHom (TorsS K S W N) (ZMod N)
  exact ⟨(weilS_injective W hμ hW).bijective_of_nat_card_le
      (natCard_addMonoidHom_zmod_le _ N),
    (weilS_flip_injective W hμ hW).bijective_of_nat_card_le (natCard_addMonoidHom_zmod_le _ N)⟩

/-- `E(K_S)[N] ≃ (ℤ/N)²` under `FullTorsion` (vendored Tau Ceti basis of `E(K̄)[N]`). -/
theorem torsS_addEquiv_prod (hW : FullTorsion K S W N) :
    Nonempty (TorsS K S W N ≃+ ZMod N × ZMod N) := by
  obtain ⟨b⟩ := (W.baseChange (AlgebraicClosure K)).nonempty_basis_torsionBy N
    (natCast_ne_zero_bar N)
  exact ⟨(AddEquiv.ofBijective (inclTors W N) (inclTors_bijective W N hW)).trans
    (b.equivFun.toAddEquiv.trans (LinearEquiv.piFinTwo (ZMod N) (fun _ => ZMod N)).toAddEquiv)⟩

end WeilS

/-! ### The `A`-bilinear Weil pairing -/

section WeilA

variable (W : WeierstrassCurve K) [W.IsElliptic] {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N)
  (A : Type) [CommRing A] [Algebra (ZMod N) A]

/-- **The `A`-bilinear Weil pairing** `(A ⊗ E(K_S)[N]) × (A ⊗ E(K_S)[N]) → A`. -/
def weilA : A ⊗[ℤ] TorsS K S W N →ₗ[A] A ⊗[ℤ] TorsS K S W N →ₗ[A] A :=
  (pairingBaseChange (R := A) (weilS W hμ)).compr₂ (mulZMod A N)

theorem weilA_tmul (a b : A) (P Q : TorsS K S W N) :
    weilA W hμ A (a ⊗ₜ P) (b ⊗ₜ Q) = (a * b) * algebraMap (ZMod N) A (weilS W hμ P Q) := rfl

/-- **The `A`-bilinear Weil pairing is perfect** under `FullTorsion`. Kind: PROVED (the other
group's `pairingBaseChange_perfect` and `A ⊗ ℤ/N ≃ A`). -/
theorem weilA_perfect (hW : FullTorsion K S W N) :
    Function.Bijective (weilA W hμ A) ∧ Function.Bijective (weilA W hμ A).flip := by
  obtain ⟨φ⟩ := torsS_addEquiv_prod W hW
  obtain ⟨h1, h2⟩ := weilS_perfect W hμ hW
  obtain ⟨p1, p2⟩ := pairingBaseChange_perfect φ (AddEquiv.refl (ZMod N)) (weilS W hμ) h1 h2 A
  constructor
  · have h : ⇑(weilA W hμ A) =
        ⇑((LinearEquiv.refl A (A ⊗[ℤ] TorsS K S W N)).arrowCongr (mulZModEquiv A N)) ∘
          ⇑(pairingBaseChange (R := A) (weilS W hμ)) := by
      funext x
      exact LinearMap.ext fun y => rfl
    rw [h]
    exact (LinearEquiv.bijective _).comp p1
  · have h : ⇑(weilA W hμ A).flip =
        ⇑((LinearEquiv.refl A (A ⊗[ℤ] TorsS K S W N)).arrowCongr (mulZModEquiv A N)) ∘
          ⇑(pairingBaseChange (R := A) (weilS W hμ)).flip := by
      funext y
      exact LinearMap.ext fun x => rfl
    rw [h]
    exact (LinearEquiv.bijective _).comp p2

/-- The cyclotomic action of `G_{K,S}` on `ℤ/N` (a local instance in proofs). -/
abbrev cycAct : DistribMulAction (GKS K S) (ZMod N) where
  smul σ z := ((cycS hμ σ : (ZMod N)ˣ) : ZMod N) * z
  one_smul z := by
    change ((cycS hμ 1 : (ZMod N)ˣ) : ZMod N) * z = z
    rw [map_one, Units.val_one, one_mul]
  mul_smul σ τ z := by
    change ((cycS hμ (σ * τ) : (ZMod N)ˣ) : ZMod N) * z =
      ((cycS hμ σ : (ZMod N)ˣ) : ZMod N) * (((cycS hμ τ : (ZMod N)ˣ) : ZMod N) * z)
    rw [map_mul, Units.val_mul, mul_assoc]
  smul_zero σ := mul_zero _
  smul_add σ z w := mul_add _ z w

/-- **`id ⊗ σ` acts on the values by the cyclotomic character**:
`weilA (σ x) (σ y) = χ_cyc(σ) · weilA x y`. Kind: PROVED. -/
theorem weilA_baseChange (σ : GKS K S) (x y : A ⊗[ℤ] TorsS K S W N) :
    weilA W hμ A (baseChangeAct A _ σ x) (baseChangeAct A _ σ y) =
      ((cycA A hμ σ : Aˣ) : A) * weilA W hμ A x y := by
  let _ := cycAct hμ
  have he : ∀ (σ : GKS K S) (P Q : TorsS K S W N),
      weilS W hμ (σ • P) (σ • Q) = σ • weilS W hμ P Q := fun σ P Q => weilS_smul W hμ σ P Q
  change mulZMod A N (pairingBaseChange (weilS W hμ) (baseChangeAct A _ σ x)
    (baseChangeAct A _ σ y)) = _
  rw [pairingBaseChange_equivariant (weilS W hμ) he σ x y]
  change _ = ((cycA A hμ σ : Aˣ) : A) * mulZMod A N (pairingBaseChange (weilS W hμ) x y)
  generalize pairingBaseChange (weilS W hμ) x y = z
  induction z using TensorProduct.inductionOn with
  | tmul a w =>
    rw [baseChangeAct_tmul, mulZMod_tmul, mulZMod_tmul]
    change a * algebraMap (ZMod N) A (((cycS hμ σ : (ZMod N)ˣ) : ZMod N) * w) = _
    rw [map_mul]
    change _ = (algebraMap (ZMod N) A ((cycS hμ σ : (ZMod N)ˣ) : ZMod N)) * _
    ring
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, mul_add]

end WeilA

/-! ### The Weil pairing on the actual coefficient modules -/

section WeilM

variable (W : WeierstrassCurve K) [W.IsElliptic] {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N)
  (A : Type) [CommRing A] [Algebra (ZMod N) A] (α : GKS K S →* Aˣ)

/-- **The Weil pairing on the actual coefficient modules**
`M(α) × M(α⁻¹) → A(1)`, `(E[N] ⊗ A)(α) × (E[N] ⊗ A)(α⁻¹) → A(1)` (tex 2798–2804: the two scalar
characters multiply to one). -/
def weilPairingM :
    CoefMod A α (TorsS K S W N) →ₗ[A] CoefMod A (charInv α) (TorsS K S W N) →ₗ[A] Tate1 A hμ :=
  weilA W hμ A

theorem weilPairingM_apply (x : CoefMod A α (TorsS K S W N))
    (y : CoefMod A (charInv α) (TorsS K S W N)) :
    (CharMod.equiv A (cycA A hμ)) (weilPairingM W hμ A α x y) =
      weilA W hμ A (show A ⊗[ℤ] TorsS K S W N from x) (show A ⊗[ℤ] TorsS K S W N from y) := rfl

/-- **Equivariance** (lane RC26's hypothesis `hβ`):
`β(g a, g b) = g β(a, b)` for `g ∈ G_{K,S}`. Kind: PROVED. -/
theorem weilPairingM_smul (g : GKS K S) (a : CoefMod A α (TorsS K S W N))
    (b : CoefMod A (charInv α) (TorsS K S W N)) :
    weilPairingM W hμ A α (g • a) (g • b) = g • weilPairingM W hμ A α a b := by
  change weilA W hμ A (((α g : Aˣ) : A) • baseChangeAct A _ g (show A ⊗[ℤ] TorsS K S W N from a))
      ((((charInv α) g : Aˣ) : A) • baseChangeAct A _ g (show A ⊗[ℤ] TorsS K S W N from b)) =
    ((cycA A hμ g : Aˣ) : A) * weilA W hμ A (show A ⊗[ℤ] TorsS K S W N from a)
      (show A ⊗[ℤ] TorsS K S W N from b)
  rw [LinearMap.map_smul₂, map_smul, weilA_baseChange, smul_eq_mul, smul_eq_mul, charInv_apply,
    ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- **Perfectness** (lane RC26's hypotheses `hb`, `hb'`) under `FullTorsion`. Kind: PROVED. -/
theorem weilPairingM_bijective (hW : FullTorsion K S W N) :
    Function.Bijective (weilPairingM W hμ A α) :=
  (weilA_perfect W hμ A hW).1

theorem weilPairingM_flip_bijective (hW : FullTorsion K S W N) :
    Function.Bijective (weilPairingM W hμ A α).flip :=
  (weilA_perfect W hμ A hW).2

end WeilM

end ZInQ.Manuscript.RC.CoefModules
