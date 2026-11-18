import ZInQKernel.Contrib.OneProof.RC.CoefModules.CoefModule
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.RootsOfUnity

/-!
# Lane RC28 (coefficient modules), part 5: the cyclotomic twist `A_i(1)` over `G_{K,S}`

Manuscript `diophantine_zq.tex` (11/5), tex 2798–2804: the Weil pairing takes values in
`R_i(1)`, "and `e_2` transforms by the cyclotomic character".

Over `K_S` containing a primitive `N`-th root of unity (`HasRootsOfUnity`; for `N = 2^i` it
follows from `FullTorsion` by the Weil pairing, `hasRootsOfUnity_of_fullTorsion`, vendored Tau
Ceti), Mathlib's `modularCyclotomicCharacter` gives the genuine cyclotomic character
`cycS : G_{K,S} → (ℤ/N)^×` (`σ ζ = ζ^{cycS σ}` for every `N`-th root of unity `ζ ∈ K_S`, with open
kernel). For a commutative `ℤ/N`-algebra `A` (such as `A_i`, `N = 2^i`):

* `cycA`: `cycS` with values in `A^×`;
* `Tate1 A`: **`A(1)`**, the rank-one module `CharMod A cycA`;
* `isCyclotomicTwist_tate1`: it satisfies lane RC26's `IsCyclotomicTwist K S A (Tate1 …)`
  (`T ≅ R(1)`: free of rank one, Galois acting through the cyclotomic character modulo `N`,
  `K_S ⊇ μ_N` with `N` elements) — the hypothesis of the Nekovář PRINTs;
* `mulZMod`: the `A`-linear isomorphism `A ⊗_ℤ ℤ/N ≃ A` (`a ⊗ z ↦ a z`), used to read values of
  pairings into `ℤ/N` in `A`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open NumberField IsDedekindDomain TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex (GKS IsCyclotomicTwist toGal)
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside)

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- `K_S` contains a primitive `N`-th root of unity. -/
def HasRootsOfUnity (N : ℕ) : Prop := ∃ ζ : KS K S, IsPrimitiveRoot ζ N

/-- **`E[N] ⊆ E(K_S)` implies `μ_N ⊆ K_S`** (Silverman III.8.1.1, through the Weil pairing;
vendored Tau Ceti `exists_isPrimitiveRoot_of_natCard_torsionBy`). Kind: PROVED. -/
theorem hasRootsOfUnity_of_fullTorsion (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N]
    (hW : FullTorsion K S W N) : HasRootsOfUnity K S N := by
  have hN : ((N : ℕ) : KS K S) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  exact (W.baseChange (KS K S)).exists_isPrimitiveRoot_of_natCard_torsionBy hN hW

/-- `G_{K,S} → Aut(K_S)` as ring automorphisms. -/
def ringAutHom : GKS K S →* (KS K S ≃+* KS K S) where
  toFun σ := (galS K S σ).toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

variable {K S}

section Cyc

variable {N : ℕ} [NeZero N]

theorem card_rootsOfUnity_KS (hμ : HasRootsOfUnity K S N) :
    Nat.card (rootsOfUnity N (KS K S)) = N :=
  IsPrimitiveRoot.card_rootsOfUnity (Classical.choose_spec hμ)

/-- **The cyclotomic character** `G_{K,S} → (ℤ/N)^×` (Mathlib's `modularCyclotomicCharacter` of
`K_S`, which contains `μ_N`). -/
def cycS (hμ : HasRootsOfUnity K S N) : GKS K S →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter (KS K S) (card_rootsOfUnity_KS hμ)).comp (ringAutHom K S)

/-- `σ ζ = ζ^{cycS σ}` for every `N`-th root of unity `ζ ∈ K_S`. Kind: PROVED. -/
theorem cycS_spec (hμ : HasRootsOfUnity K S N) (σ : GKS K S) {ζ : KS K S} (hζ : ζ ^ N = 1) :
    galS K S σ ζ = ζ ^ ((cycS hμ σ : (ZMod N)ˣ) : ZMod N).val := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne N)] at hζ
    exact zero_ne_one hζ
  let t : (KS K S)ˣ := Units.mk0 ζ hζ0
  have ht : t ∈ rootsOfUnity N (KS K S) := by
    rw [mem_rootsOfUnity]
    exact Units.ext (by simpa [t] using hζ)
  exact modularCyclotomicCharacter.spec (KS K S) (card_rootsOfUnity_KS hμ)
    ((galS K S σ).toRingEquiv) ht

/-- **The cyclotomic character has open kernel**: an automorphism fixing a primitive `N`-th root
of unity has trivial cyclotomic character. Kind: PROVED. -/
instance cycS_isOpenKer (hμ : HasRootsOfUnity K S N) : IsOpenKer (cycS hμ) := by
  obtain ⟨ζ, hζ⟩ := id hμ
  refine ⟨Subgroup.isOpen_mono (H₁ := stabS K S ζ) (fun σ hσ => ?_) (isOpen_stabS K S ζ)⟩
  rw [mem_stabS] at hσ
  rw [MonoidHom.mem_ker]
  have h1 := cycS_spec hμ σ hζ.pow_eq_one
  rw [hσ] at h1
  set c := ((cycS hμ σ : (ZMod N)ˣ) : ZMod N).val with hc
  apply Units.ext
  rw [Units.val_one]
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · -- `ζ = 1`, so `N = 1` and `ZMod N` is trivial
    rw [h0, pow_zero] at h1
    have hN1 : N = 1 := by
      have := hζ.eq_orderOf
      rw [h1, orderOf_one] at this
      exact this
    subst hN1
    exact Subsingleton.elim _ _
  · have hdvd : N ∣ c - 1 := by
      rw [← hζ.pow_eq_one_iff_dvd]
      have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
      have : ζ ^ (c - 1) * ζ = ζ := by
        rw [← pow_succ, Nat.sub_add_cancel hpos]
        exact h1.symm
      exact (mul_eq_right₀ hζ0).mp this
    have hval : ((c : ℕ) : ZMod N) = 1 := by
      have := (ZMod.natCast_eq_zero_iff (c - 1) N).mpr hdvd
      rw [Nat.cast_sub hpos, Nat.cast_one, sub_eq_zero] at this
      exact this
    rw [hc, ZMod.natCast_zmod_val] at hval
    exact hval

end Cyc

/-! ### `A ⊗_ℤ ℤ/N ≃ A` and the twist `A(1)` -/

section Tate

variable (A : Type) [CommRing A] (N : ℕ) [NeZero N] [Algebra (ZMod N) A]

/-- `a ⊗ z ↦ a · z`, `A ⊗_ℤ ℤ/N → A` (`A`-linear). -/
def mulZModLin : A →ₗ[A] ZMod N →ₗ[ℤ] A :=
  LinearMap.mk₂' A ℤ (fun a z => a * algebraMap (ZMod N) A z)
    (fun a b z => by rw [add_mul])
    (fun c a z => by rw [smul_eq_mul, smul_eq_mul, mul_assoc])
    (fun a z w => by rw [map_add, mul_add])
    (fun c a z => by rw [map_zsmul, mul_smul_comm])

/-- **`A ⊗_ℤ ℤ/N → A`**, `a ⊗ z ↦ a z`. -/
def mulZMod : A ⊗[ℤ] ZMod N →ₗ[A] A := TensorProduct.AlgebraTensorModule.lift (mulZModLin A N)

theorem mulZMod_tmul (a : A) (z : ZMod N) :
    mulZMod A N (a ⊗ₜ z) = a * algebraMap (ZMod N) A z := rfl

theorem algebraMap_zmod_eq_val (z : ZMod N) : algebraMap (ZMod N) A z = (z.val : A) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact map_natCast _ _

theorem tmul_eq_mulZMod_tmul_one (a : A) (z : ZMod N) :
    (a ⊗ₜ[ℤ] z : A ⊗[ℤ] ZMod N) = (mulZMod A N (a ⊗ₜ z)) ⊗ₜ (1 : ZMod N) := by
  rw [mulZMod_tmul, algebraMap_zmod_eq_val]
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  rw [show ((z.val : ℕ) : ZMod N) = z.val • (1 : ZMod N) by simp, TensorProduct.tmul_smul,
    show z.val • (a ⊗ₜ[ℤ] (1 : ZMod N)) = (z.val • a) ⊗ₜ[ℤ] (1 : ZMod N) from
      (map_nsmul ((TensorProduct.mk ℤ A (ZMod N)).flip 1) _ a).symm, nsmul_eq_mul, mul_comm]

/-- **`A ⊗_ℤ ℤ/N ≃ A`** for a `ℤ/N`-algebra `A`. Kind: PROVED. -/
theorem mulZMod_bijective : Function.Bijective (mulZMod A N) := by
  refine ⟨fun x y hxy => ?_, fun a => ⟨a ⊗ₜ 1, by rw [mulZMod_tmul, map_one, mul_one]⟩⟩
  have key : ∀ x : A ⊗[ℤ] ZMod N, x = (mulZMod A N x) ⊗ₜ (1 : ZMod N) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a z => exact tmul_eq_mulZMod_tmul_one A N a z
    | add x y hx hy => rw [map_add, TensorProduct.add_tmul, ← hx, ← hy]
  rw [key x, key y, hxy]

/-- `A ⊗_ℤ ℤ/N ≃ₗ[A] A`. -/
def mulZModEquiv : (A ⊗[ℤ] ZMod N) ≃ₗ[A] A :=
  LinearEquiv.ofBijective (mulZMod A N) (mulZMod_bijective A N)

variable {N}

/-- **The cyclotomic character with values in `A^×`** (through `ℤ/N → A`). -/
def cycA (hμ : HasRootsOfUnity K S N) : GKS K S →* Aˣ :=
  (Units.map (algebraMap (ZMod N) A).toMonoidHom).comp (cycS hμ)

instance cycA_isOpenKer (hμ : HasRootsOfUnity K S N) : IsOpenKer (cycA A hμ) :=
  isOpenKer_map (cycS hμ) _

/-- **`A(1)`**: the free rank-one `A`-module with `G_{K,S}` acting through the cyclotomic
character (tex 2800, `R_i(1)`). -/
abbrev Tate1 (hμ : HasRootsOfUnity K S N) : Type := CharMod A (cycA A hμ)

/-- **`A(1)` is lane RC26's cyclotomic twist** (`IsCyclotomicTwist`: free of rank one, the Galois
action through the cyclotomic character modulo `N`, and `K_S ⊇ μ_N` with `N` elements), for a
`ℤ/N`-algebra `A`. Kind: PROVED. -/
theorem isCyclotomicTwist_tate1 (hμ : HasRootsOfUnity K S N) :
    IsCyclotomicTwist K S A (Tate1 A hμ) := by
  obtain ⟨ζ, hζ⟩ := id hμ
  refine ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), CharMod.equiv A (cycA A hμ),
    fun σ => ((cycS hμ σ : (ZMod N)ˣ) : ZMod N).val, ?_, ?_, ?_, ?_⟩
  · rw [← map_natCast (algebraMap (ZMod N) A), ZMod.natCast_self, map_zero]
  · -- the `N`-th roots of unity of `K_S` are the `N` elements of `rootsOfUnity N K_S`
    have e : {x : KS K S // x ^ N = 1} ≃ rootsOfUnity N (KS K S) :=
      { toFun := fun x => ⟨Units.mk0 x.1 (by
            rintro h0; have := x.2; rw [h0, zero_pow (NeZero.ne N)] at this
            exact zero_ne_one this), by
            rw [mem_rootsOfUnity]; exact Units.ext (by simpa using x.2)⟩
        invFun := fun u => ⟨((u : (KS K S)ˣ) : KS K S), by
            have := (mem_rootsOfUnity _ _).mp u.2
            rw [← Units.val_pow_eq_pow_val, this, Units.val_one]⟩
        left_inv := fun x => rfl
        right_inv := fun u => by ext; rfl }
    rw [Nat.card_congr e, card_rootsOfUnity_KS hμ]
  · intro σ x hx
    exact cycS_spec hμ σ hx
  · intro σ t
    change ((cycA A hμ σ : Aˣ) : A) * (show A from t) =
      (((cycS hμ σ : (ZMod N)ˣ) : ZMod N).val : A) * (show A from t)
    rw [← algebraMap_zmod_eq_val]
    rfl

end Tate

end ZInQ.Manuscript.RC.CoefModules
