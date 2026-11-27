import ZInQKernel.Contrib.CloudB3E1Torsion.OrthNoInverse
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Ring
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Weil

/-!
# The invariant socle element of the actual stage modules

Manuscript `diophantine_zq.tex`, tex 2724–2727 (`A_i = (ℤ/2^i)[t]/t^i`,
`M_i = (T₂E ⊗ A_i)(α)`), 3736–3753.

`not_orthComparisonInverse` (`OrthNoInverse.lean`) needs a nonzero element of the coefficient
module fixed by a decomposition group. This file constructs one in the actual modules
`M_i = (E[2^i] ⊗ A_i)(α)`, `i ≥ 1`:

* `socleA i = 2^{i−1} t^{i−1} ∈ A_i` (definition). `socleA_ne_zero` (PROVED): it is nonzero.
  `two_mul_socleA`, `t_mul_socleA` (PROVED): `2` and `t` kill it.
* **`unit_mul_socleA`** (PROVED): every unit of `A_i` fixes it. A unit has residue `1 ∈ 𝔽₂`, so
  `u − 1 ∈ (2, t)` (`mem_maxIdealA_of_acoefResidue_eq_zero`), and `(2, t)` kills `socleA`.
* `socleM` (definition), **`socleM_ne_zero`** (PROVED, under `FullTorsion`): `m = socleA ⊗ Q`,
  where `Q` is the first vector of a `ℤ/2^i`-basis of `E(K_S)[2^i] ≅ (ℤ/2^i)²`
  (`torsS_addEquiv_prod`). The pairing `a ⊗ t ↦ a · φ(t)`, for the first coordinate `φ`, sends
  `m` to `socleA ≠ 0`.
* **`ModTwoTrivial`** (named input): `G_{K,S}` acts trivially on `E(K_S)[2^i] / 2E(K_S)[2^i]`.
  For a curve with `E[2] ⊆ E(K)`, such as `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` with 2-torsion points
  `(0,0), (ℓ,0), (−3ℓ,0)`, it is equivalent to the triviality of the action on `E[2]`: `[2^{i−1}]`
  induces `E[2^i]/2E[2^i] ≅ E[2]` (equal cardinalities under `FullTorsion`). The tree's
  `HasFullTwoTorsion` does not give it: it is the cardinality statement `|E(K_S)[2^n]| = 4^n`,
  about points over `K_S`, and says nothing of the Galois action.
* **`socleM_fixed`** (PROVED): under `ModTwoTrivial`, `g • m = m` for every `g ∈ G_{K,S}`:
  `g • (c ⊗ Q) = α(g)c ⊗ gQ = c ⊗ (Q + 2t') = c ⊗ Q + 2c ⊗ t' = c ⊗ Q`.
* **`not_orthComparisonInverse_actual`** (PROVED): lane E2's `OrthComparisonInverse` is
  uninhabited on the actual inflated module `MinS` (over any coefficient ring `k` acting on it)
  for `i ≥ 1`, given `FullTorsion` and `ModTwoTrivial` over `S₀`, as soon as there is an index.

Kinds: definitions, named input (`ModTwoTrivial`), PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open Polynomial NumberField IsDedekindDomain TensorProduct
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef tA tA_pow two_pow_A)
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.SelmerComplex

/-! ### The socle of `A_i` -/

section Socle

variable (i : ℕ)

/-- **`2^{i−1} t^{i−1}`**, spanning the socle of `A_i`. Kind: definition. -/
def socleA : Acoef i := (2 : Acoef i) ^ (i - 1) * tA i ^ (i - 1)

variable {i}

theorem two_mul_socleA (hi : i ≠ 0) : (2 : Acoef i) * socleA i = 0 := by
  rw [socleA, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi),
    two_pow_A, zero_mul]

theorem t_mul_socleA (hi : i ≠ 0) : tA i * socleA i = 0 := by
  rw [socleA, mul_left_comm, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi),
    tA_pow, mul_zero]

/-- `(2, t)` kills `socleA`. Kind: PROVED. -/
theorem maxIdealA_mul_socleA (hi : i ≠ 0) {x : Acoef i} (hx : x ∈ maxIdealA i) :
    x * socleA i = 0 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  rw [add_mul, mul_assoc, mul_assoc, two_mul_socleA hi, t_mul_socleA hi, mul_zero, mul_zero,
    add_zero]

/-- **Every unit of `A_i` fixes `socleA`.** Kind: PROVED. -/
theorem unit_mul_socleA (hi : i ≠ 0) (u : (Acoef i)ˣ) : (u : Acoef i) * socleA i = socleA i := by
  have hres : acoefResidue i hi (u : Acoef i) = 1 := by
    rcases zmod_two_eq_zero_or_one (acoefResidue i hi (u : Acoef i)) with h | h
    · exact absurd (h ▸ (u.isUnit.map (acoefResidue i hi))) not_isUnit_zero
    · exact h
  have hm : (u : Acoef i) - 1 ∈ maxIdealA i :=
    mem_maxIdealA_of_acoefResidue_eq_zero hi (by rw [map_sub, hres, map_one, sub_self])
  have := maxIdealA_mul_socleA hi hm
  rw [sub_mul, one_mul, sub_eq_zero] at this
  exact this

/-- **`socleA ≠ 0`** for `i ≥ 1`. Kind: PROVED. -/
theorem socleA_ne_zero (hi : i ≠ 0) : socleA i ≠ 0 := by
  have he : socleA i = Ideal.Quotient.mk _ (C ((2 : ZMod (2 ^ i)) ^ (i - 1)) * X ^ (i - 1)) := by
    simp only [socleA, tA, map_mul, map_pow]
    rw [show (C (2 : ZMod (2 ^ i)) : (ZMod (2 ^ i))[X]) = 2 from map_ofNat C 2, map_ofNat]
  rw [he, Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, X_pow_dvd_iff]
  intro h
  have h1 := h (i - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hi) one_pos)
  rw [coeff_C_mul_X_pow, ite_eq_left_iff.mpr (fun h => absurd rfl h)] at h1
  have h2 : ((2 ^ (i - 1) : ℕ) : ZMod (2 ^ i)) = 0 := by exact_mod_cast h1
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by positivity) h2
  have h3 : 2 ^ (i - 1) < 2 ^ i := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end Socle

/-! ### The socle element of `M_i` -/

section Module

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (α : GKS K S →* (Acoef i)ˣ)

/-- **The action of `G_{K,S}` is trivial on `E(K_S)[2^i] / 2E(K_S)[2^i]`** (named input; for a
curve with `E[2] ⊆ E(K)`, such as `E_ℓ`, the triviality on `E[2]`; see the module docstring).
Kind: definition (named input). -/
def ModTwoTrivial : Prop :=
  ∀ (g : GKS K S) (t : TorsS K S W ((2 ^ i : ℕ) : ℤ)),
    ∃ t' : TorsS K S W ((2 ^ i : ℕ) : ℤ), g • t = t + 2 • t'

variable {W i}

/-- The first coordinate of `E(K_S)[2^i] ≅ (ℤ/2^i)²`. Kind: definition. -/
def firstCoord (e : TorsS K S W ((2 ^ i : ℕ) : ℤ) ≃+ ZMod (2 ^ i) × ZMod (2 ^ i)) :
    TorsS K S W ((2 ^ i : ℕ) : ℤ) →+ Acoef i :=
  (algebraMap (ZMod (2 ^ i)) (Acoef i)).toAddMonoidHom.comp
    ((AddMonoidHom.fst _ _).comp e.toAddMonoidHom)

/-- The pairing `a ⊗ t ↦ a · φ(t)`. Kind: definition. -/
def socleTest (e : TorsS K S W ((2 ^ i : ℕ) : ℤ) ≃+ ZMod (2 ^ i) × ZMod (2 ^ i)) :
    Acoef i ⊗[ℤ] TorsS K S W ((2 ^ i : ℕ) : ℤ) →+ Acoef i :=
  TensorProduct.liftAddHom ((AddMonoidHom.mul : Acoef i →+ Acoef i →+ Acoef i).compl₂
    (firstCoord e)) fun r a t => by
      simp only [map_zsmul, AddMonoidHom.smul_apply, AddMonoidHom.compl₂_apply,
        AddMonoidHom.mul_apply]

/-- **The socle element** `m = socleA ⊗ Q` of `M_i`, `Q = e⁻¹(1, 0)`. Kind: definition. -/
def socleM (e : TorsS K S W ((2 ^ i : ℕ) : ℤ) ≃+ ZMod (2 ^ i) × ZMod (2 ^ i)) :
    CoefMod (Acoef i) α (TorsS K S W ((2 ^ i : ℕ) : ℤ)) :=
  CoefMod.equiv (Acoef i) α _ (socleA i ⊗ₜ e.symm (1, 0))

omit [NumberField K] [W.IsElliptic] in
/-- **`m ≠ 0`.** Kind: PROVED. -/
theorem socleM_ne_zero (e : TorsS K S W ((2 ^ i : ℕ) : ℤ) ≃+ ZMod (2 ^ i) × ZMod (2 ^ i)) :
    socleM α e ≠ 0 := by
  intro h
  have h1 : socleTest e ((CoefMod.equiv (Acoef i) α _).symm (socleM α e)) = 0 := by
    rw [h, map_zero, map_zero]
  rw [socleM, LinearEquiv.symm_apply_apply, socleTest, TensorProduct.liftAddHom_tmul] at h1
  change socleA i * firstCoord e (e.symm (1, 0)) = 0 at h1
  rw [firstCoord] at h1
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.apply_symm_apply, AddMonoidHom.coe_fst, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass, map_one, mul_one] at h1
  exact socleA_ne_zero (NeZero.ne i) h1

omit [NumberField K] [W.IsElliptic] in
/-- **`m` is fixed by `G_{K,S}`** under `ModTwoTrivial`. Kind: PROVED. -/
theorem socleM_fixed (hmod : ModTwoTrivial (S := S) W i)
    (e : TorsS K S W ((2 ^ i : ℕ) : ℤ) ≃+ ZMod (2 ^ i) × ZMod (2 ^ i)) (g : GKS K S) :
    g • socleM α e = socleM α e := by
  obtain ⟨t', ht'⟩ := hmod g (e.symm (1, 0))
  rw [socleM, CoefMod.smul_tmul, unit_mul_socleA (NeZero.ne i), ht', TensorProduct.tmul_add,
    ← TensorProduct.smul_tmul, two_smul, ← two_mul, two_mul_socleA (NeZero.ne i),
    TensorProduct.zero_tmul, add_zero]

end Module

/-! ### The orthogonal comparison at the actual modules -/

section Actual

open ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3E2.DualPres
open ZInQ.Manuscript.RC.Limits (SplitInclusion)

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
  {k : Type} [CommRing k] [TopologicalSpace k] [Module k (MinS hS W i α)]
  [SMulCommClass (GKS K S) k (MinS hS W i α)]
  {Δ' Δ'' : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (MinS hS W i α)}
  {ι : Type} [DecidableEq ι] {place : ι × Bool → Places K S}
  {X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1)}
  {EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j))
    (genuineLq K S k (MinS hS W i α) (place j))}

/-- **Lane E2's `OrthComparisonInverse` is uninhabited at the actual modules** (PROVED; tex
3736–3753): for `i ≥ 1`, `FullTorsion` and `ModTwoTrivial` over `S₀`, and any index `p`, there is
no `OrthComparisonInverse` on `MinS hS W i α`, over any coefficient ring `k` acting on it and for
any `φo`. Kind: PROVED. -/
theorem not_orthComparisonInverse_actual (hFull : FullTorsion K S₀ W (2 ^ i))
    (hmod : ModTwoTrivial (S := S₀) W i) (p : ι) :
    ¬ Nonempty (OrthComparisonInverse K S₀ S k (MinS hS W i α) Δ' Δ'' place X EU) := by
  obtain ⟨e⟩ := torsS_addEquiv_prod W hFull
  refine not_orthComparisonInverse p
    (show MinS hS W i α from socleM α e) (socleM_ne_zero α e) fun g => ?_
  exact socleM_fixed α hmod e _

end Actual

end ZInQ.Contrib.CloudB3E1Torsion
