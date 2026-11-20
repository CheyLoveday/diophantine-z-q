import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Coefficients
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SelfInjective
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints

/-!
# Lane RC28 (coefficient modules), part 1: the coefficient rings `A_i` in Nekovář's finite setting

Manuscript `diophantine_zq.tex` (11/5), §8 setup, tex 2720–2727:

> The actual finite coefficients are `A_i = (ℤ/2^iℤ)[t]/t^i`, `M_i = (T_2E ⊗ A_i)(χ_hΨ_i)`.

and the finite standing hypotheses of Nekovář's duality theorems, cited at tex 3454–3456 and
3829–3835 (Nekovář, *Selmer complexes*, Astérisque 310 (2006), 5.1, p. 113; 5.2.3 and 6.2.5 (A)
with `J = I[0] = R`): a finite local ring with nilpotent `p`, self-injective.

The ring is lane RC10's `Acoef i` (`ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef`); its
self-injectivity is the other group's `acoef_selfInjective`. This file adds what the finite
setting still needs, all PROVED:

* `acoefResidue i : A_i →+* 𝔽₂` (the residue map, `t ↦ 0`, reduction modulo `2`), and
  `isNilpotent_of_acoefResidue_eq_zero`: its kernel is nilpotent (it lies in `(2, t)`, whose
  `2i`-th power is zero);
* `acoef_isLocalRing` (instance for `i ≠ 0`): `A_i` is local with residue field `𝔽₂`;
* `acoef_finite` (instance), `acoef_isNilpotent_two`, `acoef_two_pow_eq_zero`;
* `nekovarFiniteSetting_acoef`: lane RC26's `NekovarFiniteSetting K S 2 A_i` for a totally
  complex `K` (condition (P) at `p = 2`; the text's `K` is imaginary quadratic, tex 2720) and a
  finite `S` containing the primes above `2`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.CoefModules

open Polynomial ZInQ.Manuscript.RC.HeegnerAlgebra NumberField IsDedekindDomain

/-- `A_i` is finite: it is free of rank `i` over `ℤ/2^i` (power basis `1, t, …, t^{i−1}`).
Kind: PROVED. -/
instance acoef_finite (i : ℕ) : Finite (Acoef i) := by
  have : Module.Finite (ZMod (2 ^ i)) (Acoef i) :=
    (AdjoinRoot.powerBasis' (monic_X_pow (R := ZMod (2 ^ i)) i)).finite
  exact Module.finite_of_finite (ZMod (2 ^ i))

/-- `2^i = 0` in `A_i` (lane RC10's `two_pow_A`). Kind: PROVED. -/
theorem acoef_two_pow_eq_zero (i : ℕ) : (2 : Acoef i) ^ i = 0 := two_pow_A i

/-- `2` is nilpotent in `A_i`. Kind: PROVED. -/
theorem acoef_isNilpotent_two (i : ℕ) : IsNilpotent (2 : Acoef i) := ⟨i, two_pow_A i⟩

/-- The ideal `(2, t)` of `A_i`. -/
def maxIdealA (i : ℕ) : Ideal (Acoef i) := Ideal.span {(2 : Acoef i)} ⊔ Ideal.span {tA i}

/-- `(2, t)^{2i} = 0` in `A_i` (as in lane RC10's proof of `(1 + t)^{2^{2i}} = 1`).
Kind: PROVED. -/
theorem maxIdealA_pow (i : ℕ) : maxIdealA i ^ (i + i) = ⊥ := by
  have h := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(2 : Acoef i)})
    (J := Ideal.span {tA i}) (n := i) (m := i)
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, two_pow_A, tA_pow,
    Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at h
  exact le_bot_iff.mp h

/-- Every element of `(2, t)` is nilpotent. Kind: PROVED. -/
theorem isNilpotent_of_mem_maxIdealA {i : ℕ} {x : Acoef i} (hx : x ∈ maxIdealA i) :
    IsNilpotent x := by
  refine ⟨i + i, ?_⟩
  have : x ^ (i + i) ∈ maxIdealA i ^ (i + i) := Ideal.pow_mem_pow hx _
  rwa [maxIdealA_pow, Ideal.mem_bot] at this

/-- The ring map `(ℤ/2^i)[X] → 𝔽₂`, `p ↦ p(0) mod 2`. -/
def residuePoly (i : ℕ) (hi : i ≠ 0) : (ZMod (2 ^ i))[X] →+* ZMod 2 :=
  (ZMod.castHom (dvd_pow_self 2 hi) (ZMod 2)).comp (Polynomial.evalRingHom 0)

theorem residuePoly_X_pow (i : ℕ) (hi : i ≠ 0) : residuePoly i hi (X ^ i) = 0 := by
  simp [residuePoly, hi]

/-- **The residue map** `A_i → 𝔽₂` (`t ↦ 0`, reduction modulo `2`). -/
def acoefResidue (i : ℕ) (hi : i ≠ 0) : Acoef i →+* ZMod 2 :=
  Ideal.Quotient.lift _ (residuePoly i hi) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, residuePoly_X_pow, mul_zero]

theorem acoefResidue_mk (i : ℕ) (hi : i ≠ 0) (p : (ZMod (2 ^ i))[X]) :
    acoefResidue i hi (Ideal.Quotient.mk _ p) = ((p.coeff 0 : ZMod (2 ^ i)).cast : ZMod 2) := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [acoefResidue, residuePoly]

/-- **The kernel of the residue map is `(2, t)`, hence nilpotent.** Kind: PROVED. -/
theorem mem_maxIdealA_of_acoefResidue_eq_zero {i : ℕ} (hi : i ≠ 0) {x : Acoef i}
    (hx : acoefResidue i hi x = 0) : x ∈ maxIdealA i := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [acoefResidue_mk] at hx
  set a : ZMod (2 ^ i) := p.coeff 0 with ha
  have h2 : 2 ∣ a.val := by
    have : ((a.val : ℕ) : ZMod 2) = 0 := by
      rw [← hx, ZMod.cast_eq_val]
    exact (ZMod.natCast_eq_zero_iff _ _).mp this
  obtain ⟨b, hb⟩ := h2
  have hp : p = X * p.divX + C a := (X_mul_divX_add p).symm
  rw [hp, map_add, map_mul]
  refine Ideal.add_mem _ (Submodule.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
    (Submodule.mem_sup_left ?_)
  have hCa : (C a : (ZMod (2 ^ i))[X]) = C 2 * C (b : ZMod (2 ^ i)) := by
    rw [← C_mul]
    congr 1
    rw [← ZMod.natCast_zmod_val a, hb]
    push_cast
    ring
  rw [hCa, map_mul]
  refine Ideal.mul_mem_right _ _ (Ideal.subset_span ?_)
  simp only [Set.mem_singleton_iff, map_ofNat]

/-- The kernel of the residue map consists of nilpotent elements. Kind: PROVED. -/
theorem isNilpotent_of_acoefResidue_eq_zero {i : ℕ} (hi : i ≠ 0) {x : Acoef i}
    (hx : acoefResidue i hi x = 0) : IsNilpotent x :=
  isNilpotent_of_mem_maxIdealA (mem_maxIdealA_of_acoefResidue_eq_zero hi hx)

theorem zmod_two_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `A_i` is nontrivial for `i ≠ 0` (its residue map sends `1` to `1 ≠ 0`). Kind: PROVED. -/
theorem acoef_nontrivial {i : ℕ} (hi : i ≠ 0) : Nontrivial (Acoef i) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (acoefResidue i hi) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

/-- **`A_i` is a local ring** (`i ≠ 0`), with maximal ideal `(2, t)` and residue field `𝔽₂`.
Kind: PROVED. -/
theorem acoef_isLocalRing {i : ℕ} (hi : i ≠ 0) : IsLocalRing (Acoef i) := by
  have := acoef_nontrivial hi
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases zmod_two_eq_zero_or_one (acoefResidue i hi x) with h | h
  · exact Or.inr (isNilpotent_of_acoefResidue_eq_zero hi h).isUnit_one_sub
  · left
    have h' : acoefResidue i hi (x - 1) = 0 := by rw [map_sub, h, map_one, sub_self]
    have := (isNilpotent_of_acoefResidue_eq_zero hi h').isUnit_one_add
    rwa [add_sub_cancel] at this

instance acoef_isLocalRing_inst (i : ℕ) [NeZero i] : IsLocalRing (Acoef i) :=
  acoef_isLocalRing (NeZero.ne i)

/-- **Nekovář's finite standing hypotheses for the coefficient ring `A_i`** (Nekovář 5.1, p. 113;
5.2.3 and 6.2.5 (A) with `J = I[0] = R`), in lane RC26's form: for a totally complex number field
`K` (the text's imaginary quadratic `K`, tex 2720; condition (P) at `p = 2`) and a finite set `S`
of primes containing those above `2`, `A_i` is a finite local ring with nilpotent `2`, injective
over itself. Kind: PROVED. -/
theorem nekovarFiniteSetting_acoef (K : Type) [Field K] [NumberField K] (hK : IsTotallyComplex K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) (i : ℕ) [NeZero i] :
    ZInQ.Manuscript.RC.SelmerComplex.NekovarFiniteSetting K S 2 (Acoef i) where
  prime := Nat.prime_two
  finite_S := hS
  above_p v hv := h2 v (by exact_mod_cast hv)
  condP _ := hK
  finite_R := inferInstance
  nilpotent_p := by exact_mod_cast acoef_isNilpotent_two i
  selfInjective := ZInQ.Contrib.CloudB3RC53.SelmerDuality.acoef_selfInjective i

end ZInQ.Manuscript.RC.CoefModules
