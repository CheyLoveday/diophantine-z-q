import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.DualityData
import ZInQKernel.Contrib.CloudB3RC53.Duality.LocalKummer

/-!
# Duality area: the derived Kummer step (tex L3443–3450) for the truncated target

Lemma `ex:arith-local-kummer`, tex L3443–3450: "The restricted cup map
`M[−1] ⊗^L M[−1] → ℤ₂[−2]` has homotopy class determined by `Hom(M ⊗ M, ℤ₂)`. Finite isotropy makes
every value divisible by every power of two, hence zero. A projective resolution therefore supplies
a null-homotopy. The possible ambiguity group in degree minus one vanishes."

Nekovář's construction (6.2–6.3) needs the null-homotopy only after the canonical truncation
`τ≥2` of the local target (`SwitchInputs/TruncIsotropy.lean`). This file proves the step at chain
level for that target. Let `U, U'` be models of the conditions concentrated in degrees `0, 1`
(a free resolution `[P₁ → P₀]` of `M`, or any two-term model), `T` a target vanishing in degrees
`≤ 1` (as `τ≥2 E_L` does), and `P : U × U' → T` a pairing of complexes (`GPair`):

* `pair_eq_zero_of_11`: `P` is determined by its bidegree `(1, 1)` component `U¹ × U'¹ → T²`;
* `pair11_boundary_left/right`, `pair11_descends`: that component vanishes on boundaries, so it is a
  bilinear form on `H¹(U) × H¹(U')` ("homotopy class determined by `Hom(M ⊗ M, ℤ₂)`"), with values
  in the degree-two cocycles of `T` (`pair11_cocycle`);
* `nullHomotopy_eq_zero`: every family of degree `−1` (a would-be null-homotopy) is zero (the
  ambiguity group vanishes), so a null-homotopy exists iff `P = 0`, and is then unique;
* **`derivedKummerStep_trunc` (PROVED)**: over `ℤ₂`, if a map `e : T² → ℤ₂` is injective on the
  degree-two cocycles (`inv` on `H²(τ≥2 E_L) ≅ ℤ₂`) and every value `e (P u v)` is divisible by
  every power of two (finite isotropy), then `P = 0`: the restricted pairing into the truncated
  target vanishes identically and the zero family is its unique null-homotopy.

So for the `τ≥2` target the class is exactly `Hom(H¹(U) ⊗ H¹(U'), H²(T))`; the summands
`Hom(Tor₁(M,M), H¹)` and `Ext¹(M ⊗ M, H¹)` of the untruncated target do not occur, and no
`Ext¹(Tor₁(M,M), ℤ₂)` term arises (it would need a map `Tor₁[−1] → ℤ₂[−2]`, i.e. `Ext⁻¹ = 0`). For
the untruncated target they do occur: `DerivedKummerWitness.lean`.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Duality

open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology (VanishesOutside)

universe u

variable {S : Type u} [CommRing S] {U U' T : GCx S}

/-- The degree bounds: conditions in degrees `0, 1`, target in degrees `≥ 2`. -/
structure TruncBounds (U U' T : GCx S) : Prop where
  hU : VanishesOutside U (fun i => i = 0 ∨ i = 1)
  hU' : VanishesOutside U' (fun i => i = 0 ∨ i = 1)
  hT : VanishesOutside T (fun k => 2 ≤ k)

/-- **The pairing is determined by its bidegree `(1, 1)` component.** -/
theorem pair_eq_zero_of_11 (hb : TruncBounds U U' T) (P : GPair U U' T)
    (h11 : ∀ (u : U.X 1) (v : U'.X 1), P.P 1 1 2 rfl u v = 0) (i j k : ℤ) (h : i + j = k)
    (u : U.X i) (v : U'.X j) : P.P i j k h u v = 0 := by
  by_cases hi : i = 0 ∨ i = 1
  · by_cases hj : j = 0 ∨ j = 1
    · by_cases hk : 2 ≤ k
      · obtain rfl : i = 1 := by omega
        obtain rfl : j = 1 := by omega
        obtain rfl : k = 2 := by omega
        exact h11 u v
      · have := hb.hT k hk
        exact Subsingleton.elim _ _
    · have := hb.hU' j hj
      rw [Subsingleton.elim v 0, map_zero]
  · have := hb.hU i hi
    rw [Subsingleton.elim u 0, map_zero, LinearMap.zero_apply]

/-- The `(1, 1)` component vanishes on boundaries in the first variable. -/
theorem pair11_boundary_left (hb : TruncBounds U U' T) (P : GPair U U' T) (u0 : U.X 0)
    (v : U'.X 1) : P.P 1 1 2 rfl (U.d 0 1 rfl u0) v = 0 := by
  have e := P.leib 0 1 1 2 1 2 rfl rfl rfl rfl u0 v
  have h1 : Subsingleton (T.X 1) := hb.hT 1 (by norm_num)
  have h2 : Subsingleton (U'.X 2) := hb.hU' 2 (by norm_num)
  rw [Subsingleton.elim (P.P 0 1 1 rfl u0 v) 0, map_zero,
    Subsingleton.elim (U'.d 1 2 rfl v) 0, map_zero, smul_zero, add_zero] at e
  exact e.symm

/-- The `(1, 1)` component vanishes on boundaries in the second variable. -/
theorem pair11_boundary_right (hb : TruncBounds U U' T) (P : GPair U U' T) (u : U.X 1)
    (v0 : U'.X 0) : P.P 1 1 2 rfl u (U'.d 0 1 rfl v0) = 0 := by
  have e := P.leib 1 2 0 1 1 2 rfl rfl rfl rfl u v0
  have h1 : Subsingleton (T.X 1) := hb.hT 1 (by norm_num)
  have h2 : Subsingleton (U.X 2) := hb.hU 2 (by norm_num)
  rw [Subsingleton.elim (P.P 1 0 1 rfl u v0) 0, map_zero,
    Subsingleton.elim (U.d 1 2 rfl u) 0, map_zero, LinearMap.zero_apply, zero_add] at e
  have hs : (sgn 1 : ℤ) • P.P 1 1 2 rfl u (U'.d 0 1 rfl v0) = 0 := e.symm
  rw [sgn_one, neg_one_smul, neg_eq_zero] at hs
  exact hs

/-- **The `(1, 1)` component is a bilinear form on `H¹(U) × H¹(U')`** ("homotopy class determined by
`Hom(M ⊗ M, ℤ₂)`"). -/
theorem pair11_descends (hb : TruncBounds U U' T) (P : GPair U U' T) (u u' : U.X 1)
    (v v' : U'.X 1) (hu : ∃ a, U.d 0 1 rfl a = u - u') (hv : ∃ c, U'.d 0 1 rfl c = v - v') :
    P.P 1 1 2 rfl u v = P.P 1 1 2 rfl u' v' := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨c, hc⟩ := hv
  have e1 : P.P 1 1 2 rfl u v - P.P 1 1 2 rfl u' v = 0 := by
    rw [← LinearMap.sub_apply, ← map_sub, ← ha]; exact pair11_boundary_left hb P a v
  have e2 : P.P 1 1 2 rfl u' v - P.P 1 1 2 rfl u' v' = 0 := by
    rw [← map_sub, ← hc]; exact pair11_boundary_right hb P u' c
  exact sub_eq_zero.mp (by rw [← sub_add_sub_cancel _ (P.P 1 1 2 rfl u' v), e1, e2, add_zero])

/-- The values of the `(1, 1)` component are degree-two cocycles. -/
theorem pair11_cocycle (hb : TruncBounds U U' T) (P : GPair U U' T) (u : U.X 1) (v : U'.X 1) :
    T.d 2 3 rfl (P.P 1 1 2 rfl u v) = 0 := by
  have e := P.leib 1 2 1 2 2 3 rfl rfl rfl rfl u v
  have h2 : Subsingleton (U.X 2) := hb.hU 2 (by norm_num)
  have h2' : Subsingleton (U'.X 2) := hb.hU' 2 (by norm_num)
  rw [e, Subsingleton.elim (U.d 1 2 rfl u) 0, Subsingleton.elim (U'.d 1 2 rfl v) 0, map_zero,
    map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/-- **The ambiguity group vanishes**: every family of degree `−1` from `U × U'` to `T` is zero. -/
theorem nullHomotopy_eq_zero (hb : TruncBounds U U' T)
    (f : ∀ i j k : ℤ, i + j = k + 1 → U.X i →ₗ[S] U'.X j →ₗ[S] T.X k) (i j k : ℤ)
    (h : i + j = k + 1) (u : U.X i) (v : U'.X j) : f i j k h u v = 0 := by
  by_cases hi : i = 0 ∨ i = 1
  · by_cases hj : j = 0 ∨ j = 1
    · have := hb.hT k (by omega)
      exact Subsingleton.elim _ _
    · have := hb.hU' j hj
      rw [Subsingleton.elim v 0, map_zero]
  · have := hb.hU i hi
    rw [Subsingleton.elim u 0, map_zero, LinearMap.zero_apply]

/-- An element of `ℤ₂` divisible by every power of two is zero. -/
theorem eq_zero_of_forall_two_pow_dvd (z : ℤ_[2]) (h : ∀ a : ℕ, (2 : ℤ_[2]) ^ a ∣ z) : z = 0 := by
  by_contra hne
  have hd := h (z.valuation + 1)
  rw [← Ideal.mem_span_singleton] at hd
  have hd' : z ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ (z.valuation + 1)} := by exact_mod_cast hd
  rw [PadicInt.mem_span_pow_iff_le_valuation _ hne] at hd'
  omega

/-- **The derived Kummer step for the truncated target** (tex L3443–3450; PROVED): if `e : T² → ℤ₂`
is injective on degree-two cocycles and every value `e (P u v)` is divisible by every power of two
(finite isotropy), the restricted pairing vanishes identically, and every family of degree `−1`
vanishes (so the zero family is the unique null-homotopy). -/
theorem derivedKummerStep_trunc {U U' T : GCx ℤ_[2]} (hb : TruncBounds U U' T)
    (P : GPair U U' T) (e : T.X 2 →ₗ[ℤ_[2]] ℤ_[2])
    (he : ∀ t : T.X 2, T.d 2 3 rfl t = 0 → e t = 0 → t = 0)
    (hiso : ∀ (a : ℕ) (u : U.X 1) (v : U'.X 1), (2 : ℤ_[2]) ^ a ∣ e (P.P 1 1 2 rfl u v)) :
    (∀ (i j k : ℤ) (h : i + j = k) (u : U.X i) (v : U'.X j), P.P i j k h u v = 0) ∧
      ∀ (f : ∀ i j k : ℤ, i + j = k + 1 → U.X i →ₗ[ℤ_[2]] U'.X j →ₗ[ℤ_[2]] T.X k) (i j k : ℤ)
        (h : i + j = k + 1) (u : U.X i) (v : U'.X j), f i j k h u v = 0 := by
  refine ⟨pair_eq_zero_of_11 hb P fun u v => ?_, nullHomotopy_eq_zero hb⟩
  exact he _ (pair11_cocycle hb P u v) (eq_zero_of_forall_two_pow_dvd _ fun a => hiso a u v)

end ZInQ.Contrib.CloudB3RC53.Duality
