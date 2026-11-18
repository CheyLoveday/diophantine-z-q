import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Triangular
import ZInQKernel.Contrib.OneProof.RC.Wiring.Central
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Coefficients

/-!
# Calibration (4.6): the support-triangle bookkeeping and the two-torsion exponent `t_p`

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex L3987–4141), consumed by
RC0's `CalibrationModel` (`RC/Wiring/Central.lean`), whose field

```
hvprim : v2 (central (D.uPrim Fam x)) = (primValuation j vL vm gA sA vN ω : WithTop ℤ)
```

is listed as "ELLIOT: determinant multiplicativity in the support triangles (RC15, with the Duality
and RankCounts areas)". This file proves:

* `central_support_triangle` (tex L4058–4078): if the support triangle gives
  `det(D_W) · u_big = e² · u_small` in `ℚ₂[[t]]` (`CommonCoordinate.triangular_coord`), then the
  central valuations satisfy `v₂ det_W(0) + v₂ u_big(0) = 2 v₂ e(0) + v₂ u_small(0)`;
* `hvprim_of_support_triangle`: RC0's field `hvprim` in its exact type, from the ordinary Kummer
  coordinate's valuation `2(j + v₂L + v₂m) + (2g_A − s_A)` (the class, functional and torsion-disk
  contributions, tex L4051–4064; input), the support triangle from the Kummer complex to the
  primitive complex at the moving and active places (no point factor, `e = 1`), and the total
  length `2 v₂N + 4ω` of the full/Kummer quotients (tex L4066–4078; input);
* `hvprim_of_triangular_model`: the same with the support triangle given as a triangular model
  (`triangular_coord`);
* `card_twoTorsion_eq_two_pow` (genuine objects): for an elliptic curve over a field of
  characteristic `≠ 2`, `#E(K)[2] = 2^t` with `t ≤ 2` — the exponent `t_p = dim_{𝔽₂} E[2]^{Fr_p}`
  of tex L4029–4033, L4118–4138 (RC0's fields `hB`, `htp` with `tp p` this exponent, once the
  component number is identified with `#Ẽ(𝔽_p)[2]`, Edixhoven Thm 5.3 and Rem 5.4.1: GLUE, the
  component groups of Néron models are not in the library).

**Classification.** PROVED (the inputs are named in each statement).
-/

namespace ZInQ.Contrib.CloudB3RC53.Calibration

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate

/-! ### Central valuations through a support triangle -/

theorem central_mul (f g : PowerSeries ℚ_[2]) : central (f * g) = central f * central g := by
  simp only [central, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]

theorem v2_mul (x y : ℚ_[2]) : v2 (x * y) = v2 x + v2 y :=
  Padic.addValuation.map_mul x y

/-- **Central valuations through a support triangle** (tex L4058–4078): from
`det(D_W) · u_big = e² · u_small` in `ℚ₂[[t]]`,
`v₂ det_W(0) + v₂ u_big(0) = 2 v₂ e(0) + v₂ u_small(0)`. -/
theorem central_support_triangle {δ e ubig usmall : PowerSeries ℚ_[2]}
    (h : δ * ubig = e ^ 2 * usmall) :
    v2 (central δ) + v2 (central ubig) = 2 • v2 (central e) + v2 (central usmall) := by
  have := congrArg (fun f => v2 (central f)) h
  simp only [central_mul, v2_mul, sq] at this
  rw [this, two_nsmul]

/-- **RC0's field `hvprim` from the support triangle** (tex L4051–4078). Inputs: the ordinary
Kummer coordinate `uK` has central valuation `2(j + v₂L + v₂m) + (g_A − s_A + g_A)` (the class and
functional free coefficients and the torsion disks in degrees one, two, three; ELLIOT, tex
L4051–4064); the support triangle from the Kummer complex to the primitive complex gives
`det(D_W) · u_prim = uK` (the class and functional are unchanged; `CommonCoordinate.triangular_coord`
with `e = 1`); and the full/Kummer quotients have total central length `2 v₂N + 4ω`
(`v₂ det_W(0)`; ELLIOT/GLUE, tex L4066–4078). Then `v₂ u_prim(0) = primValuation …`. -/
theorem hvprim_of_support_triangle {uprim uK δ : PowerSeries ℚ_[2]} (j vL vm gA sA vN ω : ℤ)
    (hK : v2 (central uK) = (((j + vL + vm) + (j + vL + vm) +
      (Central.diskContribution 1 gA + Central.diskContribution 2 sA +
        Central.diskContribution 3 gA) : ℤ) : WithTop ℤ))
    (htri : δ * uprim = uK) (hδ : v2 (central δ) = ((2 * vN + 4 * ω : ℤ) : WithTop ℤ)) :
    v2 (central uprim) = ((primValuation j vL vm gA sA vN ω : ℤ) : WithTop ℤ) := by
  have h := central_support_triangle (δ := δ) (e := 1) (ubig := uprim) (usmall := uK)
    (by rw [one_pow, one_mul]; exact htri)
  rw [hδ, hK] at h
  have h1 : v2 (central (1 : PowerSeries ℚ_[2])) = 0 := by
    simp [central, v2]
  rw [h1, smul_zero, zero_add] at h
  -- cancel the finite valuation `2 v₂N + 4ω`
  have hne : v2 (central uprim) ≠ ⊤ := by
    intro htop
    rw [htop, WithTop.add_top] at h
    exact WithTop.top_ne_coe h
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hn] at h ⊢
  have h' := WithTop.coe_inj.mp ((WithTop.coe_add _ _).symm.trans h)
  congr 1
  unfold primValuation
  rw [Central.local_contribution]
  linarith

/-- **`hvprim` from a triangular model of the support triangle** (tex L4058–4078): the primitive
complex is the relaxation of the Kummer complex at the moving and active places,
`D_prim = [[D_K, X], [0, D_W]]` over `ℚ₂[[t]]`, with the class and functional restricting to the
Kummer ones (`e = 1`). With the Kummer coordinate's valuation and the quotient length as in
`hvprim_of_support_triangle`, RC0's `hvprim` holds. -/
theorem hvprim_of_triangular_model {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])) (X : Matrix (Fin n) κ (PowerSeries ℚ_[2]))
    (DW : Matrix κ κ (PowerSeries ℚ_[2])) (zK wK : Fin n → PowerSeries ℚ_[2])
    (zP wP : Fin n ⊕ κ → PowerSeries ℚ_[2]) (uK uprim : PowerSeries ℚ_[2])
    (hz : ∀ i, zP (Sum.inl i) = zK i) (hw : ∀ i, wP (Sum.inl i) = wK i)
    (hP : IsCoordOn (fromBlocks DK X 0 DW) zP wP uprim)
    (hKc : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord DK zK wK uK)
    (hadj : DK.adjugate ≠ 0) (j vL vm gA sA vN ω : ℤ)
    (hK : v2 (central uK) = (((j + vL + vm) + (j + vL + vm) +
      (Central.diskContribution 1 gA + Central.diskContribution 2 sA +
        Central.diskContribution 3 gA) : ℤ) : WithTop ℤ))
    (hδ : v2 (central DW.det) = ((2 * vN + 4 * ω : ℤ) : WithTop ℤ)) :
    v2 (central uprim) = ((primValuation j vL vm gA sA vN ω : ℤ) : WithTop ℤ) := by
  have htri := triangular_coord DK X DW zK wK zP wP 1 uK uprim (fun i => by rw [hz, one_mul])
    (fun i => by rw [hw, one_mul]) hP hKc hadj
  rw [one_pow, one_mul] at htri
  exact hvprim_of_support_triangle j vL vm gA sA vN ω hK htri hδ

/-! ### The two-torsion exponent `t_p` -/

/-- **`#E(K)[2] = 2^t` with `t ≤ 2`** for an elliptic curve over a field in which `2` is
invertible (genuine objects): `E(K)[2]` embeds in `E(Kˢ)[2]`, which has four elements. This is the
exponent `t_p = dim_{𝔽₂} E[2]^{Fr_p}` of tex L4029–4033, L4118–4138 at a residue field `𝔽_p`. -/
theorem card_twoTorsion_eq_two_pow {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
    [W.IsElliptic] (h2 : IsUnit (2 : K)) :
    ∃ t : ℕ, t ≤ 2 ∧ Nat.card (AddSubgroup.torsionBy W.toAffine.Point (2 : ℕ)) = 2 ^ t := by
  have h2' : IsUnit ((2 : ℕ) : K) := by exact_mod_cast h2
  have hcard : Nat.card (W.TorsionCoeff 2) = 2 ^ 2 := W.natCard_torsionCoeff h2'
  have : NeZero (2 : ℕ) := ⟨two_ne_zero⟩
  have hfin : Finite (W.TorsionCoeff 2) := W.finite_torsionCoeff 2
  have hdvd : Nat.card (AddSubgroup.torsionBy W.toAffine.Point (2 : ℕ)) ∣ 2 ^ 2 := by
    rw [← hcard, ← Nat.card_range_of_injective (W.baseTorsionCoeff_injective 2)]
    exact AddSubgroup.card_addSubgroup_dvd_card (W.baseTorsionCoeff 2).range
  obtain ⟨t, ht, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨t, ht, heq⟩

/-- **RC0's fields `hB` and `htp` from the reductions** (tex L4118–4138). For each companion prime
`p ∈ T` let `W p` be an elliptic curve over a field `k p` in which `2` is invertible (the good
reduction `Ẽ₀` over `𝔽_p`, `p` odd), and assume the component number of the ramified twist is
`#Ẽ₀(𝔽_p)[2]` (GLUE, the content of Edixhoven, *Néron models and tame ramification*, Thm 5.3 and
Rem 5.4.1, pp. 299–300, as cited: component groups of Néron models are not in the library). Then
there is `t : ℕ → ℕ` with `c_p(ℬ) = 2^{t_p}` and `t_p ≤ 2` at every `p ∈ T`. -/
theorem componentFields_of_reductions (T : Finset ℕ) (k : ℕ → Type) [∀ p, Field (k p)]
    [∀ p, DecidableEq (k p)] (W : ∀ p, WeierstrassCurve (k p)) [∀ p, (W p).IsElliptic]
    (h2 : ∀ p ∈ T, IsUnit (2 : k p)) (cB : ℕ → ℕ)
    (hEdix : ∀ p ∈ T, cB p = Nat.card (AddSubgroup.torsionBy (W p).toAffine.Point (2 : ℕ))) :
    ∃ tp : ℕ → ℕ, (∀ p ∈ T, cB p = 2 ^ tp p) ∧ (∀ p ∈ T, tp p ≤ 2) := by
  classical
  have key : ∀ p, ∃ t : ℕ, p ∈ T → (t ≤ 2 ∧ cB p = 2 ^ t) := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨t, ht, heq⟩ := card_twoTorsion_eq_two_pow (W p) (h2 p hp)
      exact ⟨t, fun _ => ⟨ht, (hEdix p hp).trans heq⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose tp htp using key
  exact ⟨tp, fun p hp => (htp p hp).2, fun p hp => (htp p hp).1⟩

end ZInQ.Contrib.CloudB3RC53.Calibration
