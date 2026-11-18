import ZInQKernel.Contrib.OneProof.RC.Rings.OValuation
import ZInQKernel.Contrib.OneProof.RC.Rings.LambdaHalfCoeff

/-!
# Lane RC20: wiring the genuine rings into lanes RC16 and RC7

Manuscript (`diophantine_zq.tex`, 11/5 version): tex 4914–4920 (`v₂ u_prim ≥ −C`, `u_prim ∈ Λ[1/2]`, the
valuation of `𝒪`), tex 5486–5507 and 5605–5629 (Proposition `ex:limits-fixed-field-clearing`, (5.9)),
tex 5491–5496 ("`ũ_x ∈ Λ[1/2]`"), tex 5698–5705.

* `iotaO_lambdaHalfToFrac` : the two embeddings of `Λ[1/2]` in `Frac 𝒪` agree (`ι ∘ (Λ[1/2] ⊂ Frac Λ)` and
  `halfToFracO`);
* `neg_le_vO_iff` : (5.5) in valuation form on the genuine `Λ[1/2]`: `v_𝒪(u) ≥ −C ↔ 2^C u ∈ Λ`
  (both directions; RC16's `integral_form_of_valuation_bound` gave one direction from the GLUE);
* `clearing_nodes_of_lambdaHalf` : lane RC7's `clearing_nodes_genuine` restated with the corrected
  coordinates given as genuine elements `ũ_x ∈ Λ[1/2]` (the objects lane RC16 produces) and
  `C.u x j = [tʲ] ũ_x` (`coeffHalf`), instead of the auxiliary data `ũ_x = g_x/2^{e_x}`; the hypotheses
  `hrank`, `hacyc` are stated on the image of `ũ_x` in `Frac 𝒪`. The value at `t = 0` is the central
  specialization (`coeffHalf_zero_eq_centralSpecialization`), so this `C` also has `C.u 0 0 = ũ_0(0)`,
  the hypothesis `hC` of `baseZero_node_genuine` (`LambdaT.lean`).

Everything here is `PROVED` (from the named inputs of RC7's theorem, which are unchanged).
-/

namespace ZInQ.Manuscript.RC.Rings

open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Determinant

/-- **Tex 4916–4918, 5698–5705 (PROVED).** The embedding `Λ[1/2] → Frac 𝒪` of `LambdaHalfCoeff.lean`
is `ι : Frac Λ → Frac 𝒪` composed with RC16's `Λ[1/2] ⊂ Frac Λ`. -/
theorem iotaO_lambdaHalfToFrac (u : LambdaHalf) : iotaO (lambdaHalfToFrac u) = halfToFracO u := by
  have h : iotaO.comp (lambdaHalfToFrac : LambdaHalf →+* FractionRing Lambda) = halfToFracO := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (2 : Lambda)) ?_
    ext f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgHom.commutes,
      halfToFracO_algebraMap]
    exact iotaO_algebraMap f
  exact congrArg (fun φ : LambdaHalf →+* FractionRing OO => φ u) h

/-- **(5.5) in valuation form on the genuine `Λ[1/2]`** (tex 4914–4920, 5698–5700; PROVED): for
`u ∈ Λ[1/2]` and `C ∈ ℕ`, `v_𝒪(u) ≥ −C` iff `2^C u ∈ Λ`. -/
theorem neg_le_vO_iff (C : ℕ) (u : LambdaHalf) :
    (((-C : ℤ)) : WithTop ℤ) ≤ vO (halfToFracO u) ↔
      (2 : LambdaHalf) ^ C * u ∈ (algebraMap Lambda LambdaHalf).range := by
  constructor
  · intro h
    rw [← iotaO_lambdaHalfToFrac] at h
    exact integral_form_of_valuation_bound_genuine C u h
  · rintro ⟨g, hg⟩
    have h1 : 0 ≤ vO (halfToFracO ((2 : LambdaHalf) ^ C * u)) := by
      rw [← hg, halfToFracO_algebraMap]
      exact (vO_nonneg_iff _).mpr ⟨lamToO g, rfl⟩
    rw [map_mul, map_pow, map_ofNat, AddValuation.map_mul, AddValuation.map_pow, vO_two] at h1
    induction hv : vO (halfToFracO u) using WithTop.recTopCoe with
    | top => exact le_top
    | coe m =>
      rw [hv] at h1
      have h2 : (0 : ℤ) ≤ C • (1 : ℤ) + m := by
        have : ((0 : ℤ) : WithTop ℤ) ≤ ((C • (1 : ℤ) + m : ℤ) : WithTop ℤ) := by
          rw [WithTop.coe_add, WithTop.coe_nsmul, WithTop.coe_one]
          exact h1
        exact_mod_cast this
      rw [nsmul_eq_mul, mul_one] at h2
      exact_mod_cast (show -(C : ℤ) ≤ m by omega)

/-- **Proposition `ex:limits-fixed-field-clearing`, (5.9), with genuine coordinates `ũ_x ∈ Λ[1/2]`**
(tex 5486–5507, 5605–5629, 5491–5496; PROVED from RC7's named inputs). Lane RC7's
`clearing_nodes_genuine` with its auxiliary data `u, e, g, hu` (`ũ_x = g_x / 2^{e_x}`) replaced by the
family `ũ : Addr b → Λ[1/2]` and `C.u x j := [tʲ] ũ_x` (`coeffHalf`); the coordinate hypotheses `hrank`,
`hacyc` (RC7's ELLIOT inputs E1–E2) are stated on the image `halfToFracO (ũ x)` of `ũ_x` in `Frac 𝒪`.
All other hypotheses are RC7's, verbatim. -/
theorem clearing_nodes_of_lambdaHalf {b : ℕ}
    (B : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO) (hn : 2 < B.n)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam OO))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra OO (SignGroup b)) (a : ℕ)
    (ũ : Addr b → LambdaHalf)
    (RankOne Acyclic : Addr b → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → RankOne x →
      halfToFracO (ũ x) = evK (sgnChar x) η * evK (sgnChar x) κ * sd.αK (evK (sgnChar x)) *
        (((2 : FractionRing OO) ^ a)⁻¹ * sd.βK (evK (sgnChar x))) * cleanT (evK (sgnChar x)) B ε)
    (hacyc : ∀ x, evK (sgnChar x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (sgnChar x)) = 0 ∧ halfToFracO (ũ x) = (0 : FractionRing OO))
    (hpole : ∀ x M i, ∀ j k,
      ((B.A i).map (signEval (sgnChar x))) j k ∈ genuinePole.poleModLE M (4 * M))
    (dK hK cE tK : ℕ) (hm : B.mTot ≤ dK + 5) (hh : B.hSmith ≤ hK + 2 * cE + 2 * tK) :
    ∃ C : ZInQ.Contrib.CloudB3RC53.CoordData b, C.u = (fun x j => coeffHalf (ũ x) j) ∧
      ZInQ.Contrib.CloudB3RC53.ClearingIdentity C ∧
      (∀ M : ℕ, ZInQ.Contrib.CloudB3RC53.PoleBound C (16 * (dK + 5) * M) M) ∧
      ZInQ.Contrib.CloudB3RC53.BaseRegular C (a + 4 * B.hSmith) ∧
      a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) ∧
      ∀ x, C.u x 0 = centralSpecialization (ũ x) := by
  obtain ⟨e, g, hcoef, huK⟩ := exists_coeffHalf_uK_family ũ
  obtain ⟨C, hCu, h1, h2, h3, h4⟩ := clearing_nodes_genuine B hn haug sd κ ε η a
    (fun x j => coeffHalf (ũ x) j) e g hcoef RankOne Acyclic hpat
    (fun x hx hr => by rw [← huK x]; exact hrank x hx hr)
    (fun x hx ha => by rw [← huK x]; exact hacyc x hx ha)
    hpole dK hK cE tK hm hh
  refine ⟨C, hCu, h1, h2, h3, h4, fun x => ?_⟩
  rw [hCu]
  exact coeffHalf_zero_eq_centralSpecialization (ũ x)

end ZInQ.Manuscript.RC.Rings
