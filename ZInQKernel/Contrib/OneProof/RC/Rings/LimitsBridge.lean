import ZInQKernel.Contrib.OneProof.RC.Limits.OuterDVR
import ZInQKernel.Contrib.OneProof.RC.Rings.OValuation
import ZInQKernel.Contrib.OneProof.RC.Uniform.OuterContradiction

/-!
# Lane RC20: the outer DVR (5.3) built from copies of the genuine `𝒪`

Manuscript (`diophantine_zq.tex`, 11/5 version), proof of Lemma `ex:limits-outer-evaluation`,
tex 4719–4730: "For copies `𝒪_j` of `𝒪`, form `𝒪_∞ = (∏_𝒰 𝒪_j)/{(x_j) : v₂(x_j) →_𝒰 ∞}` (5.3). A nonzero
element has valuation one fixed nonnegative integer on a set in `𝒰` and is that power of two times a
unit. ... Thus (5.3) is a DVR with uniformizer two and characteristic-zero fraction field."

Lane RC6 (`Limits/OuterDVR.lean`) proved this for an arbitrary DVR `R` with uniformizer `ϖ` (instances
`OInf U ϖ`, `[Fact (Irreducible ϖ)]`) and recorded "passing from `Λ_(2)` to its `2`-adic completion `𝒪`"
as GLUE. Lane RC16 (`Uniform/OuterContradiction.lean`) uses the ideal of (5.3) through the predicate
`OuterNegligible v 𝒰` for a valuation `v` on `Frac 𝒪`. This file:

* applies RC6's construction to the genuine `𝒪 = Determinant.OO` with `ϖ = 2` (`fact_irreducible_two_OO`,
  `outerDVR_genuine`): `𝒪_∞` is a DVR with uniformizer `2`, of characteristic zero, with
  characteristic-zero fraction field — the GLUE step is no longer needed;
* identifies RC6's ideal with RC16's predicate for the genuine valuation `v_𝒪`
  (`mem_infinitesimals_iff_outerNegligible`), and so "a sequence of elements of `𝒪` is a nonzero element
  of `𝒪_∞` iff it is not negligible" (`toOInf_ne_zero_iff_not_outerNegligible`), the reading of
  `OuterNegligible` stated in RC16's module docstring.

Everything here is `PROVED`.
-/

namespace ZInQ.Manuscript.RC.Rings

open ZInQ.Manuscript.RC.Limits ZInQ.Manuscript.RC.Determinant ZInQ.Manuscript.RC.Uniform Filter

/-- **Tex 4729 "uniformizer two" (PROVED).** The uniformizer of the genuine `𝒪`, as the `Fact` used by
RC6's instances. -/
instance fact_irreducible_two_OO : Fact (Irreducible (2 : OO)) := ⟨irreducible_two_OO⟩

/-- **(5.3) for copies of the genuine `𝒪`** (tex 4666, 4719–4730; PROVED). For every ultrafilter `𝒰`
(nonprincipality is not used), the outer quotient `𝒪_∞ = (∏ 𝒪)/{v₂ →_𝒰 ∞}` of RC6 is a DVR in which
(the image of) `2` is a uniformizer generating the maximal ideal, `𝒪 → 𝒪_∞` is injective, and `𝒪_∞` and
its fraction field have characteristic zero. -/
theorem outerDVR_genuine {ι : Type*} (U : Ultrafilter ι) :
    IsDiscreteValuationRing (OInf U (2 : OO)) ∧ Irreducible (2 : OInf U (2 : OO)) ∧
      IsLocalRing.maximalIdeal (OInf U (2 : OO)) = Ideal.span {(2 : OInf U (2 : OO))} ∧
      Function.Injective (algebraMap OO (OInf U (2 : OO))) ∧
      CharZero (OInf U (2 : OO)) ∧ CharZero (FractionRing (OInf U (2 : OO))) := by
  have hirr : Irreducible (2 : OInf U (2 : OO)) := by
    have h := irreducible_algebraMap U (2 : OO)
    rwa [map_ofNat] at h
  refine ⟨inferInstance, hirr, ?_, algebraMap_injective U irreducible_two_OO, inferInstance,
    charZero_fractionRing U (2 : OO)⟩
  have h := maximalIdeal_eq_span_algebraMap U (2 : OO)
  rwa [map_ofNat] at h

/-- **Tex 4724 (PROVED).** RC6's ideal of (5.3) for the genuine `𝒪` is RC16's `OuterNegligible` for the
two-adic valuation `v_𝒪`: a sequence `(x_j)` of elements of `𝒪` satisfies "`2ⁿ ∣ x_j` for `𝒰`-almost
all `j`, for every `n`" iff "`v_𝒪(x_j) ≥ N` for `𝒰`-almost all `j`, for every `N ∈ ℤ`". -/
theorem mem_infinitesimals_iff_outerNegligible {ι : Type*} (U : Ultrafilter ι) (x : ι → OO) :
    x ∈ infinitesimals U (2 : OO) ↔
      OuterNegligible vO U (fun j => algebraMap OO (FractionRing OO) (x j)) := by
  rw [mem_infinitesimals]
  constructor
  · intro h N
    filter_upwards [h N.toNat] with j hj
    have h1 := (pow_dvd_iff_le_dvrAddVal (K := FractionRing OO) irreducible_two_OO N.toNat
      (x j)).mp hj
    exact le_trans (by exact_mod_cast Int.self_le_toNat N) h1
  · intro h n
    filter_upwards [h (n : ℤ)] with j hj
    exact (pow_dvd_iff_le_dvrAddVal (K := FractionRing OO) irreducible_two_OO n (x j)).mpr hj

/-- **Tex 4706–4714, 4724–4727 (PROVED).** For a sequence of elements of the genuine `𝒪`: its class in
`𝒪_∞` is nonzero iff the sequence is not `OuterNegligible` for `v_𝒪` (the reading of RC16's predicate as
"a nonzero element of `𝒪_∞`"). -/
theorem toOInf_ne_zero_iff_not_outerNegligible {ι : Type*} (U : Ultrafilter ι) (x : ι → OO) :
    toOInf U (2 : OO) x ≠ 0 ↔
      ¬ OuterNegligible vO U (fun j => algebraMap OO (FractionRing OO) (x j)) := by
  rw [Ne, toOInf_eq_zero_iff, mem_infinitesimals_iff_outerNegligible]

/-- Non-vacuity: for any ultrafilter, the constant sequence `1` is a nonzero element of `𝒪_∞` and the
sequence `(2^j)` is negligible. -/
example {ι : Type*} (U : Ultrafilter ι) :
    toOInf U (2 : OO) (fun _ => 1) ≠ 0 ∧
      OuterNegligible vO (Ultrafilter.of (Filter.atTop : Filter ℕ))
        (fun j => algebraMap OO (FractionRing OO) ((2 : OO) ^ j)) := by
  constructor
  · rw [toOInf_ne_zero_iff_not_outerNegligible]
    intro h
    obtain ⟨j, hj⟩ := (h 1).exists
    rw [map_one, (vO).map_one] at hj
    exact absurd hj (by decide)
  · intro N
    have hev : ∀ᶠ j in (Ultrafilter.of (Filter.atTop : Filter ℕ) : Filter ℕ), N.toNat ≤ j :=
      Ultrafilter.of_le _ (Filter.eventually_ge_atTop N.toNat)
    filter_upwards [hev] with j hj
    have h1 := (pow_dvd_iff_le_dvrAddVal (K := FractionRing OO) irreducible_two_OO j
      ((2 : OO) ^ j)).mp dvd_rfl
    refine le_trans ?_ h1
    exact_mod_cast le_trans (Int.self_le_toNat N) (by exact_mod_cast hj)

end ZInQ.Manuscript.RC.Rings
