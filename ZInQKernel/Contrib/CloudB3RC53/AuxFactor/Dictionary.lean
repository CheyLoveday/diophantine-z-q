import ZInQKernel.Contrib.CloudB3RC53.AuxFactor.Wiring
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Rules

/-!
# AuxFactor, part 5: a local lemma for the coefficient dictionary

Manuscript `diophantine_zq.tex`, App G, proof of Proposition `ex:app-rough-companion`, tex
10089–10098 and 10131–10139: "For the negative types used in the rough companion … every unit seed
is nonempty. A seed of least positive size has no dependence on internal edge bits … If a list
with the same total label contains the first `r − 1` seed anchors and a nonempty remainder,
contract that remainder into the last anchor … Prepare these sources and nonempty seeds for every
total type at the fixed support. There are finitely many. A bounded supply of dummy anchors and
reserves works for all of them. For each `h` realize that supply by distinct primes avoiding the
entire fixed support and `h` … For the total type that actually occurs, `hk'` is partitionable."

The round-3 theorem `auxFactor_of_dictionary` that stood here was removed (round-4 review): its
hypotheses (unit seeds at every total type, and a sufficient condition for `W.Partitionable` at
every `d ≠ 0` read through the prime set of `|d|`) force `W.Partitionable` at `d³`, `q²d` and
`−d`, so they cannot hold for genuine data. The corrected form is RC0's `auxFactor_of_prepared`
(`RC/Wiring/AuxFactor3.lean`): unit seeds only at the prepared total types and partitionability
only on the filter (negative, squarefree, prime to the support; tex 2296–2297).

What remains here is the local lemma `not_dvd_of_isSquareAt` used by that corrected form: a
squarefree integer that is a square in `ℚ_p` is prime to `p`.
-/

namespace ZInQ.Contrib.CloudB3RC53.AuxFactor

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Symbols
  ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

/-- A square of `ℚ_p` has even valuation, so a squarefree integer that is a square at `p` is prime
to `p`. `PROVED`. -/
theorem not_dvd_of_isSquareAt {p : ℕ} (hp : p.Prime) {x : ℤ} (hsf : Squarefree x)
    (hsq : Nonvanishing.IsSquareAt p (x : ℚ)) : ¬ (p : ℤ) ∣ x := by
  haveI := Fact.mk hp
  intro hpx
  have hx0 : x ≠ 0 := by rintro rfl; exact not_squarefree_zero hsf
  obtain ⟨y, hy⟩ := hsq (Fact.mk hp)
  have hxq : ((x : ℚ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hx0
  have hy0 : y ≠ 0 := by rintro rfl; rw [mul_zero] at hy; exact hxq hy
  have hv := congrArg Padic.valuation hy
  rw [Padic.valuation_mul hy0 hy0, Padic.valuation_ratCast, padicValRat.of_int] at hv
  -- `v_p(x) = 1`
  have h1 : padicValInt p x = 1 := by
    have hn : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx0
    have hle : x.natAbs.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hn).mp (Int.squarefree_natAbs.mpr hsf) p
    have hge : 1 ≤ padicValNat p x.natAbs :=
      one_le_padicValNat_of_dvd hn (Int.natCast_dvd.mp hpx)
    rw [← Nat.factorization_def _ hp] at hge
    rw [show padicValInt p x = padicValNat p x.natAbs from rfl, ← Nat.factorization_def _ hp]
    omega
  rw [h1] at hv
  omega

end ZInQ.Contrib.CloudB3RC53.AuxFactor
