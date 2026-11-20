import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Theorem 5.3, Lane RC34: free lines of rank-one modules (the vocabulary of the point half)

Lemma `ex:arith-central-specialization` (`diophantine_zq.tex`, tex 3895–3986) and the proof of
Proposition `ex:arith-central-calibration` (tex 4005–4021, 4057–4064) measure the central class
and its paired functional by their **free-line coefficients**: "On a rank-one Mordell–Weil free
lattice, both free-line coefficients consequently have valuation `j_rc(h,k) + v₂(Lm)`"
(tex 3905–3907). This file fixes the vocabulary.

* `IsFreeLineGenerator R g`: `g` is not torsion and every element of the module is an
  `R`-multiple of `g` modulo torsion (the module is a free line modulo its torsion, generated
  by the image of `g`).
* `IsFreeLineGenerator.coeff_unique`: modulo torsion the coefficient on a free-line generator is
  unique (over a domain).

Kinds: definitions and PROVED.
-/

namespace ZInQ.Manuscript.RC.CalPoint

variable (R : Type*) [CommRing R] {H : Type*} [AddCommGroup H] [Module R H]

/-- **A generator of the free line of a rank-one module, modulo torsion** (tex 3905–3907,
3977–3980): `g` is not torsion, and every `z` is `c • g` modulo the torsion submodule. -/
def IsFreeLineGenerator (g : H) : Prop :=
  (∀ r : R, r • g ∈ Submodule.torsion R H → r = 0) ∧
    ∀ z : H, ∃ c : R, z - c • g ∈ Submodule.torsion R H

variable {R}

/-- **The coefficient on a free-line generator is unique.** If `z − c • g` and `z − c' • g` are
torsion for a free-line generator `g`, then `c = c'`. PROVED. -/
theorem IsFreeLineGenerator.coeff_unique {g : H} (hg : IsFreeLineGenerator R g) {z : H}
    {c c' : R} (hc : z - c • g ∈ Submodule.torsion R H)
    (hc' : z - c' • g ∈ Submodule.torsion R H) : c = c' := by
  have h := Submodule.sub_mem _ hc' hc
  have e : z - c' • g - (z - c • g) = (c - c') • g := by
    rw [sub_smul]; abel
  rw [e] at h
  exact sub_eq_zero.mp (hg.1 _ h)

end ZInQ.Manuscript.RC.CalPoint
