# gt-shpair results log

Target: `ReductGlue.StrictHenselizationPair` (ZInQKernel/OneProof/H/TailZ14.lean L2055), GLUE composite.

## Plan (2026-11-14 23:00)
- Leaf: a strict-henselization form of BLR 1.2/2 (Néron models commute with O -> O^sh), stated for
  `IsSHUnram`-type extensions with `K₁/K` separable algebraic (pins O₁ ≅ O^sh in every characteristic);
  a specialization of the chain's existing `ReductGlue.NeronBaseChangeUnramifiedDVR` (checked in Lean).
- Glue (commutative algebra), to be proved in Lean in every characteristic and for imperfect residue
  fields: generalize sh-route's CA1-CA3 (char 0, perfect residue field).
  * key_finite: replace `card_inertia_eq_ramificationIdxIn` (needs separable residue fields) by
    |I|·|Aut(κP/κp)| = e·f and separable degrees: e(𝔮|p)·f(𝔮|p) = sepdeg(κ𝔮/κp) ≤ f(𝔮|p).
  * inertia field: separability of simple roots; normal closures of separable extensions.
  * E_{K'} ⊆ E_K(K'): p-power trick (x^q ∈ E_K(K'), x separable over E_K(K')).
