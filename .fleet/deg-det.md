# deg-det (fleet note, provisional)

**Verdict.** Target (charPolyIndepOfEllAlgClosed removed, −1, no new leaf) not reachable: Mumford's proof of
§19 Thm 4 needs that deg is a homogeneous polynomial function on End(A) (theorem of the cube + Riemann–Roch),
which no open field supplies. Instead charpoly-ell's leaf `DegEqDetTate` (deg ψ = det T_ℓ ψ) is **proved in Lean**
from two printed leaves and two open fields, no glue:
`ZInQ.Contrib.OneProof.DegDet.degEqDetTate_of_printed (hP : DegHomogPoly) (hS : SepDegKernel)
(hM : AvSplit.MumfordTorsionAlgClosed) (hH : HomFreeFiniteAlgClosed) : CharPolyEll.DegEqDetTate`, and
`charPolyIndepOfEllAlgClosed_of_printed` for the field.

**Compiles** (standard axioms): `ZInQKernel/Contrib/OneProof/DegEqDetTate.lean` + helpers `DegEqDetTate/Algebra.lean`
(Mathlib-only algebra of Mumford's proof: Nullstellensatz extension of a multiplicative polynomial function,
det F(M) = ∏F(roots), ℓ-adic comparison lemma) and `DegEqDetTate/TateIndex.lean` (|det T_ℓ φ|_ℓ = |#ker φ|_ℓ for any
φ with finite kernel, Smith normal form over ℤ_ℓ). #discharges: discharges `charPolyIndepOfEllAlgClosed`, assumes
[DegHomogPoly, SepDegKernel, MumfordTorsionAlgClosed, HomFreeFiniteAlgClosed]. Autofold dry run 34/11 → 35/11
(+1 leaf, no glue rise); compiles.

**Remains.** Count: charpoly-ell's fold (34/11 → 34/11) stays better; recommended to fold that one. New leaves
`DegHomogPoly` (Mumford §19) and `SepDegKernel` (Mumford §4, §7) are printed form, locators UNVERIFIED.
Report: docs/research/deg-det.md.
