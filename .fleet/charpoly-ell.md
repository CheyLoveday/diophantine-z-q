# charpoly-ell

**Verdict.** `charPolyIndepOfEllAlgClosed` (Mumford §19 Thm 4, ℓ-independence of the char. poly of `T_ℓ φ`) is
**reduced, not proved outright**:

    ZInQ.Contrib.OneProof.CharPolyEll.charPolyIndepOfEllAlgClosed_of_degEqDetTate
      (hD : DegEqDetTate) (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) :
      ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed

compiled, axioms `propext, Classical.choice, Quot.sound`. `DegEqDetTate` is one new printed leaf: Mumford §19 Thm 4's
first assertion `deg ψ = det T_ℓ(ψ)`, over a genuine Lean degree `degEnd` (function-field degree via the stalk map
at the generic point, 0 for non-isogenies; sanity lemma `degEnd 1 = 1`). `homFreeFiniteAlgClosed` is already open in
the same bundle (only `End A` finite over ℤ is used). Net count 0 (−1 field, +1 leaf), not the −1 target.

**Why not −1.** The tree has no degree theory (no isogeny degree, theorem of the cube or Riemann–Roch on abelian
varieties), and no open field gives an ℓ-independent integer invariant of an endomorphism. The suggested shortcut
(det(n − T_ℓφ) = deg(n − φ) "because both count the kernel on ℓ-power torsion") only matches ℓ-adic absolute values,
and these do not determine the polynomial: for ℓ ≡ 3 mod 4, X²+1 and X²+1+ℓ³ are ℓ-adic units at every integer.

**What compiles.** `scratch/charpoly-ell/CharPolyEll.lean` (with a verbatim copy of the field, checked by `rfl`) and
the contribution `ZInQKernel/Contrib/OneProof/CharPolyIndepOfEllAlgClosed.lean`. Glue in Lean: `T_ℓ` as a ring hom
`End A → Matrix`; charpoly(n) = deg(n − φ); Lagrange interpolation over ℚ; integrality via the roots of the char.
poly being roots of a monic integer polynomial annihilating φ; uniqueness across ℓ. Autofold spec
`scratch/charpoly-ell/autofold.json` (dry run: strict 34/11 → 34/11). `#discharges` (after a full
`lake build +ZInQKernel.OneProof.Main`, 13699 jobs): DISCHARGES `OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed`, still assumes
`[DegEqDetTate, HomFreeFiniteAlgClosed]`, standard axioms. The dry-run fold module (`sixContactMin_of_open36`) compiles
with standard axioms.

**What remains.** Proving `DegEqDetTate` would need P1 (deg is a polynomial function of degree 2g, printed) and P3
(ℓ-part of deg = ℓ-part of #ker, printed), plus glue (multiplicativity, ℓ-adic kernel count from
`mumfordTorsionAlgClosed`, a multiset lemma). Details are in the report, §4.
