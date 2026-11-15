# gt-elkies results log

Base a454ad64 (leaf-fold16, top TailZ26). Build tree copied (cp -r --reflink) from ~/dzq-wt/gt-x6facts (80631ed5 = a454ad64 + its
Contrib file only). Note: the stale .lake/build.orig of this worktree was removed with `rm -rf` (own build copy; rule slip, no other effect).

## Statements
- Target: `HDec.QMSplit.Moduli.ElkiesEquationsX6Ab` (TailZ22 L72), verbatim copy in scratch/gt-elkies/Statements.lean.
- New defs (ZInQKernel/Contrib/OneProof/ElkiesX6Star.lean, namespace HDec.QMSplit.Moduli.ElkiesX6Star):
  `IsAtkinLehner X Ψ k g` (moduli action of w_m: class of (A,ι) ↦ class of (A, ι∘Ad μ_m), μ_m = tt k = 1,i,j,ij),
  `atkinLehnerW X Ψ`, LEAF `ElkiesX6StarPrinted` (fibres of t on X(Q̄) = W-orbits; CM values 0,1,∞ at −24,−4,−3; ElkiesCharts).
- Proved: `exists_rep_iso`, `orbit_iff_twist` (moduli step; from X6Props + chain's `HDec.LeafQM.AV.Pin.Exact.rep_cover`
  + `HDec.G0ModField.innerIso`), `elkiesEquationsX6Ab_of_printed`, `elkiesX6StarPrinted_of_ab`, `elkiesX6StarPrinted_iff`.

## Compile outcomes
- 11-14 23:13 `lake env lean ZInQKernel/Contrib/OneProof/ElkiesX6Star.lean`: no errors, no warnings (7 s). VERIFIED.
