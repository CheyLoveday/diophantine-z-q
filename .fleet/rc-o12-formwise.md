The formwise comparisons for (O.12) are proved on the finite window, conditional on the intrinsic-level realization data in `BlockLevels` and `AtLevel`. `seed_unramified` gives `hseed` on the active coordinates of every subset seed. `seed_fourier` gives `hexcl` in the original coefficient lattice: the diamond translate is the determinant translate divided by the odd unit `q`, and its coordinates are the local character scalars times the seed coordinates. `window_good_hecke` combines this with the ambient tests and supplies `good_hecke`.

All five files in `ZInQKernel/Contrib/OneProof/RC/O12Formwise/` passed sequential `lake env lean`. The 16 theorem audits and the constructor audit reported only `propext`, `Classical.choice`, and `Quot.sound`.

The remaining realization inputs are the lower-level bounds of the theta blocks, the specialization of the existing cuspidal good attachment and Fourier recurrence to those levels, and identification of the existing Eisenstein attachment with its normalized Dirichlet pair. The Eisenstein inertia and Frobenius comparisons are proved from that pair. Compatible realizations beyond a finite window and the other inputs to (O.12) stay with their respective lanes. No new print or manuscript error was established.

Report: `docs/research/rc-o12-formwise.md`. Results log: `scratch/rc-o12-formwise/log.md`.
Final result commit: `6200ca2f6a8954b14047bccab778769d6202fd63`. This status note is committed separately after it.
