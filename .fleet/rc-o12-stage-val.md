`inputs_of_pm` applies the unchanged finite-precision (O.12) consumer to a valid odd stage and returns both constituent-model inputs. The integral (O.4) sum and the finite Brandt source use the same Eichler classes, mass factors, local weights and (P_M). The divisions and the intrinsic reading use the same integer depth and precision; the good-prime transfer preserves later label-only restrictions, and both sides use the same elliptic coefficients.

All three new files under `ZInQKernel/Contrib/OneProof/RC/O12StageVal/` compiled with one Lean job at a time. The 23 declaration audits use only `propext`, `Classical.choice`, and `Quot.sound`. No new prints were introduced.

The application still needs the actual stage identification and local frame geometry, (O.7) with its chosen integer representatives, the exact integral sieve and squarefree stage support, and App G's coarse bound and attained minimum on the full intrinsic filter. On the model side it needs the full compatible realization, formwise good operators and inertia, stationary type and finite-quotient data, the two-fresh field, and the same-lattice local input. The exact hypotheses and owners are in `docs/research/rc-o12-stage-val.md`.

Known issue: the address filter may incorporate later prime exclusions; tex 2026–2029 and 9471–9483 do not allow treating these as Fourier support. The proof uses the intrinsic odd filter throughout. The App F coefficient (H(mn)) also retains its phase in (O.7); only the integer representative used in the valuation has its phase removed.

Code and report SHA: `853d09093e716db634f1a42b9ee0fd47d0ab35a1`. The final SHA is the commit containing this handoff; resolve it with `git log -1 --format=%H -- .fleet/rc-o12-stage-val.md`.
