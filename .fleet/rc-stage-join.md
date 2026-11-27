`pmSievedSource` keeps the exact late sieve list with the actual Appendix F
stage and integral lift and applies it to both. The class set and detector
weights come from the original geometry. The Eichler level in both is
`CST.newformLevel (Ecurve ℓ)` by proof. For arbitrary `F : PMLocal`, the
sieved `ThetaStage.Good` accepts exactly the primes outside
`F.support ∪ B.primes`, and the underlying stage accepts all those primes.

The refined type covers exactly the original stationary modulus primes and
this coefficient support once the local constructor supplies the original
support comparison. It provides the old-level and ambient coprimality tests,
`LevelSetup`, and the freshness needed by `hseed`, `hexcl`, and
`good_hecke`. All three files under `ZInQKernel/Contrib/OneProof/RC/StageJoin/`
passed `lake env lean -j1` in sequence. The 34 audits cover all 24 new
theorems and list only `propext`, `Classical.choice`, and `Quot.sound`.
No new prints.

The manuscript specifies the odd late sieve by operation and gives no
enumerated list. Tex 10527–10531 does not explicitly fix it before the odd
stages or bound the added coordinate rank on the same ultrafilter (V21).
A fixed list compatible with the original filter and depth is sufficient
for that bound. The actual list, original local vanishing, and the old
modular level's support bound remain inputs. The full list of remaining
hypotheses and owners is in `docs/research/rc-stage-join.md`.

Lean, report, and log SHA: `579a7bf827f3cb96d56ac5ad8dd20c51b7ead8eb`.
The final branch SHA is the commit containing this file; resolve it with
`git log -1 --format=%H -- .fleet/rc-stage-join.md`.
