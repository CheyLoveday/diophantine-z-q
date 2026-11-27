# (O.12): fixed-set realization

The per-set port is complete conditional on the actual theta blocks and the upstream inputs. For a fixed operator set `U`, `commonSpace` builds the constituent lattice for `U` and its subsets from the supplied blocks. The consumer proof chooses the four (O.12) representatives outside `U ∪ avoid` in that one space. Over all tested roots it gives the existing `O12Reading`, `FixedUFactorization`, and `PrimaryReading` types, hence the unchanged dictionary's `RulesUpTo` with `ApEven`. The prescribed-prime comparisons use `ExcludedAtOne` at the root only; (O.12) needs no such comparison.

The analytic stop is the existence of the actual weight-two `Blocks` and `Attachment` for each fixed `U` on a finite coefficient extension of the same stage. The [report](../docs/research/rc-o12-realize.md) states the exact Prop and lists the named stage, formwise, two-fresh, and local inputs. The inherited obsolete `hdiam` in `ThetaCoeff/Model.lean` is bypassed.

All three new Lean modules compile serially with `lake env lean -j1`. The 14 theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`. No prints were added.

Verified implementation and report SHA: `ac8b775f7a656e0961e2cfc9e89b1d821e8e156e`. The final status commit contains only this file; its SHA is `git log -1 --format=%H -- .fleet/rc-o12-realize.md`.
