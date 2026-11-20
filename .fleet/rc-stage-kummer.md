The shared `StageKummer` used by `lamOf` now reduces each conductor-one datum at the detector's chosen place and applies its finite evaluation. The embeddings use one identification with the algebraic numbers in ℂ and recover the original witness embedding exactly. The family is zero off the moving split support. `Setup.hev` proves the existing witness pin, and `hev_at` supplies the exact homomorphism equality required at every evaluated split row.

`datumAt` fills the reference reduction from the two pointwise CM equations and the existing Artin and orbit data. `toOddStagedInstanceOfReference` uses those records to build the comparison core for the same family. The selector adapter retains the witness and the old index at every prepared simple zero. It still needs the algebraic parametrization value at each admissible hole.

All six files in `ZInQKernel/Contrib/OneProof/RC/StageKummer/` passed serial `lake env lean`; all 31 audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. No new prints. The two CM equations, actual orbit and local weight data, coarse geometry, and the theta coefficient reading remain separate inputs. See `docs/research/rc-stage-kummer.md` for their owners and the manuscript check.

Known issue: the inherited Jetchev–Kane citation at tex 8468–8474 does not cover level one. This implementation does not apply it there.

Final implementation and report SHA: `5790db3c66c429fcde4e14e0b1fbcaae502d2893`.
