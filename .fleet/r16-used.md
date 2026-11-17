# r16-used (fleet summary)

**Verdict.** The research field `r16CoreY` (Eichler–Shimura on `J₁(N)`, composite GLUE) cannot be removed:
no bundle field puts `ρ_f` inside `V_ℓ(J₁(N))`. It can be replaced by a single printed-form leaf:
`R16Used.AfTateCharPoly`, the existence form of Diamond–Shurman Lemma 9.5.3 and Thm 9.5.4 (numbers
UNVERIFIED). The leaf says: for a quotient `J₁(N) ↠ A` over `ℚ` with `θ : K_f → End⁰(A)`, `V_ℓ(A)` is free of
rank 2 over `ℚ_ℓ ⊗ K_f`, and the char. poly of Frobenius at `p ∤ Nℓ` over `ℚ_ℓ ⊗ K_f` is `X² − a_p X + χ(p)p`.
Proposed kind: published, flag unread. Autofold dry run: strict 46/10 → 47/9 (−1 GLUE), strictest 45/11 → 46/10.

**Consumer** (VERIFIED). There is a single use: `G0ModNewform.g13` → `commonConstituent_of_attached`, at
ℓ = 5, ι = embOf, for the newform from Pan via T24/T25, any level N and every J₁(N). It reads only
`[K_f:ℚ] < ∞`, π, θ, rank two and the trace. The weakest form is `R16Used.R16Trace`, and `g13` is re-proved
from it in `scratch/r16-used/Bypass.lean`.

**Compiles** (Lean 4.35 / Mathlib 4.35, standard axioms):
- `ZInQKernel/Contrib/OneProof/R16Used.lean` provides `r16_of_afTate`, `r16CoreY_of_printed`,
  `r16Trace_of_r16` and `r16Trace_of_coreY`. The proofs cover: the eigenfunctionals of a free rank-two
  module, ≅ Ω²; trace and det through `(ι_R M)ᵀ`; `[K_f:ℚ] < ∞` by faithfully flat descent; and `dim A` from
  rank two.
- `#discharges` reports r16CoreY discharged, still assuming `[AfTateCharPoly, MumfordTorsionAlgClosed]` (the
  latter is already a published field).
- The bypass compiles, and so does the autofold dry-run module (`sixContactMin_of_open30`).

**Remains.**
- A statement check of DS 9.5.3/9.5.4. The point to confirm is that the print states the characteristic
  polynomial over `K_f ⊗ ℚ_ℓ`, not only the annihilating relation. If it does not, flag the leaf "pending
  reading".
- A locators.md row (proposed in the report).
- The converse (leaf ⇐ r16 + glue) is argued but not formalized.
- The fold is not applied (integrator's step).

Report: docs/research/r16-used.md.
