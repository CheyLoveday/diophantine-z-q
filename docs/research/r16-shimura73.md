# r16-shimura73: `r16CoreY` along the manuscript's own sources (Li 1975, Shimura 1973 Thm 1)

Task r16-shimura73 (2026-11-17). Scratch: `scratch/r16-shimura73/` (log `log.md`). Lean:
`ZInQKernel/Contrib/OneProof/R16ShimuraLi.lean` (namespace `R16ShimuraLi`).

## Known issues (for the lead, to raise with Jack)

1. **The manuscript's inference at diophantine_zq.tex L770-773 has the gap the review recorded, and this re-route
   reaches it.** The manuscript passes from "Li's Fricke formula makes the span of the coefficient conjugates
   Fricke-stable" and "Shimura's quotient construction and Euler-factor identity" to "`r_5` is a constituent of the
   Tate module of `A_f`". What Shimura 1973 Thm 1 gives (per the locator audit, row R16 of
   `docs/research/locators.md`, which read pp. 526-527) is the `ℚ`-rational quotient `A_f` of `J₁(N)`, the action of
   `K_f`, `dim A_f = [K_f : ℚ]`, and, under the Fricke-stability premise, the equality of the zeta function of `A_f`
   with `∏_σ L(s, f^σ)` (up to finitely many Euler factors). In Lean (`EulerIdentity`): the characteristic polynomial
   of Frobenius on all of `V_ℓ(A)` is `∏_{ι : K_f → ℂ} (X² − ι(a_p) X + ι(χ(p)) p)`.
   **What is missing.** That identity is a statement about the total characteristic polynomial; it does not mention
   the `K_f`-action at all, so it cannot say which `ι`-component of `V_ℓ(A)` carries which conjugate. Concretely
   (ON THE SPOT, a two-line remark, not built on): if `θ` is an action with the per-embedding property, `θ ∘ τ` for
   `τ ∈ Aut(K_f/ℚ)` satisfies the same Euler identity but its `ι`-component carries `ι(τ(a_p))`; and the multiset
   equality `⋃_ι {roots of the ι-component} = ⋃_ι {α_ι, β_ι}` does not split per `ι`. "`r_5` is a constituent of
   `V_5(A_f)` with traces `ι_5(a_p)`" (what L774-794 then use at `ℓ = 3, 5`) needs a per-embedding statement.
   **Which statement the chain would need.** `R16ShimuraLi.ShimuraTotalToComponents` (named, not proved, not
   repaired): for a quotient `π : J₁(N) ↠ A` of dimension `[K_f : ℚ]` whose Euler factors are Shimura's, some action
   `θ'` of `K_f` makes every `ι`-component of `V_ℓ(A)` carry trace `ι(a_p)` and determinant `ι(χ(p)) p` at every
   `p ∤ Nℓ`. The printed statement that supplies it is the Eichler-Shimura relation on `A_f` with `θ` the Hecke action
   (Shimura 1971 Thm 7.9 with Thms 7.11/7.14; Diamond-Shurman Thm 9.6.5 at `k = 2`, i.e. the Diamond-Shurman row
   `afCharpolyDS965` this task replaces); neither is cited at L768-773. With `∀ θ` instead of `∃ θ'` the needed
   statement is false (the `θ ∘ τ` remark).
2. **Shimura 1973 Thm 1 as the manuscript uses it is weaker than the use.** Besides item 1, the print's Euler-factor
   clause holds up to finitely many Euler factors (the exceptional set is UNVERIFIED here; the leaf takes an
   unspecified finite set, the weakest reading). The chain needs every `p ∤ Nℓ`; with a nonempty exceptional set that
   also needs good reduction of `A` outside `N` and Chebotarev (folded into `ShimuraTotalToComponents`).
3. **Step not covered by the two citations: Li's formula is applied to every conjugate `f^σ`**, which needs the
   conjugates to be newforms (`ConjNewform`: Shimura 1971 Thm 3.52 with the Galois stability of the new space,
   numbers UNVERIFIED). Small and standard, but uncited at the step.

Verdict: the re-route compiles as a reduction (`r16CoreY_of_shimura_li`), but it ends in the known gap. The two
printed leaves plus `ConjNewform` prove `R16CoreYTotal` (the per-embedding clause replaced by Shimura's total Euler
identity) with no other input; `r16CoreY` itself needs `ShimuraTotalToComponents`, which no cited source gives.
**Recommendation: do not fold before Jack rules on item 1.** The autofold spec is written and dry-run (section 5) so
that the fold is ready either way.

PLACEHOLDER-REST
