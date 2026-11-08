# Actual paired functionals and derivative normalization

Date: 2026-11-08. Research task `/root/arithmetic_functionals`, a separately instantiated model agent. This is a bounded source audit and ordinary-mathematical derivation, not independent whole-paper acceptance or a Lean replay. No manuscript, frozen research source, acceptance record, dependency, or remote was modified.

## 1. Verification target

Determine whether the actual functionals in V13 can be identified with the rows required by `BoundaryCupIdentity`, and whether their relative normalization requires an additional global comparison between the finite and singular Selmer complexes.

Reviewed checkout: `derivative-switch-review`, clean HEAD `e653d6ff295ae4e0535710a7d64aa255d294d211`. SHA-256 of raw bytes:

| File | SHA-256 |
| --- | --- |
| `manuscripts/quartic_v13.tex` | `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd` |
| `research/scalar-ratio/CONTRACT.md` | `7d7d69aa9fb2cae043ba29c93a0de5099ad552d387e1f53b09f9f58909cc4aca` |
| `lean/Research/DerivativeSwitch/BoundaryCup.lean` | `64750e7706f82cf0a47b76c80503bcab0577c2aa18f9703c09b4b8288be0df90` |
| `docs/audit-history/issue2/evidence/determinants.md` | `648a83cfec26f3032dc75aa04be03870c1864173c60daed3ff082935db703bd5` |

The governing `AGENTS.md`, audit-history protocol and research-review protocol were read. Earlier determinant history was read as an argument/excerpt rather than treated as an acceptance certificate. Its invocation of the original report's Section 9 does not display that section's proof; its full historical normalization justification remains unresolved in this bounded audit.

## 2. Independent re-derivation (outline)

### The actual functional is specified, not a chosen primitive generator

V13 lines 3842–3861 and 3873–3891 define a single generic functional for each actual class:

`z_perp = j_U^{-1} c(z)`, and `lambda_z(w) = PD_U(w,z_perp)`.

Here `c` is actual conjugate-dual transport and `j_U` is the orthogonal-to-transported comparison. Lines 3974–3999 give these formulas on integral cochains over the completed coefficient ring, with a homotopy inverse and a closed degree-two row. Thus for the switched object the row is specifically

`lambda_B = PD_S(-, j_S^{-1} c(B))`.

There is no freedom here to replace it by a separately normalized primitive row. There is also no claim that a determinant-line map acts on the individual degree-two functional spaces.

At the derivative place, `j_F` and `j_S` are the identity under the specified integral orthogonal local-condition identifications. For the singular condition this is explicitly checked at lines 5351–5368; finite self-orthogonality is specified at 5020–5028 and 5044–5059. The old-place comparisons and active/moving contractions can affect the chosen cochain representative elsewhere, but the inverse comparison commutes with the retained localization diagram. Therefore the derivative-place localization of `j_U^{-1}c(z)` is the localization of the transported class itself, up to the retained boundary homotopy. Pairing a closed local boundary direction is insensitive to that homotopy.

This reduces the question to local transport and the boundary–cup formula. An isomorphism `C_F -> C_S`, a strict automorphism, or a separate map from the functional of A to the functional of B is unnecessary.

### One coefficient J, and a separate tame pullback sign

The coefficient pairing is explicitly

`Q(x,y) = e_2(x,Jy)`, with `J = rho_T(tau)`,

at lines 2898–2908 and 2935–2957. It is linear over the same coefficient ring: neither `t` nor the group-ring basis is involuted. The source expressly warns that the J is already part of the duality convention.

Since `J^2=1` and `det J=-1`, the alternating Tate form satisfies

`Q(x,y)=Q(y,x)`.

This symmetry is a statement about the coefficient pairing Q. It must not be confused with the sign of a raw cup product between two degree-one cochains.

At the inert derivative prime, conjugate cochain pullback fixes the finite Frobenius generator and acts on tame inertia by the inverse rational Frobenius exponent. Write that exponent as `h=ell^{-1}` at finite precision. The retained congruences force `h=-1` in the limit. The two resulting actions after putting the coefficient J back in are J on the finite coordinate and −J on the singular coordinate, exactly as computed in V13 lines 5196–5220. Thus, when J is already included in Q, the residual cochain actions are +1 on the finite coordinate and −1 on the singular coordinate.

The displayed calculation appears in the quadratic-specialization discussion, but its local mechanism does not require the global character to be quadratic: at this derivative prime the coefficient character is trivial (3405–3414 and 3435–3446), and the Frobenius/tame calculation depends only on that local condition and H12. A change of transported place or coefficient frame can introduce a shared character-unit or orientation-unit; it does not introduce unrelated nonunit factors for A and B. Such units must be retained consistently rather than discarded.

### Boundary–cup calculation in one explicit convention

Use the cone convention

`d(g,u,l)=(dg,du,loc(g)-i(u)-d(l))`.

A boundary from the opposite local plane is represented by `(0,0,-s)` or `(0,0,-f)`. The boundary–cup adjunction then has the same cone sign in both cases:

`lambda_A(partial_S(s)) = -inv(s cup loc(A_perp))`,

`lambda_B(partial_F(f)) = -inv(f cup loc(B_perp))`.

The local cup formula has raw mixed part

`epsilon * (Q(f,s') - Q(s,f'))`.

The actual local class relation is `loc(A)=(v,0)` and `loc(B)=(0,Jv)`, with the same multiplier L. After conjugate pullback the raw dual local coordinates are `(v,0)` and `(0,h Jv)` in these transported bases. Therefore, writing `beta(f,s)=epsilon Q(f,s)`, direct substitution gives

`lambda_A(partial_S(s)) = beta(v,s)`,

`lambda_B(partial_F(f)) = -h beta(f,Jv)`.

At the retained limit h=−1, both evaluations have the same displayed effective beta sign. A uniform change of trace, cone, or tame orientation can alter these formulas by a unit. The relevant conclusion is the relative unit, not a preferred exact numerical sign.

The frozen Lean adapter at `BoundaryCup.lean:33–41` requires

`lambda_F(AS s)=c_F beta(v,s)`,

`lambda_S(AF f)=-c_S beta(f,Jv)`.

Thus the convention above instantiates `c_F=1`, `c_S=h`; in the limit `c_S=-c_F`. It does **not** instantiate the stronger common-normalizer specialization `c_F=c_S`. With a shared additional scalar kappa it gives `c_F=kappa`, `c_S=h*kappa`; the ratio remains a unit even when kappa is a nonunit. The frozen `integral_boundary_cup_adapter` already permits this.

In particular, for fractional complement x and `eta=area(v,x)`, the limiting cross-evaluations are `q_F=epsilon*eta` and `q_S=-epsilon*eta` in this convention. The scalar-ratio theorem gives `delta*u_F/u_S=1`, hence `u_F=-u_S` when `delta=-1`. This is compatible with the manuscript's equality of valuations. Exact equality of numerical cofactor coordinates requires an orientation adjustment or different normalization convention; it should not be inferred from the common-normalizer corollary without checking its hypotheses.

The adjunction used here is a concrete cone calculation. A primary-source locator is Nekovar, *Selmer complexes*, Astérisque 310 (2006), §6.2.2 (local cup products) and §6.3.3 (global compatibility): [published Numdam source](https://www.numdam.org/item/AST_2006__310__R1_0.pdf). In this subtask I checked the displayed local cone/cup convention in §6.2.2; the parallel cochain investigator owns the detailed §6.3.3 chain-level source check. This report does not duplicate or replace that independent check.

## 3. Checks

### Fixed multipliers

H11 (3208–3223) fixes one L for all derivative stages; H19 (3323–3337), the coefficient push (3405–3414), and the concluding statement (3544–3546) preserve that multiplier. The paired-functional proof expressly retains L in the actual z, permits a=0 over the completed ring, and forbids dividing out L or changing the determinant basis (4001–4011).

Linearity of conjugate transport, inverse comparison and duality gives `lambda_(Lz)=L lambda_z`. Consequently using the fixed actual class on both sides cannot introduce an extra relative L. A separately chosen clearing factor for each functional would change the object and is not the manuscript's construction. A single common clearing factor would cancel in the unit comparison even if nonunit.

### Localization and exceptional cases

Over `O[G]`, active and moving contractions are integral and the old-support comparisons are integral (3893–3896, 3917–3999). At height-one primes other than (2), integrality is claimed separately for the primitive scalar functional; active ramified inertia is −2, the moving contraction uses t away from (t), and the central Frobenius adjugate contraction handles (t). At (t+2), the inertia contraction applies (3897–3911). These are not claims that every relaxed universal functional is regular at every scalar prime.

The switched-functional check at 5351–5373 uses the derivative-plane identity, the same old comparisons, and exactly those primitive contraction regimes. The derivative boundary calculation itself does not invert t, 2, a localization vector, or a Frobenius determinant. Its unit ratio h is a unit in every ring in question; the limiting value −1 is a unit even at residue characteristic two. Thus the normalization calculation introduces no extra exceptional localization.

### Inner limits and actual objects

The finite source retains the actual cycles and local witnesses (3509–3542), the local cup diagrams and their homotopies (3434–3507), and the duality/localization homotopies (4568–4574). The inner-limit lemma transports the fixed finite diagram and preserves polynomial identities and retained homotopy inverses (4577–4592, 4623–4636). The identities above must be put into this same retained tuple; equality of abstract cohomology dimensions would not suffice.

This is preservation of a boundary–cup identity after it is derived, not an independent proof of every finite-free-model or arithmetic-existence premise. It is not a new assertion of uniform rank bounds for an entire unbounded derivative family.

### Downstream identity and nonzero conditions

The consumed coordinate is the tensor of the actual z with its actual lambda, in the retained determinant basis (4014–4029). The local switch assumes nonzero generic localization (5030–5037). Its inner generic rank-one claim is distinct from the outer rank drop at 5126–5138. No primitive replacement of the actual z or lambda is used in this calculation. Strict torsion and the common-strict matrix/determinant realization remain the separate determinant-comparison component.

## 4. Discrepancy report

1. **The apparent free normalizers are more constrained by the source than the abstract adapter assumes.** Once actual `lambda_z=PD(-,j_U^{-1}c(z))` is used and j is identity at the derivative place, the opposite-boundary values are fixed local cup evaluations. No additional map between the two global Selmer complexes is required to determine them.
2. **Exact common normalization is sensitive to conjugate pullback.** In the explicit convention above the tame sign gives `c_S=-c_F`, not `c_S=c_F`. Forgetting this sign, or inserting J again into a pairing already containing J, can produce an incorrect exact-equality claim. The unit-ratio adapter is sufficient and remains applicable.
3. **A source-only assertion of integrality is not by itself a proof of the normalization identity.** The route that closes the scalar discrepancy is the actual boundary–cup computation, followed by the identity property of the orthogonal comparison at the derivative place. Lines 5086–5092 compress that argument and do not display it.
4. **Historical status is not settled by the excerpt.** Prior source components are present; the full original Section 9 proof was not established by this bounded inspection. The calculation is a proposed explicit reconstruction/application of those components, not a priority claim or a claim that the old manuscript theorem was false.

## 5. Certification result

**Bounded result:** the actual paired-functional construction removes arbitrary independent normalizations. The local conjugate-pullback calculation yields an integral-unit ratio (in the displayed convention −1) between the frozen adapter's normalizers. Thus this functional audit finds no normalization obstruction requiring a global strict automorphism or a finite/singular quasi-isomorphism.

**Remaining acceptance step:** bind the cone boundary maps and the conjugate local coordinates to the exact retained arithmetic diagram, combine the parallel primary-source boundary–cup check with the common-strict determinant realization, and obtain a non-author review of the resulting application record. The precise sign above is convention-dependent and must not be silently advertised as common normalization. No full arithmetic theorem, manuscript repair, formal arithmetic instantiation, cloud result, or upstream acceptance is certified by this report alone.
