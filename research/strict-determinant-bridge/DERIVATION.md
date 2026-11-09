# The common strict determinant factor and the actual coordinate

Date: 2026-11-09. Author: Codex `/root/determinant_attack`.
This is a source-bound ordinary proof and computational-check packet. It does
not change the manuscript or frozen 39-target packet and does not formalize
the determinant functor in Lean.

### 0) Problem restatement (brief)

The source is research checkout `fb29fe2bc6968e178a6458357c437574221b5338`.
Exact input hashes are in `SOURCES.json`. The target is the manuscript's actual
class-functional coordinate (`quartic_v13.tex`, 4014–4029), as consumed in the
derivative-switch paragraph, 5021–5093. It is a coordinate in an integral
inverse-determinant line, rather than a coordinate defined by a cofactor formula.

Relevant prior arguments were read: the frozen `Coordinate.lean` and
`CommonStrict.lean`, `UnitCriterion.lean`, scalar-ratio `DERIVATION.md`, and
arithmetic-boundary-cup `DERIVATION.md` §5. The latter already gives the ordinary
two-triangle wedge argument. The contribution here is its explicit bridge to
the actual integral basis, with the common possibly nonunit strict scalar and
the precise cofactor sign. The historical `issue2/evidence/determinants.md`
excerpt cites a section 9 not located in this bounded search; completeness of
that historical justification remains unresolved. This is not a claim that the
determinant-switch conclusion or wedge method is new.

The determinant application below is proved from actual integral triangles,
actual class/row identifications and generic rank hypotheses. Establishing the
actual boundary–cup identity, the orthogonal comparison, and their retained-limit
transport is work of the parallel packets. None is assumed merely because the
frozen algebra was checked. In particular this packet alone does not establish
the full arithmetic switch.

### 1) Assumptions ledger

- **Integral coefficients.** R is a DVR (a local domain with all invertible
  determinant lines trivialized is sufficient), with fraction field K. F and S
  are free R-modules of rank two. J:F→S is an integral isomorphism. Used for the
  two integral triangle trivializations and integral-unit conclusions. A general
  group ring with zero divisors is outside this scalar-field argument.
- **Actual diagrams.** The same perfect integral complex Cstr lies in actual
  triangles Cstr→CF→F[-1] and Cstr→CS→S[-1], with their actual boundary maps.
  The source explicitly retains D⁰ in all four derivative local conditions.
  Used for the determinant maps and generic long exact sequences. No triangle
  morphism or isomorphism CF≃CS is assumed.
- **Generic finite rank one and actual classes.** CF,K has cohomology only in
  degrees one and two, each of dimension one; A is a generator and maps to
  v≠0 in F_K. The actual B maps to Jv in S_K. Used to identify the strict
  cohomology, and then the actual cycle vectors.
- **Independent directions.** For some x with η=det[v,x]≠0, the actual vectors
  a=∂F(x), b=∂S(Jx) are independent in W=H²(Cstr,K). This must be proved from
  the actual exact-annihilator or nonzero cup evaluations, rather than from the
  determinant conclusion. Used to obtain the singular rank-one description.
- **Actual functionals.** λA,λB are the manuscript's PD-defined functionals,
  pulled back from H²(CF,K),H²(CS,K) to W as rF,rS. No primitive replacement or
  independent rescaling is allowed. Used to compute the actual tensors.
- **Actual integral bases.** e_str is one R-generator of det⁻¹Cstr. The retained
  bases of det⁻¹CF and det⁻¹CS are R-generators, not arbitrary nonzero K-vectors.
  Used to conclude that changes to retained bases are integral units.
- **Normalizer only for the last corollary.** qF=rF(b), qS=rS(a) satisfy qS=-qF,
  as supplied by the actual shared-trace boundary–cup calculation. This is not
  needed for the coordinate bridge itself. If absent, the exact scalar formulas
  below still expose the remaining normalization discrepancy.

### 2) Lemma-by-lemma resolution

**L1 — Strict cohomology and the actual rank-two boundary model: PROVED under
the finite-side hypotheses.**

The finite triangle gives H¹(Cstr,K)=ker(H¹(CF,K)→F_K)=0, since A maps to
v≠0 and spans H¹(CF,K). All other strict cohomology except H² vanishes, and

    0 → F_K/Kv → W → H²(CF,K) → 0.

Thus dim W=2, ker ∂F=Kv, and im ∂F=Ka. The derivative supplies
∂S(Jv)=0. Independent a,b imply b≠0, hence rank ∂S=1, and the singular
triangle has H¹,H² of dimension one. The injection H¹(CS,K)→S_K identifies
B with Jv and H²(CS,K)=W/Kb. Both equalities concern the actual maps in the
long exact sequences. Higher/lower concentration follows from the same
sequences, not a separate rank guess.

Over K, the cohomological truncation identifies Cstr,K with W[-2]. Each
triangle is then separately represented by the two-term boundary complex
[F_K --∂F→ W] or [S_K --∂S→ W], in degrees one and two, with one consistently
fixed connecting-map sign. This is the usual classification of the extension
by the actual connecting map: the fibre of F[-1]→W[-1] is [F→W]. It does not
identify CF with CS. Naturality of the determinant isomorphism for these
separate triangles is essential to L4.

**L2 — Exact-sequence determinant tensor formula: PROVED.**

Here is a precise convention that matches the frozen cofactor convention.
Let V,W be two-dimensional K-spaces, D:V→W rank one, z a nonzero generator
of ker D and λ:W→K annihilating im D. Choose x so (z,x) is a basis, and y
so (y,Dx) is a basis. The exact-sequence determinant identification sends

    (z ∧ x) ⊗ (y ∧ Dx)*  ↦  [z] ⊗ [y]*.

The star denotes the dual of the displayed top wedge; [y]* is dual to the
class of y in coker D. This specifies the target order: quotient lift FIRST,
boundary SECOND. Since λ=λ(y)[y]* on the quotient, the inverse image of the
actual class-functional tensor is

    t(D,z,λ) = λ(y) (z ∧ x) ⊗ (y ∧ Dx)*.             (1)

This formula is intrinsic. If x′=αx+βz, α≠0, then the numerator and boundary
vector both multiply by α. If y′=γy+δDx, γ≠0, then λ(y′)=γλ(y) and the
target wedge multiplies by γ. These factors cancel in (1); arbitrary choices
of x′ and quotient lift y′ have precisely this form. The construction is
linear in z and in the functional and agrees on a basis tensor with the
exact-sequence identification. It therefore identifies the actual tensor,
rather than assigning a scalar definition to it.

A determinant-functor convention ordering boundary before quotient differs
by -1 in this rank pattern. That is a single sign unit on both branches.
No comparison of degree-two functional spaces is induced by a determinant-line
isomorphism; λ remains the actual quotient functional throughout.

**L3 — Matching the full cofactor specification: REUSED with exact inputs.**

Choose integral local bases and a K-basis (w1,w2) of W. Let D,z,r be the
actual boundary matrix, actual cycle column, and actual pulled-back closed row.
Set B=[z,x], T=[y,Dx]. Then DB=T diag(0,1). Relative to the matrix determinant
basis e_mat=det(local basis)⊗(w1∧w2)*, equation (1) has coordinate

    u_mat = det(B) λ(y) / det(T).                       (2)

The frozen `coordinate_of_closed_frame` / `raw_side_coordinate` prove the
FULL equation z r = u_mat adj(D), including λ=0. They require exactly the
actual cycle equation, the closed row equation, and nonzero det B,det T;
none assumes normalization or the desired unit comparison.

For the finite side put y=b and Dx=a. For the singular side use z=Jv,
x_S=Jx, y=a and D_Sx_S=b. With θ=det[a,b] in the W-basis and δ=det J,

    u_mat,F = -η qF/θ,        u_mat,S = δ η qS/θ.       (3)

The sign comes from det[b,a]=-θ. In particular the normal differential
diag(0,1), z=e1, λ=e1* has u_mat=1. This explicitly fixes the convention.

The earlier arithmetic-boundary-cup §5 displays both wedge tensors with the
opposite global sign to (3). Its unit conclusion is unchanged, but those
expressions must not be read as literal frozen `HasCoordinate` formulas without
the shared sign adjustment. This packet preserves that old file unchanged.

**L4 — Common integral strict factor and actual stored coordinate: PROVED.**

Put Ω=w1∧w2. Under the canonical cohomological determinant identification,
write the SAME integral strict generator as

    e_str ↦ c Ω*,                 c ∈ K×.             (4)

There is no assertion c∈R×. By the two actual integral triangle determinant
isomorphisms define integral generators

    e_F^△ ↦ e_str ⊗ det(local F basis),
    e_S^△ ↦ e_str ⊗ det(local S basis).

The naturality square between each triangle determinant map and the exact
cohomology determinant map of L2 gives, over K,

    e_F^△ = c e_mat,F,        e_S^△ = c e_mat,S.       (5)

Here the left and right expressions are compared THROUGH that square. They
are not definitions of the actual tensor or coordinate. Indeed, (4) is a
statement only about the strict determinant line, the local top wedge is
unchanged, and the two triangles use the identical e_str and Ω*. Equation
(5) is thus the tensor product of (4) with the local determinant identity.
The actual tensors of L2 and their independently derived coordinates (2)
therefore satisfy

    u_F^△ = c⁻¹ u_mat,F,        u_S^△ = c⁻¹ u_mat,S.   (6)

If retained bases are e_F=αF e_F^△ and e_S=αS e_S^△, then αF,αS∈R×, since
both pairs are integral generators. Their stored actual coordinates are

    u_F = αF⁻¹ c⁻¹ u_mat,F,
    u_S = αS⁻¹ c⁻¹ u_mat,S.                           (7)

This is the requested actual-coordinate bridge. In the generic two-dimensional
matrix model, the inputs `huF` and `huS` can be supplied by L2/L3 for the matrix
coordinates and equation (7) then transports the result to the actual stored
coordinates. Supplying `HasCoordinate ... u_F` directly for the stored coordinate
would usually be FALSE when c or αF is nontrivial; the scale must be retained.

**L5 — Torsion is retained by c: PROVED as bookkeeping; checked explicitly.**

Every strict cohomology group disappearing after tensoring K still contributes
to the image (4) of its integral determinant generator. It is erased nowhere:
only the common scalar is canceled in comparing the two branches. As an
explicit diagnostic, add the same strict disk [R --d→ R] in degrees one and
two, d≠0, to the rank-two strict model. Its determinant cancellation sends its
integral generator to d, hence c becomes d c. The full boundary matrices have
a common leading block [d], whose lower adjugate block is d adj(D_U). Thus the
full tensor coordinate becomes u_mat,U/d on BOTH sides, exactly as (6).
When d is a nonunit, discarding this disk as an integral contractible disk
would give the wrong coordinates. Its common cancellation is still valid.

**L6 — Integral unit consequence: REUSED algebra with actual bridge.**

The frozen `unitRelated_scale_iff` cancels the common nonzero c⁻¹ without
assuming it is an integral unit. Integral αF,αS are separately unit changes.
Thus the stored actual coordinates are unit-related over the SAME R iff the
matrix coordinates are. The frozen integral-unit criterion then reduces this
to UnitRelated_R(qF,qS), since δ is the image of an integral unit.
This also allows both q's to vanish; independence, however, must then come
from a separate actual argument, not from zero cross values.

### 3) Main theorem

**Conditional actual determinant bridge: PROVED in ordinary mathematics under
the ledger above.** The actual coordinates satisfy (7). If the actual common
trace calculation establishes qS=-qF, formula (3) gives

    u_mat,S = δ u_mat,F,

and (6) gives the same equality in the triangle-induced integral bases.
Consequently the actual tensors agree under Φ_det in this fixed convention,
where Φ_det is identity on the strict factor and det J on the local factor.
An alternative consistent determinant convention contributes only its recorded
sign unit. In arbitrary retained integral bases the two coordinates differ by
an integral unit, and every valuation trivial on R× is equal on them.

The strict determinant scale has now been explicitly accounted for; it is not
a new arithmetic assumption of unit preservation. What remains open in this
packet is establishment of all actual arithmetic hypotheses: particularly the
shared-trace boundary–cup identity, orthogonal partner localization and
retained-limit coherence. Universal O[G] descent, where G is nontrivial and
O[G] has zero divisors, is also outside the K-vector-space theorem. Scalar
characterwise unit comparisons do not establish that universal claim.

### 4) If refuted: repaired statement

No counterexample to the theorem WITH its premises is claimed. Two tempting
stronger statements fail and are tested explicitly:

- Forgetting c gives incorrect actual coordinates when a common strict
  nonunit disk is present. Retain (6), with arbitrary c≠0.
- Rescaling only λB by 2 preserves all cycle/rank/closedness inputs but changes
  the dyadic coordinate valuation. The actual shared-trace normalization is
  indispensable; no determinant-only argument supplies it.

### 5) Verification plan for the verifier role

Independently rederive (1) from the two short exact sequences, check the
normal diag(0,1) sign, and verify naturality produces the SAME c, rather than
two arbitrary generic scales. Compare to source `HasCoordinate` and the
retained-basis definition. Check the degree-one/two disk contributes c=d.

`check_bridge.py` uses exact rational arithmetic, not floating point, and
checks the full adjugate equation for valid generated boundary models, changes
of complements/quotient lifts, divisible v with fractional complement, and
common nonunit disks. Negative controls rescale one functional, discard a
strict torsion factor, flip one frame sign, and set v=0. These checks test
the finite algebra and scope guards; they do not compute a global Galois cup
product or certify a retained-limit arithmetic theorem. A nonauthor review is
required before calling this source bridge independently accepted.
