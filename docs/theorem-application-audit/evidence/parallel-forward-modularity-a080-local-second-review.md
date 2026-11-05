# A080 local repair: independent second review

Reviewed 2026-11-05 against manuscript SHA256 a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e and theta-local/A080-LOCAL-REVIEW.md. This review follows A080-REPORT.md in this directory.

## Decision

Accept the revised derivative-place construction. It supplies a substantive local compatibility argument, rather than treating Nekovar 8.6.4 as a theorem that makes arbitrary local conditions functorial. The final revision supplies local integral comparison contractions by comparing the small free resolution with the continuous bar resolution. This review does not certify the separate global bounded-contraction, perfectness, or global exact-annihilator claims. The local repair must not be used to close those dependencies.

The operational claim must remain restricted to the actual split and totally ramified derivative extensions. An arbitrary tame subgroup need not have generators phi^f and tau^e: phi^f tau^c introduces a shear. The revised report and insertion now state this restriction correctly.

## Source interface

The inspected source is Nekovar, Selmer complexes, Asterisque 310 (2006), pinned PDF work/nekovar-selmer-complexes-2006.pdf, SHA256 61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f. Printed pp.222 through 224, sections 8.6.2.1 through 8.6.2.4, require local maps, comparison homotopies and the indicated coherent cubes. Printed pp.224 through 226, section 8.6.4, consumes that data. Sections 8.1.4 through 8.1.7, printed pp.191 through 200, supply the full cochain transfer, comparison and local decomposition constructions. These source statements do not themselves prove that the bespoke finite/singular subcomplexes are preserved.

The explicit tame-model, shear and degree computations below are mathematical checks of the repair. They are not quotations from those pages. No new source was downloaded for this second review.

## Local arithmetic and the model

H12 gives Phi=rho(Fr_ell)^2=1 modulo 2^(a+1), and ell=-1 modulo 2^(a+1). For a>=0, ell^2-1 has valuation at least a+2, so q=ell^2=1 modulo 2^(a+2). At retained m<=a, the unramified representation is trivial. The moving character is locally trivial because the old ring-class extension splits here. This last condition is needed for the binary coefficient version as well.

For arithmetic Frobenius with phi tau phi^-1=tau^q, the relation derivatives are 1-tau^q and phi-(1+tau+...+tau^(q-1)). On an unramified module they give d0=((Phi-1),0) and d1(x,y)=(Phi-q)y. Thus the proposed complex is zero at the retained precision, with free terms in degrees 0,1,2. There is no switch to geometric Frobenius in this computation.

The description via the two length-one resolutions of Z_2 supplies the usual mapping-cone resolution for the semidirect product. To obtain actual comparison contractions with the continuous bar complex, one must compare these resolutions in the appropriate completed module category, or invoke the already retained integral contractions. Merely identifying the cohomology groups with free modules would not by itself justify a chosen contraction. The proposal expressly retains the latter dependency; preserve that qualification when integrating it.

## Singular square and choice of lift

Since q=1 modulo 2^(m+1), the local field contains mu_(2^(m+1)); consequently -1 is a 2^m-th power. The norm relation for a 2^m-th root of a uniformizer gives (pi,-pi)=0 and hence (pi,pi)=0. This proves the needed square vanishing at two; alternating-sign formalism alone would not.

After choosing phi upstairs, specify a uniformizer adjusted by a unit so its Kummer character evaluates to zero on phi. Unit Kummer classes give the unramified character and their evaluation at phi is surjective onto Z/2^m, so this adjustment is possible. Its inertia coordinate is unchanged. Equivalently, use the Kummer class spanning the chosen singular coordinate, not an arbitrary fixed uniformizer without adjustment. The square remains zero for the adjusted uniformizer. The finite plane has zero self-cup by unramified cohomological dimension one. Mixed duality and D0/D2 duality then give the stated annihilators with the manuscript's transported coefficient pairing.

## Maps and integral factors

For the actual new derivative extension f=1 and e=ell+1; choosing phi in the upper subgroup is possible since inertia surjects onto its totally ramified quotient. Use tau'=tau^e. The old split terms have e=f=1. With these choices restriction is diag(1,f,e,ef) and corestriction diag(ef,e,f,1). Degree one follows from evaluation and group transfer, while degree two follows from inv_upper(res c)=ef inv_lower(c) and inv_lower(cor c)=inv_upper(c). The degree-zero norm is ef, not an average.

For cosets tau^j the extra inertia exponent in transfer of phi is sum floor(qj/e). Because multiplication by q permutes residues modulo e, this sum equals (q-1)(e-1)/2. The retained q congruence annihilates it modulo 2^m even when e is even. The formula therefore uses a verified divisibility by two, not inversion of two in coefficients. The corresponding unramified sum is 1+q+...+q^(f-1)=f modulo 2^m. All displayed res/cor products are ef. Their pairwise adjunctions match D0/D2 and finite/singular duality. Coefficient transport and scalar weights commute with the entries.

## Cochain and cube check

Write 1-i_v p_v=d h_v+h_v d and use nonnegative cochain models. For a chain map F:v->w put F_L=p_w F i_v. The formula H_F=h_w F i_v restricted to U gives

F i_v-i_w F_L=d H_F+H_F d.

For F:v->w and G:w->z put K(G,F)=p_z G h_w F i_v. Direct substitution gives

(GF)_L-G_L F_L=d K(G,F)+K(G,F)d.

Every degree-minus-one map from U, concentrated in degrees 0 and 1, into the nonnegative local model lands in D0. Since every derivative condition retains all D0, K restricts to the target U. This is the precise reason the homotopies preserve these conditions.

There is also an explicit triple identity. For H:z->t put L(H,G,F)=p_t H h_z G h_w F i_v. Expansion of 1-ip gives

K(H,GF)-K(HG,F)+H_L K(G,F)-K(H,G)F_L=L(H,G,F)d-dL(H,G,F).

The degree-minus-two map L vanishes on U. Thus the transferred associativity boundary is zero there, not an unexamined obstruction in negative degree. When a square of original bar maps commutes only up to a specified homotopy, transfer that original homotopy as well. Its source comparison cubes from Nekovar 8.1 must be retained; one cannot choose unrelated boundaries for individual arithmetic classes. The same degree argument then restricts the resulting data. No division by a group order occurs in these formulas.

For a dual pair U,U', their tensor product is bounded free in degrees 0,1,2. With the trace target A[-2], the internal Hom complex has no negative-degree terms. Therefore H^-1 of this Hom complex is zero. Once the transported restricted pairing is zero, a difference between two full-model nullhomotopies is a boundary, giving the required next homotopy. This conclusion uses a free model and the correct trace target. It is not a statement that arbitrary pairings or arbitrary local subcomplexes have coherent isotropy automatically.

## Suggested additions to the insertion

Add after the choice of compatible Frobenius:

"Choose the uniformizer representing the singular Kummer coordinate after this choice of Frobenius, adjusting it by a unit so its Kummer character is zero on that Frobenius."

Add after the contraction formulas:

"These constructions use the retained integral comparison contractions. Their existence and compatibility are the bounded-model dependency, not a consequence of equality of local cohomology dimensions. For three composable maps the associativity boundary is Ld-dL, where L=pHhGhFi; this degree-minus-two map vanishes on every derivative U. Original bar comparison homotopies and cubes are transferred along with the maps."

The repair's old Kummer, unramified, full and zero conditions use their separate natural models. The diagonal derivative matrices must not replace those maps. Their underlying Kummer-duality and bounded-model existence claims remain dependencies as stated in the first review.

## Check of the final revision

The author incorporated the adapted uniformizer and replaced the assumed local contraction by comparison of the small free resolution with the continuous bar resolution. Projectivity gives augmentation-preserving maps and homotopies in both directions, degree by degree. Applying continuous Hom preserves the identities. The composite on the zero-differential small cochain model is exactly its identity because it is homotopic to that identity. Thus p i=1, and the other composite has the required homotopy. This is a valid local construction and removes the conditional local-contraction qualification in the initial review. It still does not prove global uniform bounded contractions or other claims about limits.

The suggested explicit triple identity above remains useful supporting detail. The earlier conditional comments identify what the final resolution-comparison paragraph now supplies; they are not a remaining objection to this revised local repair.
