# A080 local-interface review and proposed construction

Scope: the local-condition requirements in Nekovar 8.6.2.1–8.6.2.4 that precede 8.6.4, for the actual coefficient push and finite/singular conditions in the a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e manuscript. I coordinated with forward-modularity, which checked the global transfer formula. No shared files were edited.

## Finding

The current sentences H19 and H22 do not by themselves establish the local morphisms, homotopies and coherent cubes required by 8.6.2. They establish equality of particular degree-one classes and witnesses for those classes. A repair should construct the local functorial diagrams first, then place those classes in the diagrams. Merely changing the source citation to 8.6.4 would leave this gap.

There is a concrete construction for the present local conditions. It depends essentially on three hypotheses that the manuscript already states: H12 retains one extra factor of two; every derivative condition retains D^0; all Frobenius/inertia choices are transported together. Below I derive the local maps and give the homotopy construction. The revised construction supplies the local interface rather than assuming it and has now passed the independent second review. The final section contains insertion text. The revised local construction was independently accepted in forward-modularity/A080-LOCAL-SECOND-REVIEW.md; its final-revision section removes the initial local-contraction qualification.

This review does not independently certify global perfectness or bounded contractions, uniform ranks, the two ultrafilter limits, the Selmer exact-annihilator theorem, or the arithmetic derivation of H19. Those remain separate dependencies.

## Source requirements and consumer map

I read Nekovar's extracted printed pp.222–226 from forward-modularity/primary/nek-p222.txt through nek-p226.txt. Section 8.6.2 asks for local Shapiro and transport maps, local restriction/corestriction, comparison homotopies with the full local cochains, and 2-homotopies trivializing the indicated cube boundaries. Section 8.6.4 constructs global Selmer maps from that supplied data; it does not supply arbitrary local-condition compatibility for free.

Manuscript consumers: H20–H22, lines 3042–3156; local Kummer construction, lines 3164–3208; finite-model transport, lines 4123–4174; derivative conditions, lines 4566–4614; and the later orthogonal comparison, lines 4896–4907. H12, lines 2930–2940, supplies the extra precision needed below. At old places the moving character is trivial and the binary local type is fixed. At derivative places the coefficient character is locally trivial and H_f/K splits completely. These are used, not replaced by a generic assertion about Selmer complexes.

## Explicit derivative local complex

Fix retained exponent m and derivative prime ell; let q=ell^2 be the residue cardinality of K_v. Choose m<=a and the H12 congruence rho_T(Fr_ell)=J modulo 2^(a+1), J^2=1, det J=-1. Thus the local coefficient action Phi=rho_T(Fr_ell^2) is 1 modulo 2^(a+1), and ell=-1 modulo 2^(a+1). In particular q=1 modulo 2^(a+2). The moving coefficient character is trivial at v. For M=(T/2^m) tensor A, or its binary version, both inertia and Phi act trivially.

The pro-2 tame local calculation has generators phi,tau, with phi tau phi^-1=tau^q. The wild pro-ell group contributes no positive cohomology on 2-primary coefficients. The standard two-generator resolution, evaluated on an unramified M, is

L(M)=[ M -> M_phi direct-sum M_tau -> M ],
d^0(t)=((Phi-1)t,0), d^1(x,y)=(Phi-q)y.

The resolution is obtained by combining the length-one completed group-ring resolutions of the tame Z_2 kernel and the unramified Z_2 quotient; each is the exact sequence defined by multiplication by its generator minus one. The semidirect action inserts the q term. Thus this is a resolution calculation, not an inference that a complex with the right cohomology dimensions must be quasi-isomorphic. The differential formula also follows directly by differentiating the relation in the group ring: its coefficients are 1-tau^q and phi-(1+tau+...+tau^(q-1)). At the retained coefficients the two differentials are zero. These are D^0, F direct-sum S, D^2 in degrees 0,1,2. The coefficient module is free over the finite coefficient ring, so this is an actual free zero-differential model, not merely a decomposition of abstract cohomology groups. All assertions are at finite retained precision; a fixed arithmetic ell is not claimed to satisfy the congruence integrally at arbitrary precision.

The finite coordinate is evaluation at the chosen phi and the singular coordinate at the chosen tau, with the manuscript's Tate-basis and conjugate-duality transports retained. A change phi -> tau^b phi shears the coordinates, sending finite evaluation to f+b s. Therefore the singular plane is not independent of the Frobenius lift. The repair must specify compatible lifts, as below, rather than claim it is canonical under arbitrary choices.

## Pairing and the extra factor of two

The finite plane is isotropic because its classes inflate from the procyclic unramified quotient of cohomological dimension one. The singular plane can be represented using the Kummer class of a uniformizer adjusted to the chosen phi, since mu_(2^m) is present. An arbitrary uniformizer need not have Kummer value zero on that phi. Multiply it by a unit whose unramified Kummer value cancels that value; the residue-unit Kummer characters realize every value in Z/2^m because q-1 is divisible by 2^m. The adjusted element is still a uniformizer and now represents S. Its self-cup vanishes here for a stronger reason than skew-commutativity: q=1 modulo 2^(m+1) makes -1 a 2^m-th power in the local field. The norm of a 2^m-th root of a uniformizer is minus that uniformizer; the norm/cup relation gives (pi,-pi)=0, and bilinearity then gives (pi,pi)=0. Thus the singular square vanishes even at 2. This would not follow from an assertion that 2 times the square is zero.

The mixed finite/singular cup is the usual perfect tame local pairing. D^0 pairs with D^2. Transporting the Tate pairing and the conjugate identification gives the manuscript's displayed unit and J factors. This review does not replace that transported pairing by an untransported symplectic form. Once transported, the four inclusions D^0; D^0+F[-1]; D^0+S[-1]; D^0+(F+S)[-1] have the asserted strict/relaxed and self-orthogonal descriptions. Their restricted trace pairings vanish where isotropy is asserted.

## Restriction and corestriction matrices

For the actual derivative diagram, all old ring-class fields split at ell, and the new conductor-ell extension is totally ramified. Thus its residue degree is f=1. Choose phi in the upper subgroup first; this is possible because inertia surjects onto the ramified Galois quotient. Take tau'=tau^e. At split places e=f=1 and the matrices are the identity on each component. Transport these generators, the Tate basis and the local condition together at conjugate places. The general e,f formulas below are valid when compatible generators phi'=phi^f and tau'=tau^e have been chosen; they are not an assertion that every tame subgroup has that form. A subgroup generated by phi^f tau^c would require the corresponding shear. Only the split and f=1 cases are needed here.

In the zero models, restriction and corestriction are respectively

res=diag(1,f,e,ef),
cor=diag(ef,e,f,1),

in the order D^0,F,S,D^2, with any coefficient transport on all entries. These are maps of the full local complexes and restrict to all four U's. The degree-zero entries are invariants and norm; degree-one entries follow by evaluating cocycles on phi^f and tau^e and by group transfer; degree-two entries are fixed by the local invariant map. Their products equal multiplication by ef.

There is a possible transfer shear before imposing the extra congruence. In a totally ramified Galois tame extension, transfer of phi has an inertia exponent proportional to (q-1)(e-1)/2 after writing the result in terms of tau'. This is zero modulo 2^m because q-1 is divisible by 2^(m+1). More explicitly, coset representatives tau^j give the upper inertia exponent sum_{j=0}^{e-1} floor(qj/e)=(q-1)(e-1)/2; the residues qj modulo e are a permutation of 0,...,e-1. The sum 1+q+...+q^(f-1) in transfer of inertia is f modulo 2^m. Hence the displayed diagonal maps are correct at the retained precision, including the even ramification degrees used here. Keeping only q=1 modulo 2^m and ignoring the division by two would not justify the shear cancellation.

For the concrete H19 upper extension e=ell+1, f=1. For the H20 Mackey terms at derivative primes H_f/K is split, so e=f=1 after transporting each place. Coefficient reduction and the scalar weights in H20 commute with every displayed entry. These observations explain precisely why the finite/singular conditions survive that coefficient push.

The matrices also satisfy adjunction under the full local pairing: res in D^0 is adjoint to cor in D^2; res on F multiplies by f while cor on S multiplies by f; res on S multiplies by e while cor on F multiplies by e. Thus the local projection formulas hold in the transported models. For arbitrary changes of Frobenius the displayed diagonal matrices must be conjugated by the corresponding shear and the U's transported as well.

## Actual comparison homotopies, not just H^1 preservation

Compare the small completed-group-ring free resolution with the continuous bar resolution using augmentation-preserving comparison maps. Projectivity supplies maps in both directions and the usual degree-by-degree lifts give chain homotopies for their composites. Applying continuous Hom into the finite coefficient module retains these homotopy identities. The bounded model has zero differential here, so a self-map homotopic to its identity is its identity; the comparison maps therefore give p_v i_v=1. Normalizing the remaining homotopy gives a contraction. Choose these comparisons once for the finite diagram, with 1-i_v p_v=d h_v+h_v d. This is a local resolution construction; it does not assume the manuscript's broader bounded-global-model claim. Use the same coset representatives as the global bar-cochain Shapiro and transfer maps. For an actual cochain arrow F:C_v->C_w set F_L=p_w F i_v. This is the displayed full matrix because the zero models identify maps with their action on cohomology. Its restriction to a chosen U is the local-condition arrow F_U.

The local inclusion square has explicit homotopy

H_F=h_w F i_v|_U,
F i_v|_U-i_w F_U=d H_F+H_F d.

For two composable arrows F,G, the difference between the transferred composite and the composite transferred maps is homotopic through

K_(G,F)=p_z G h_w F i_v,
(GF)_L-G_L F_L=d K_(G,F)+K_(G,F)d,

with the corresponding terms for any already chosen bar-cochain comparison homotopy. The direction of the equality fixes the sign convention.

Crucially, every U here is free and concentrated in degrees 0 and 1, and contains all of D^0. Consequently any degree-minus-one K restricted to U lands in D^0 and is automatically a map into U. Thus the composition homotopies needed by the local diagrams restrict as well. If D^0 had been discarded, this argument would fail. Higher transferred terms such as p H h G h F i have degree minus two and vanish on these U's, or give their prescribed full-cochain counterparts before restriction. The contraction identity gives the required cube identities; one must transfer the whole finite diagram, not choose independent classwise boundaries.

For the isotropy/projection-formula diagrams, the relevant source U tensor U' is a bounded free complex in degrees 0 through 2. The trace target is A[-2]. The Hom complex has no negative-degree terms, hence Hom_D(U tensor U',A[-2][-1])=0. Once the restricted pairing is zero, any two null-homotopies after returning to full cochains differ by a null-homotopic cycle; this supplies the required next homotopy. In the bounded trace model the isotropy map is literally zero. This is the degree argument justifying 2-homotopy coherence, not the unqualified claim that equality on H^1 provides it.

For general coset changes one uses the usual bar-cochain homotopies already retained in Nekovar 8.1 and 8.6, then applies the same formulas. The degree-minus-one restriction argument still applies, and the zero negative Hom group controls the cup/isotropy coherence. No averaging or division by 2, e, f or a group order is used.

## Other local conditions

At old Kummer places use the derived Kummer map from the actual local group, including torsion. Its finite free resolution is concentrated in degrees 0 and 1: resolve the finitely generated Z_2-module B(F)^completion and shift by -1, then use the stated derived scalar extension. Restriction is the point inclusion and corestriction is the point norm; their Kummer diagrams follow from the multiplication-by-2^m exact sequences and are compatible in every degree, not merely after dropping local torsion. The finite local duality projection formula identifies their adjoints. The same bounded-degree negative-Hom argument supplies the coherence for isotropy homotopies. The common local twist and locally trivial moving character are necessary to use this diagram for the scalar/binary coefficient push.

At unconstrained full or zero conditions the local arrows are the full cochain arrows or the unique zero arrows. At good unramified conditions the subcomplex is the unramified two-term complex [M^I -> M^I] in degrees 0,1. In the present coefficient-push uses these places remain unramified; restriction/norm are the procyclic maps and commute with the inclusions into full cochains. New ramified supports are not quietly treated by this assertion: their conditions are explicitly full or are the derivative diagrams constructed above.

H22 may now be used to select the actual arithmetic cycles and their degree-zero comparison witnesses inside this coherent finite diagram. It is not the construction of the diagram. The later finite-model contraction argument transports this data; it cannot repair absent initial local maps on its own.

## Proposed insertion before paragraph 8

The following insertion is intended to replace the current implicit local-functoriality assertion. It is the substantive local repair accepted by the independent second review, with the explicit triple identity added.

```tex
\paragraph{The local diagrams underlying the coefficient push.}
At a retained derivative place put $q=\ell^2$ and choose tame
and unramified generators $\tau_v,\phi_v$ with
$\phi_v\tau_v\phi_v^{-1}=\tau_v^q$. The local coefficient
character is trivial. The two-generator tame resolution is
\[
 [M\xrightarrow{u\mapsto((\Phi_v-1)u,0)}M\oplus M
       \xrightarrow{(x,y)\mapsto(\Phi_v-q)y}M],
 \qquad \Phi_v=\rho(\phi_v).
\]
At the retained exponent $m\le a$, (H12) makes this the
zero-differential model $D^0\oplus(F_v\oplus S_v)[-1]
\oplus D^2[-2]$. Moreover $q\equiv1\pmod{2^{a+2}}$.
Represent the singular generator by a uniformizer adjusted by
a unit so its Kummer value on the chosen $\phi_v$ is zero.
Residue-unit Kummer characters allow this adjustment. The latter
congruence makes its self-cup zero: $-1$ is a $2^m$-th power,
so the adjusted uniformizer Kummer class has square zero. The finite self-cup is zero by unramified cohomological
dimension one. Retain the transported mixed pairing and the
$D^0,D^2$ pairing.

In the derivative diagram the old ring-class fields split
locally, and the new conductor extension is totally ramified.
For the latter choose the lower Frobenius in the upper subgroup
and take $\tau_{\rm upper}=\tau_{\rm lower}^e$; here $f=1$.
For split terms $e=f=1$. Transport these choices with the Tate
basis. With these compatible generators the local matrices, in the order
$D^0,F_v,S_v,D^2$, are
\[
 \operatorname{res}=\operatorname{diag}(1,f,e,ef),\qquad
 \operatorname{cor}=\operatorname{diag}(ef,e,f,1).
\]
The possible transfer shear is divisible by $(q-1)/2$ and
vanishes at retained precision. These matrices preserve each
of the four conditions retaining $D^0$, and satisfy the local
cup-product adjunctions. Split Mackey terms have $e=f=1$;
coefficient weights and reduction commute with these matrices.
An arbitrary new Frobenius lift is not used without transporting
the resulting finite/singular decomposition.

Compare the small free resolution with the continuous bar
resolution and choose augmentation-preserving comparison maps
and their composite homotopies. Continuous Hom into $M$ retains
these identities. Since the small model has zero differential,
the composite on it is the identity; normalize the other homotopy
to obtain a contraction. Here are its compatibility maps.
For this retained contraction $1-i_vp_v=dh_v+h_vd$ and a full
local cochain arrow $F$, take $F_L=p_wFi_v$ and restrict it to
$U_v$. The inclusion square has homotopy $h_wFi_v|_{U_v}$.
For composable arrows the transferred composition homotopy is
$p_zGh_wFi_v$, together with the transferred original bar
homotopy when present. Every such degree-minus-one map on
$U_v$ lands in $D^0$, which is retained in every condition;
thus these homotopies restrict too. For three composable maps,
write $K(G,F)=pGhFi$ and $L(H,G,F)=pHhGhFi$, with the
intermediate subscripts understood. Direct expansion gives
\[
 K(H,GF)-K(HG,F)+H_LK(G,F)-K(H,G)F_L=Ld-dL.
\]
The degree-minus-two map $L$ vanishes on every derivative
condition. Transfer the original bar comparison homotopies and
cubes as well; unrelated classwise boundaries are not substituted
for them. For the isotropy diagrams, $U_v\otimes U'_v$ is
free in degrees $0,1,2$, whereas the trace target is $A[-2]$.
Its negative Hom groups vanish, so the restricted zero pairing
has compatible null-homotopies and the requisite 2-homotopies.
This constructs the local data required in
\cite[8.6.2.1--8.6.2.4]{nekovar} before using 8.6.4.
At old Kummer places use the natural restriction/norm diagrams
of the multiplication-by-$2^m$ exact sequences, including
local torsion, and their derived scalar extensions; at good
unramified, full and zero places use the corresponding standard
subcomplexes. The witnesses in (H22) are chosen in these same
diagrams.
```
