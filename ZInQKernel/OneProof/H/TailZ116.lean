import ZInQKernel.OneProof.H.TailZ115
import ZInQKernel.Contrib.OneProof.DelignePrintShapedMilne.Bridges

/-! # OneProof H, y3-milne-1128: `sixContactMin_of_open109` (skip-generation fold onto `OpenResearchLeaves83CMJ`)

The new generation `OpenResearchLeaves87` is built from `OpenResearchLeaves83CMJ`, the bundle of the `cmjDegreePrint` reroute's copy chain
that still has `deligneCanonicalModelY3EveryPrint` as a field. The conversion fills it by
`DelignePSMilne.deligneCanonicalModelY3EveryPrint_of_milne` from `voightQMComplexModuliPrint`, `boutotCarayolPolarizationPrint`, `boutotCarayolRepresentabilityPrint`, `milneShimuraFamilyPrint`, `milneCanonicalModelPrint`.
Against the previous top `OpenResearchLeaves86`, `cornutVatsalCMReciprocityPrint` and `fineModuliCanonicalModelGlue` leave and
`boutotCarayolPolarizationPrint`, `boutotCarayolRepresentabilityPrint`, `milneShimuraFamilyPrint`, `milneCanonicalModelPrint` enter. The fields `cmHeight62`, proved since, are filled by their proofs. The previous generations stay imported as history. -/

namespace HDec

namespace HSyn

/-- `OpenResearchLeaves83CMJ` without `deligneCanonicalModelY3EveryPrint`, `cmHeight62`, with the fields `voightQMComplexModuliPrint`, `boutotCarayolPolarizationPrint`, `boutotCarayolRepresentabilityPrint`, `milneShimuraFamilyPrint`, `milneCanonicalModelPrint` (y3-milne-1128). -/
structure OpenResearchLeaves87 : Prop where
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1),
  pp. 513-514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an
  eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N
  1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified
  outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) =
  eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma,
  TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- r16-det: Diamond-Shurman Thm 9.6.5 at k = 2 for the Section 9.5 realization on A_f, over
  K_{f,lambda}, universal over A_f. For every (A, pi, theta) that is DS's A_f (afShimura's
  characterization, for any X, generators, P0, Jacobian and Hecke operators as in heckeJ1DS), every
  prime l and every place lambda | l of K_f: for p not dividing N l every arithmetic Frobenius sigma
  at p acting on V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) (rho_{f,lambda}, DS Exercise 9.5.2(a))
  has characteristic polynomial X^2 - a_p X + chi(p) p over K_lambda. Statement = aftate-fix2's
  AfTateLam.AfTateDSLambda verbatim (AfTateLam.afCharpolyDS965_iff, Iff.rfl); it implies r16-close's
  glue AfDetLambda (AfTateLam.afDetLambda_of_ds965). -/
  afCharpolyDS965 : _root_.AfTateLam.AfCharpolyDS965
  /-- R13, printed existence form over a finite coefficient field (htnew-assembly): for a prime l,
  embeddings iota_C, iota_L and a Tau Ceti newform f of weight k >= 2 and level N (every level, l |
  N included), there are a finite extension E of Q_l inside Qbar_l (the print's K_{f,lambda} /
  Kato's F_lambda, embedded) and a continuous rho : G_Q -> GL_2(E), unramified outside N l, with
  either (arithmetic Frobenius trace a_p and Hodge-Tate weights {0, k-1}, cyclotomic weight +1) or
  (geometric Frobenius trace a_p and Hodge-Tate weights {0, k-1}, cyclotomic weight -1), the
  multiplicity of w being dim_E (V tensor_{Q_l} C_l(-+w))^{G_{Q_l}} (Mathlib tensor product, the
  print's definition). Replaces modularHTPrinted: the assembly lemma dim_E (V tensor C_l(w))^G =
  htMult(rho dual, -w) (trace-form isomorphism V tensor C_l = Hom(E^n, C_l)), HTDual and the
  coefficient extension E in Qbar_l are proved in Lean (ModularHTCoeff.lean). -/
  modularHTCoeff : _root_.HTNewAssembly.ModularHTCoeff
  /-- jp-an-retype: Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1 (h_Fal(X) <= 13*10^6 *
  g * deg_B(X)^5 for a smooth projective connected curve X/Qbar of genus g >= 1) composed with
  Section 2.3 (h_Fal(X) = stable Faltings height of Jac X), as the manuscript cites it at
  diophantine_zq.tex L870 (applied to J = J_1(N)). JavanpeykarDirect.JavanpeykarThm111 verbatim with
  IsStableHeightBar replaced by IsStableHeightBarAn: the stable height of a model over a number
  field L of the Jacobian W, read as IsAnStableHeightSS (archimedean metric (i/2)^g int eta~ wedge
  eta~-bar on the complex manifold A_tau(C)^an, densities in every holomorphic chart, r3-residual;
  semistability: semi-abelian reduction of the Jacobian's Neron model, IsSemistablePrinted,
  semistab-assembly; not the print's curve-model semistability, Def. 2.2.1). Replaces
  javanpeykarThm111 (JavanpeykarAnRetype.javanpeykarThm111_of_an, with mumfordTorsionAlgClosed and
  uniformizationLeafAll_proof for T35); the converse javanpeykarThm111An_of_thm111 holds given T35,
  so the leaf is not stronger than the row it replaces. -/
  javanpeykarThm111An : _root_.JavanpeykarAnRetype.JavanpeykarThm111An
  /-- carirr-refold, consequence of Darmon-Diamond-Taylor 1997 Thm 3.1 (proved:
  CarayolRefold.frob_of_DDT31 from carirr-odd's transcription CarayolDDT.CarayolDDT31), with the
  Frobenius clause in the normalization the manuscript reads off Carayol 1986 Theoreme (A)
  (diophantine_zq.tex L9784-9796): for a printed newform f (Tau Ceti Newform N 2, psi = f.chi) with
  number field K_f and a place lambda | l, a continuous rho : G_Q -> GL_2(K_{f,lambda}) that is
  irreducible (Ribet 1977), unramified at p not dividing N l with arithmetic Frobenius of trace a_p
  and determinant p psi(p) (polynomial X^2 - a_p X + p psi(p)), and with codim V^{I_p} +
  integral_0^infty codim V^{G_p^u} du = v_p(N) at every p != l (Carayol Thm A + conductor of local
  Langlands + Casselman 1973 Thm 1; packaged in DDT 3.1). Oddness is proved from the Frobenius
  determinant (CarayolRefold.odd_of_frobDet, one Chebotarev element). Carayol's own form
  (sigma_lambda(pi)|G_{Q_p} <-> pi_p under local Langlands) has no Lean form (no pi_{f,p},
  Weil-Deligne representations or local Langlands in Lean). Replaces carayolThmAIrr. -/
  carayolThmAFrob : _root_.CarayolRefold.CarayolThmAFrob
  /-- Fowler, Proposition 2·7: for an imaginary quadratic order discriminant Δ < 0 congruent to 0 or
  1 modulo 4 and positive n, h(Δ) ≤ n implies √|Δ| ≤ 2n² exp(21000n²), with h(Δ) the proper ideal
  class number of the unique order of discriminant Δ. -/
  fowlerProp27PrintCanonical : HDec.CMBranch.FowlerBridges.FowlerProp27PrintCanonical
  /-- Grothendieck's semistable reduction theorem as stated in Silverberg-Zarhin, Ann. Inst. Fourier
  45 (1995), Theorem 3.4, pp. 405-406 (proof: SGA 7 I, Exp. IX, Th. 3.6, p. 351): for an abelian
  variety A over a field K with a discrete valuation ring O, one finite Galois extension E of K
  inside an algebraic closure such that A_E has semistable reduction (HasSemistableReductionSZ,
  which also asserts a Neron model) at every prolongation of O to E. Replaces silverbergZarhinThm35
  (Raynaud's criterion), which SZRaynaud.silverbergZarhinThm35_of_sz34 proves from it with the
  proved Theorem 3.3. -/
  silverbergZarhinThm34 : _root_.SZRaynaud.SilverbergZarhinThm34
  /-- Berger's p-adic monodromy theorem, Invent. Math. 148 (2002), 219-284, as cited by the
  manuscript (bibitem berger2002; Théorème 0.7 = Corollaire 5.22 in the author copy, Théorème 0.6 =
  Théorème 5.19 of arXiv:math/0102179v3; journal locator UNVERIFIED): every de Rham representation
  of G_{Q_p} is potentially semistable, here in Fontaine's dimension form over BstFOf (Astérisque
  223 (1994), Exp. III, 1.8.5 and 5.6.1; Exp. II, 4.2.4-4.2.5). Colmez, Astérisque 319 (2008),
  Théorème 0.1, prints the basis form, which implies this field
  (PanBergerRefereed.bergerSurveyF_of_colmez); the converse needs the G_K-regularity of B_st, which
  is not proved, so ColmezThm01 is not a replacement at the same count. -/
  bergerSurveyF : _root_.HDec.PkgI4.PanDict.BergerSurveyF
  /-- Pan, The Fontaine-Mazur conjecture in the residually reducible case, Theorem 1.0.4 with
  Conjecture 1.0.1, read in arXiv:1901.07166v2 (pp. 5 and 2), the version the manuscript cites;
  published in J. Amer. Math. Soc. 35 (2022), whose numbering is unchecked. Here p >= 5, with
  potential semistability in Fontaine's sense (Astérisque 223 (1994), Exp. III, 5.6.1, in the
  equivalent form of 1.8.5). Same statement as the replaced panPrintedF, token for token; only the
  source of the definitions changes from Brinon-Conrad's notes to Fontaine's exposés;
  panPrintedF_of_thm104F. -/
  panThm104F : _root_.HDec.PkgI4.PanBergerRefereed.PanThm104F
  /-- item-m-fold: Gaudron-Rémond (GR1), Théorème des périodes et degrés minimaux d'isogénies,
  Comment. Math. Helv. 89 (2014), 343-403, Cor. 8.4, p. 400 (attribution: Bost), h(A) >= -(1/2)(dim
  A) log(2 pi), read in Faltings' original normalization h_F(A) = h(A) - (g/2) log pi (p. 352) and
  weakened to h_F(A) >= -(3/2) dim A, the weakening Gaudron and Rémond make on p. 352; Lean proves
  the weak form from the print (ZInQ.HeightModelM.gaudronRemondSec9LowerGR1Weak_of_GR1). The height
  is that of a semi-abelian model (GR1 section 2.3, p. 351;
  ZInQ.HeightModelM.IsGR1StableHeightOriginal). Replaces gaudronRemondSec9LowerAnSS, which
  ZInQ.HeightModelM.gaudronRemondSec9LowerAnSS_of_GR1Weak proves from it and egaIV_9_7_7_OL; the
  converse (from the GR1 height to the Néron-model height) is not proved in the tree. -/
  gaudronRemondSec9LowerGR1Weak : _root_.ZInQ.HeightModelM.GaudronRemondSec9LowerGR1Weak
  /-- item-m-fold: Gaudron-Rémond, Polarisations et isogénies, Duke Math. J. 163 (2014), 2057-2108,
  Thm 1.4, p. 2060, with g >= 1 and κ(A) as on p. 2058 and isogenies "surjectif de noyau fini", the
  degree being the order of the kernel (p. 2062); read in Duke's version of record (the footer of
  p. 2057 gives Vol. 163, No. 11, DOI 10.1215/00127094-2782528, and the pages run 2057-2108; see
  docs/research/duke163-version-of-record.md). The height is the h_F
  of a semi-abelian model of GR1 section 2.3, to which Duke p. 2058 refers
  (ZInQ.HeightModelM.IsGR1StableHeightOriginal). As in the replaced field, one number field K
  carries A, B and the isogenies (K = k), and the printed couple is split into two isogenies of
  degree at most κ. Replaces gaudronRemondThm14Printed, which
  ZInQ.HeightModelM.gaudronRemondThm14Printed_of_GR1 proves from it and egaIV_9_7_7_OL; the converse
  (from the GR1 height to the Néron-model height) is not proved in the tree. -/
  gaudronRemondThm14GR1 : _root_.ZInQ.HeightModelM.GaudronRemondThm14GR1
  /-- item-m-fold: EGA IV₃, Publ. Math. IHÉS 28 (1966), Théorème (9.7.7)(ii), p. 79: for a morphism
  X → S of finite presentation, the set of points of S over which the fibre is geometrically
  connected is locally constructible in S. Here S = Spec 𝓞_L for a number field L and the morphism
  is smooth, quasi-compact and quasi-separated (finite presentation in the sense of EGA IV₁ (1.6.1),
  p. 234); geometric connectedness is preconnectedness of every base change of the fibre to a field
  (EGA IV₂ (4.5.1)-(4.5.2), p. 61, empty fibres included), and local constructibility is that of EGA
  0_III (9.1.1), (9.1.2) and (9.1.11), pp. 12-14. The proof uses it only through
  ZInQ.HeightModelM.isGR1StableHeightOriginal_of_isAnStableHeightSS: a height of a semistable Néron
  model is a GR1 height. -/
  egaIV_9_7_7_OL : _root_.ZInQ.HeightModelM.EGAIV_9_7_7_OL
  /-- y3-printed, Buzzard, Duke Math. J. 87 (1997) Thm 2.1 and Cor. 2.3 at U = V1(5), where M_U d
    = 30 (author's preprint: Thm 2.1 p. 5, Cor. 2.3 p. 7), with Buzzard's own definitions: full
    level-5 structures as O-linear isomorphisms (O/5O)_T -> A[5]_T of T-schemes (Def. 1.1, p. 3),
    the left action alpha -> alpha o r_delta, H = kappa^-1{(a b; 0 1)} in (O/5O)^x for a fixed
    kappa (Y3Buzzard.XDV15.kappa5), level structures as sections over S of the etale
    sheafification on S-schemes of T -> H\F_{A/S,5}(T) (p. 4, Def. 1.2), and the morphisms of
    X^D(U) (p. 5): a proper smooth curve X over Z[1/30] with a closed immersion into some P^N over
    Z[1/30], and an FEC (Buzzard's false elliptic curve: an abelian scheme of relative dimension 2
    with a ring homomorphism iota : O -> End) over X with a level-V1(5) structure, universal over
    every Z[1/30]-scheme S (exactly one g : S -> X admits a morphism, and that morphism is
    unique). 'Algebraic stack' and 'regular' dropped; projective over the affine base as the
    closed immersion (EGA II (5.5.4)(ii)); comparison maps are homomorphisms by Milne 1986 Cor.
    20.2(a). Gives buzzardThm21Cor23V15 (proved: Y3Buzzard.b1Prime_of_literal, with
    milneProp207At5 and Y3Buzzard.geomCard5_of_rem84). One of the eight rows that replace
    y3FullThreeRepZ30 (Y3Buzzard.y3FullThreeRepZ30_of_printed_xdv15). -/
  buzzardXDV15Lit : _root_.Y3Buzzard.XDV15.BuzzardXDV15Lit
  /-- y3-printed, Milne, Abelian varieties, in Cornell-Silverman (eds.), Arithmetic Geometry
    (Springer 1986), Prop. 20.7 at g = 2, n = 3 (p. 44 of the author's retyped edition): for an
    FEC (Buzzard's false elliptic curve: an abelian scheme of relative dimension 2 with a ring
    homomorphism iota : O -> End; injectivity of iota is automatic over a nonempty base, README
    B-1) over a Z[1/30]-scheme S, iota(3), which is multiplication by 3 (proved: iotaHom_natCast),
    is finite and etale. On a Z[1/30]-scheme no residue characteristic divides 3. One of the seven
    rows that replace y3FullThreeRepZ30 (Y3Buzzard.y3FullThreeRepZ30_of_printed_rem84); prints
    quoted and unprinted steps written out in
    ZInQKernel/Contrib/OneProof/Y3FullThreeRepZ30/README.md. -/
  milneProp207At3 : _root_.Y3Buzzard.MilneProp207 3
  /-- y3-printed, Milne, Abelian varieties, in Cornell-Silverman (eds.), Arithmetic Geometry
    (Springer 1986), Rem. 8.4 at g = 2 (p. 14 of the author's retyped edition), with Thm 8.2 (p.
    13) and section 20 (p. 42): for an FEC (an abelian scheme of relative dimension 2 with a ring
    homomorphism iota : O -> End) over a Z[1/30]-scheme S, a geometric point s : Spec k -> S and
    every n with (n : k) != 0, exactly n^4 points of A_s(k) are killed by n. Gives GeomCard3 (n =
    3; proved: Y3Buzzard.geomCard3_of_rem84) and, with MilneProp207 5, BuzzardFrameRepTorsor 5
    (proved: Y3Buzzard.buzzardFrameRepTorsor5_of_milne with Y3Buzzard.geomCard5_of_rem84), so
    Buzzard's representability sentence, printed without proof, is not an input. One of the seven
    rows that replace y3FullThreeRepZ30 (Y3Buzzard.y3FullThreeRepZ30_of_printed_rem84). -/
  milneTorsionCount : _root_.Y3Buzzard.MilneRem84
  /-- y3-printed, Buzzard, Duke Math. J. 87 (1997) Lemma 2.2 at N = 5 (author's preprint p. 6):
    over an algebraically closed field k with (30 : k) != 0, an automorphism of an FEC over Spec k
    with iota injective, commuting with iota(O), that fixes a point P with a |-> iota(a)P a
    bijection O/5O -> A[5](k), is the identity. P gives a full level-5 structure (Def. 1.1; A[5]
    finite etale by Milne 1986 Prop. 20.7, hence constant) whose H-orbit is a V1(5)-structure for
    every kappa. With milneThm125Pts and the 3-adic argument it proves the fibre rigidity at level
    3 (Y3Buzzard.serreRigidityFibreZ30_of_leaves), so serreRigidityLevel3 and Buzzard's
    polarization (README B-2, B-3) are no longer inputs. One of the eight rows that replace
    y3FullThreeRepZ30 (Y3Buzzard.y3FullThreeRepZ30_of_printed_xdv15). -/
  buzzardLemma22Full5 : _root_.Y3Buzzard.BuzzardLemma22Full5
  /-- y3-printed, Milne, Abelian varieties, in Cornell-Silverman (eds.), Arithmetic Geometry
    (Springer 1986), Thm 12.5 (p. 21 of the author's retyped edition), with Rem. 8.4 (p. 14) and
    Cor. 2.4 (p. 3): over an algebraically closed field k, two endomorphisms of an FEC over Spec k
    that agree on every point of l-power order, l a prime with (l : k) != 0, are equal. Uses only
    the printed injectivity of Z_l (x) End(A) -> End(T_l A) and the freeness of End(A). With
    buzzardLemma22Full5 it proves the fibre rigidity at level 3
    (Y3Buzzard.serreRigidityFibreZ30_of_leaves). One of the eight rows that replace
    y3FullThreeRepZ30 (Y3Buzzard.y3FullThreeRepZ30_of_printed_xdv15). -/
  milneThm125Pts : _root_.Y3Buzzard.MilneThm125Pts
  /-- y3-printed, Milne, Abelian varieties (1986) Cor. 20.2(a) (p. 43 of the author's retyped
    edition), restricted to locally noetherian bases: a morphism over S of FECs (abelian schemes
    of relative dimension 2 with a ring homomorphism from O) carrying the unit section to the unit
    section is a homomorphism. The printed proof applies Prop. 20.1, stated for a connected base;
    Lan, Harvard thesis (2008) Cor. 1.3.1.6 states it over any base, citing GIT Cor. 6.4. One of
    the seven rows that replace y3FullThreeRepZ30 (Y3Buzzard.y3FullThreeRepZ30_of_printed_rem84);
    prints quoted and unprinted steps written out in
    ZInQKernel/Contrib/OneProof/Y3FullThreeRepZ30/README.md. -/
  milneZeroPreservingHomLN : _root_.Y3Buzzard.ZeroPreservingIsHomLN
  /-- y3-printed, EGA IV4, Publ. Math. IHES 32 (1967), Prop. (17.5.7), p. 70, the 'integralement
    clos' case, in the direction from the base to the source, for a morphism smooth at every
    point: if the local ring of Y at f(x) is an integrally closed domain, so is the local ring of
    X at x. Mathlib's Smooth gives EGA's hypotheses (locally of finite presentation; formally
    smooth through the lifting criterion, EGA IV4 (17.1.1), (17.1.2)(i), (17.1.6), (17.3.1),
    (17.3.7)); 'integralement clos' for a local ring includes 'integre' in EGA's usage (EGA 0_I
    (4.1.4), IV2 (5.8.6), (5.13.5)). With the regularity-free smoothness of the level-V1(5) moduli
    curve over Z[1/30], it gives that the rings of its affine opens are noetherian and normal
    (Y3Buzzard.SmoothNormal.isNormalNoeth_of_B1). One of the nine rows that replace
    y3FullThreeRepZ30 (Y3Buzzard.SmoothNormal.y3FullThreeRepZ30_of_printed_raynaud). -/
  egaIV1757SmoothNormal : _root_.Y3Buzzard.SmoothNormal.EGAIV17_5_7
  /-- y3-printed, Raynaud, Faisceaux amples sur les schemas en groupes et les espaces homogenes,
    LNM 119 (Springer 1970), Ch. XI, p. 159 (Grothendieck's theorem, cf. XI 1.4): for every
    noetherian ring R whose localizations at primes are integrally closed domains
    (Y3Buzzard.SmoothNormal.IsNormalNoeth) and an FEC (Buzzard's false elliptic curve: an abelian
    scheme of relative dimension 2 with a ring homomorphism iota : O -> End) over Spec R, there is
    a closed immersion of A into some P^N_R over R (PNR). 'Projectif' read in EGA II's sense
    ((5.5.1)-(5.5.2)), turned into P^N over the affine base by (5.1.2) c'), (5.5.4)(ii) and
    (4.1.1); the alternative readings give the same through (5.5.3)(ii) or (5.5.4)(i). Gives
    LocProjNormal (proved: Y3Buzzard.SmoothNormal.locProjNormal_of_raynaud), so
    projectiveFalseEllipticCurve is no longer an input. One of the nine rows that replace
    y3FullThreeRepZ30 (Y3Buzzard.SmoothNormal.y3FullThreeRepZ30_of_printed_raynaud). -/
  raynaudLNM119Normal : _root_.Y3Buzzard.SmoothNormal.RaynaudLNM119Normal
  /-- y3-printed, Milne, Abelian varieties, in Cornell-Silverman (eds.), Arithmetic Geometry
    (Springer 1986), Prop. 20.7 at g = 2, n = 5 (p. 44 of the author's retyped edition): for an
    FEC (Buzzard's false elliptic curve: an abelian scheme of relative dimension 2 with a ring
    homomorphism iota : O -> End; injectivity of iota is automatic over a nonempty base, README
    B-1) over a Z[1/30]-scheme S, iota(5), which is multiplication by 5 (proved: iotaHom_natCast),
    is finite and etale. On a Z[1/30]-scheme no residue characteristic divides 5. One of the seven
    rows that replace y3FullThreeRepZ30 (Y3Buzzard.y3FullThreeRepZ30_of_printed_rem84); prints
    quoted and unprinted steps written out in
    ZInQKernel/Contrib/OneProof/Y3FullThreeRepZ30/README.md. -/
  milneProp207At5 : _root_.Y3Buzzard.MilneProp207 5
  /-- y3-printed, Voight, Quaternion Algebras, GTM 288 (Springer 2021), section 43.6: 43.6.12, Main Theorem 43.6.14 and Proposition 43.6.28, for B = (2,-3 | Q) and its maximal order O, at level 1, in lattice form: (i) every tau in the upper half-plane is the period of a complex abelian surface with an O-action ((A, iota) = (C^2/Lambda_tau, iota_tau)); (ii) every complex abelian surface with an O-action and a principal polarization compatible with mu (DelignePS.HasPrincipalRiemannMu) has such a period; (iii) two periods of one surface differ by an element of O of norm 1. One of the three rows that replace deligneCanonicalModelY3EveryPrint (DelignePS.deligneCanonicalModelY3EveryPrint_of_prints). -/
  voightQMComplexModuliPrint : _root_.DelignePS.VoightQMComplexModuliPrint
  /-- y3-printed, Boutot-Carayol, Asterisque 196-197 (1991), III, Proposition (1.5), p. 129, over C at U = U(3): every complex QM abelian surface with full level-3 structure has a principal *-polarization (t = mu = 2j + ij), read as a principal Riemann form of type mu (DelignePS.HasPrincipalRiemannMu). One of the five inputs of DelignePSMilne.deligneCanonicalModelY3EveryPrint_of_milne. -/
  boutotCarayolPolarizationPrint : _root_.DelignePS.BoutotCarayolPolarizationPrint
  /-- y3-printed, Boutot-Carayol, Asterisque 196-197 (1991), III 1.4, p. 129, at U(3) = K3: the moduli problem of QM abelian surfaces with full level-3 structure is representable over Q by a proper smooth curve (the generic fibre of 1.4's curve over Z[1/6N]), read on field points (Y3Fix.R1fpPropsAbP) and on families over proper smooth complex curves (classifying maps). One of the five inputs of DelignePSMilne.deligneCanonicalModelY3EveryPrint_of_milne. -/
  boutotCarayolRepresentabilityPrint : _root_.DelignePSMilne.BoutotCarayolRepresentabilityPrint
  /-- y3-glue (consequence): a proper smooth curve T over C with a family of QM abelian surfaces with full level-3 structure and a uniformization psi of T(C) by H^pm x (B (x) A_f)^x, onto and holomorphic in tau, whose fibre at psi(z, g) is the level object of [z, g]; from Milne, Clay Math. Proc. 4 (2005), Thm 14.8 (Deligne, Hodge II, 4.4.3) applied as on p. 354, with Baily-Borel, and derived steps. One of the five inputs of DelignePSMilne.deligneCanonicalModelY3EveryPrint_of_milne. -/
  milneShimuraFamilyPrint : _root_.DelignePSMilne.MilneShimuraFamilyPrint
  /-- y3-printed, Milne, Clay Math. Proc. 4 (2005), §14, the PEL paragraph (pp. 354-355), with Def. 12.8 and (54) (p. 346), at the datum of Y3 (type C, reflex field Q) and level K3: a proper smooth curve over Q uniformized by B^x \ (H^pm x (B (x) A_f)^x / K3), on which Aut(C) acts as on the level objects, satisfies the reciprocity law at CM points (DelignePS.CVReciprocityAt, sign existential). One of the five inputs of DelignePSMilne.deligneCanonicalModelY3EveryPrint_of_milne. -/
  milneCanonicalModelPrint : _root_.DelignePSMilne.MilneCanonicalModelPrint

/-- `OpenResearchLeaves83CMJ` from `OpenResearchLeaves87`: `deligneCanonicalModelY3EveryPrint` by Milne's existence argument. -/
theorem openResearchLeaves83CMJ_of_OpenResearchLeaves87 (n : OpenResearchLeaves87) : OpenResearchLeaves83CMJ where
  pazukiCor13Upper := n.pazukiCor13Upper
  dsThm966Printed := n.dsThm966Printed
  afCharpolyDS965 := n.afCharpolyDS965
  modularHTCoeff := n.modularHTCoeff
  deligneCanonicalModelY3EveryPrint := _root_.DelignePSMilne.deligneCanonicalModelY3EveryPrint_of_milne n.voightQMComplexModuliPrint n.boutotCarayolPolarizationPrint n.boutotCarayolRepresentabilityPrint n.milneShimuraFamilyPrint n.milneCanonicalModelPrint
  javanpeykarThm111An := n.javanpeykarThm111An
  carayolThmAFrob := n.carayolThmAFrob
  cmHeight62 := _root_.ZInQ.Contrib.CMHeight62Full.cmHeight62_unconditional
  fowlerProp27PrintCanonical := n.fowlerProp27PrintCanonical
  silverbergZarhinThm34 := n.silverbergZarhinThm34
  bergerSurveyF := n.bergerSurveyF
  panThm104F := n.panThm104F
  gaudronRemondSec9LowerGR1Weak := n.gaudronRemondSec9LowerGR1Weak
  gaudronRemondThm14GR1 := n.gaudronRemondThm14GR1
  egaIV_9_7_7_OL := n.egaIV_9_7_7_OL
  buzzardXDV15Lit := n.buzzardXDV15Lit
  milneProp207At3 := n.milneProp207At3
  milneTorsionCount := n.milneTorsionCount
  buzzardLemma22Full5 := n.buzzardLemma22Full5
  milneThm125Pts := n.milneThm125Pts
  milneZeroPreservingHomLN := n.milneZeroPreservingHomLN
  egaIV1757SmoothNormal := n.egaIV1757SmoothNormal
  raynaudLNM119Normal := n.raynaudLNM119Normal
  milneProp207At5 := n.milneProp207At5

/-- **G0 with only the open leaves and the open glue** (y3-milne-1128; skip-generation onto `OpenResearchLeaves83CMJ`). -/
theorem sixContactMin_of_open109 (r : OpenResearchLeaves87) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves31) : ZInQ.SixContactMin :=
  sixContactMin_of_open104_cmj (openResearchLeaves83CMJ_of_OpenResearchLeaves87 r) t (openAddedLeaves30_of_OpenAddedLeaves31 l)

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open109
