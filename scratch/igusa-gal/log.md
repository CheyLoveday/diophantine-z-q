# igusa-gal results log

## Page check, Diamond-Shurman GTM 228 (VERIFIED: read in the 2005 printing and the 2016 4th printing on this host)
Page numbers: printed page = PDF page - 11 (2005) / - 13 (2016), checked against running heads.
- Thm 7.6.3 (H_Q = Gal(Q(j,E_j[N])/Q(j)), rho : H_Q -> GL2(Z/N) an isomorphism): p. 290 (2005) / p. 294 (2016).
- rho defined in 7.6 as the action of H_Q on E_j[N] in the ordered basis (P_tau, Q_tau) of (7.11),
  (P^s, Q^s)^T = rho(s) (P, Q)^T: p. 287 (2005) / p. 291 (2016); same as Cor 7.5.3, p. 284 / p. 288.
  One fixed basis (canonical up to sign); "any basis" is a consequence (conjugate by a fixed GL2 element, transpose).
- N: section 7.5 opens "where N > 1" (p. 279 / p. 283); 7.6 and Thm 7.6.3 inherit it. N = 1 is trivial.
- (7.12) E_j : y^2 = 4x^3 - (27j/(j-1728)) x - 27j/(j-1728): p. 282 / p. 286; j viewed as transcendental over C (p. 282 / 286).
- Where E_j[N] lives: points of E_j over Q(j) are pairs in an algebraic closure of Q(j) (7.6 opening, p. 287 / p. 291);
  over C: pairs from the algebraic closure of C(j) (p. 282 / p. 286).
- Q(j, E_j[N]) = field generated over Q(j) by x(E_j[N]) u y(E_j[N]) (defined over C, p. 283 / p. 287; carried to Q in 7.6).
- Group law: chord-tangent, origin 0_E = [0,1,0], rational formulas (7.3) (section 7.1, pp. 253-254 / pp. 257-258).
- Q(j): j transcendental (algebraic view, p. 282 / p. 286), so Q(j) = RatFunc Q; analytic meromorphic-function view
  (x1-igusa.md) is the motivation, not the definition used in 7.6.

## Lean
- ZInQKernel/Contrib/OneProof/IgusaGL2DSGal.lean: coordsDS, LDS (= Q(j,E_j[N]) in Kbar), IgusaGL2DSGal (1 < N),
  exists_LDS_point, galPtDS_liftNormal_inc, igusaGL2DS_of_igusaGL2DSGal : IgusaGL2DSGal -> IgusaGL2DS.
  `lake env lean` on it: no errors, no warnings (VERIFIED, 11-17 03:44).
- `lake build +ZInQKernel.Contrib.OneProof.IgusaGL2DSGal`: success (10403 jobs, only this module compiled) (VERIFIED).
- Consumers of IgusaGL2DS (x1PointsConjugate_of_igusaGL2DS, r16CoreY_of_picZero_igusaDS / AfTateLambda.lean:858,
  r16CoreY_of_dsOr_igusaDS, R16CoreYSatDet, R16CoreYDS965, TailZ66-71 bundle field) all take IgusaGL2DS as a
  hypothesis; IgusaGL2DSGal -> IgusaGL2DS is unconditional, so none loses anything (VERIFIED by grep of uses).

## Autofold
- scratch/igusa-gal/autofold.json: discharge igusaGL2DS by X1Igusa.igusaGL2DS_of_igusaGL2DSGal {n}.igusaGL2DSGal,
  new leaf igusaGL2DSGal (published, flag "unread: ... AI page check ...").
- `autofold.py --dry-run`: exit 0, "strict count: 9/25 on 34 -> 10/24 on 34; strictest 9/25 -> 10/24" (VERIFIED);
  output in autofold-dryrun.txt. Exact kinds row: scratch/igusa-gal/kinds-row.tsv.
