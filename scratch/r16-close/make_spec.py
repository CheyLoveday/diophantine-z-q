import json
old=json.load(open('scratch/aftate-fix2/autofold.json'))
L={l['name']:l for l in old['discharges'][0]['leaves']}
sat={"name":"afTateDSLambdaSat","type":"_root_.AfTateLam.AfTateDSLambdaSat",
 "doc":"r16-close: Diamond-Shurman Lemma 9.5.3 + Thm 9.5.4 as printed, over K_{f,lambda}, universal over A_f. For every (A, pi, theta) that is DS's A_f (afShimura's characterization, for any X, generators, P0, Jacobian and Hecke operators as in heckeJ1DS), every prime l and every place lambda | l of K_f: V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) has dimension 2 over K_lambda (Lemma 9.5.3), and for p not dividing N l every arithmetic Frobenius sigma at p satisfies X^2 - a_p X + chi(p) p on V_lambda (rho_{f,lambda}(sigma) is a root; Thm 9.5.4 says 'satisfies the polynomial equation', not 'characteristic polynomial').",
 "kind":"published",
 "flag":"unread: new printed leaf (Diamond-Shurman Lemma 9.5.3 + Thm 9.5.4, the 'satisfies' wording; AI-read in the 2005 and 2016 printings by r16-close and by the W24 check report-ds954, no human reading)",
 "source":"Diamond-Shurman, A First Course in Modular Forms, GTM 228 (2005), Lemma 9.5.3 and Theorem 9.5.4, pp. 390-391 (2016 fourth printing pp. 401-402); A_f as in Def. 6.6.3"}
det={"name":"afDetLambda","type":"_root_.AfTateLam.AfDetLambda",
 "doc":"r16-close: the determinant of rho_{f,lambda} at Frobenius. For (A, pi, theta) = DS's A_f as in afTateDSLambdaSat, l, lambda | l and p not dividing N l: every arithmetic Frobenius sigma at p has det rho_{f,lambda}(sigma) = chi(p) p on V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) (i.e. det rho_{f,lambda} = chi chi_l at Frobenius). With afTateDSLambdaSat it gives the characteristic polynomial (AfTateLam.dsLambda_of_sat_det).",
 "kind":"consequence",
 "flag":"",
 "source":"det rho_{f,lambda} = chi chi_l for the realization on V_l(A_f): not printed in Diamond-Shurman for Thm 9.5.4 (only for Thm 9.6.5's rho, Exercise 9.6.3(a), read); candidates Shimura 1971 Thm 7.14, Ribet LNM 601 (1977) section 2 (UNVERIFIED, unread); derivable from the Weil pairing on J_1(N) with T_p* = <p>^{-1} T_p (not in the tree)"}
for k in ['heckeJ1DS','afShimura','igusaGL2DS']:
  L[k]['doc']=L[k]['doc'].replace('aftate-fix2:','aftate-fix2 (r16-close fold):',1)
L['heckeJ1DS']['flag']="unread: new printed leaf (Diamond-Shurman 6.3 Hecke operators on Div/Pic^0 of X_1(N) by double cosets, pp. 226-227, coset representatives Prop. 5.2.1 p. 171, 7.9 T_p and <d> defined over Q p. 300; AI-read by r16-close, no human reading)"
L['heckeJ1DS']['source']="Diamond-Shurman, A First Course in Modular Forms, GTM 228 (2005), 6.3 (pp. 226-227), Prop. 5.2.1 (p. 171), 7.9 (p. 300); Shimura 1971 7.2 (unread)"
L['igusaGL2DS']['flag']="unread: new printed leaf (Diamond-Shurman Thm 7.6.3, Gal(Q(j,E_j[N])/Q(j)) = GL_2(Z/N), p. 290, with E_j of (7.12) p. 282; AI-read by r16-close, no human reading)"
L['igusaGL2DS']['source']="Diamond-Shurman, A First Course in Modular Forms, GTM 228 (2005), Theorem 7.6.3 (p. 290), universal curve (7.12) (p. 282); Igusa, Amer. J. Math. 81 (1959) (unread)"
L['afShimura']['source']="Shimura, On the factors of the jacobian variety of a modular function field, J. Math. Soc. Japan 25 (1973), Thm 1, pp. 526-527 (read by the locator audit, row R16); Diamond-Shurman GTM 228 (2005), Def. 6.6.3 (p. 241), Prop. 6.6.4 (p. 242) (AI-read by r16-close)"
spec={"name":"r16-close","imports":["ZInQKernel.Contrib.OneProof.R16CoreYSatDet"],
 "discharges":[{"field":"r16CoreY",
  "proof":"_root_.AfTateLam.r16CoreY_of_sat_det {n}.heckeJ1DS {n}.afShimura {n}.afTateDSLambdaSat {n}.afDetLambda {n}.igusaGL2DS {t}.mumfordTorsionAlgClosed",
  "leaves":[L['heckeJ1DS'],L['afShimura'],sat,det,L['igusaGL2DS']]}],
 "note":"r16-close: report docs/research/r16-close.md. aftate-fix2's leaves (HeckeJ1DS, AfShimura, IgusaGL2DS) with AfTateDSLambda replaced by the pair AfTateDSLambdaSat (DS 9.5.3 + 9.5.4 as printed: 'satisfies', read) + AfDetLambda (GLUE: determinant, no print found), because DS 9.5.4 does not print the characteristic polynomial (both printings). After fold34-pr (mumfordTorsionAlgClosed proved by PR #54) replace {t}.mumfordTorsionAlgClosed by _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof."}
json.dump(spec,open('scratch/r16-close/autofold.json','w'),indent=1,ensure_ascii=False)
