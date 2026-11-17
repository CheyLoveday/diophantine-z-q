import json
old=json.load(open('scratch/r16-close/autofold.json'))
L={l['name']:l for l in old['discharges'][0]['leaves']}
for k in ['heckeJ1DS','afShimura','igusaGL2DS']:
  L[k]['doc']=L[k]['doc'].replace('(r16-close fold)','(r16-det fold)',1)
cp={"name":"afCharpolyDS965","type":"_root_.AfTateLam.AfCharpolyDS965",
 "doc":"r16-det: Diamond-Shurman Thm 9.6.5 at k = 2 for the Section 9.5 realization on A_f, over K_{f,lambda}, universal over A_f. For every (A, pi, theta) that is DS's A_f (afShimura's characterization, for any X, generators, P0, Jacobian and Hecke operators as in heckeJ1DS), every prime l and every place lambda | l of K_f: for p not dividing N l every arithmetic Frobenius sigma at p acting on V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) (rho_{f,lambda}, DS Exercise 9.5.2(a)) has characteristic polynomial X^2 - a_p X + chi(p) p over K_lambda. Statement = aftate-fix2's AfTateLam.AfTateDSLambda verbatim (AfTateLam.afCharpolyDS965_iff, Iff.rfl); it implies r16-close's glue AfDetLambda (AfTateLam.afDetLambda_of_ds965).",
 "kind":"published",
 "flag":"unread: new printed leaf (Diamond-Shurman Thm 9.6.5, 'the characteristic equation of rho_{f,lambda}(Frob_p) is x^2 - a_p x + chi(p) p^{k-1} = 0', at k = 2, with DS's identification on the same page that for k = 2 the representation is the Section 9.5 construction, whose characteristic equation Section 9.5 had not proved; AI-read by r16-det in the 2005 (p. 393) and 2016 (p. 404) printings, no human reading)",
 "source":"Diamond-Shurman, A First Course in Modular Forms, GTM 228 (2005), Theorem 9.6.5 and the paragraph after it, p. 393 (2016 fourth printing p. 404); rho_{f,lambda} and V_l(A_f) as in Lemma 9.5.3, Theorem 9.5.4, Exercise 9.5.2(a), pp. 389-391"}
spec={"name":"r16-det","imports":["ZInQKernel.Contrib.OneProof.R16CoreYDS965"],
 "discharges":[{"field":"r16CoreY",
  "proof":"_root_.AfTateLam.r16CoreY_of_ds965 {n}.heckeJ1DS {n}.afShimura {n}.afCharpolyDS965 {n}.igusaGL2DS {t}.mumfordTorsionAlgClosed",
  "leaves":[L['heckeJ1DS'],L['afShimura'],cp,L['igusaGL2DS']]}],
 "note":"r16-det: report docs/research/r16-det.md. r16-close's fold with the pair AfTateDSLambdaSat (DS 9.5.4, 'satisfies') + AfDetLambda (GLUE) replaced by the single printed leaf AfCharpolyDS965 (DS Thm 9.6.5 at k = 2, which DS identify with the Section 9.5 realization on A_f; read in both printings). After fold34-pr (mumfordTorsionAlgClosed proved by PR #54) replace {t}.mumfordTorsionAlgClosed by _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof."}
json.dump(spec,open('scratch/r16-det/autofold.json','w'),indent=1,ensure_ascii=False)
