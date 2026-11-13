#!/usr/bin/env python3
"""Exact, bounded controls for Sun/Elliot/E364 interface review.

Python standard library only. These are diagnostics of displayed algebra,
not a proof of the papers, a prime-pattern experiment, or a Lean replay.
Run: python replay.py --output results.json
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, math
from fractions import Fraction as F
from pathlib import Path
from typing import Iterable

Q2 = tuple[F, F]  # a + b*sqrt(2)

def q(a=0, b=0) -> Q2:
    return F(a), F(b)

def add(x: Q2, y: Q2) -> Q2:
    return x[0]+y[0], x[1]+y[1]

def neg(x: Q2) -> Q2:
    return -x[0], -x[1]

def mul(x: Q2, y: Q2) -> Q2:
    a,b=x; c,d=y
    return a*c+2*b*d, a*d+b*c

def scale(a, x: Q2) -> Q2:
    return F(a)*x[0], F(a)*x[1]

def inv(x: Q2) -> Q2:
    a,b=x; n=a*a-2*b*b
    if n == 0: raise ZeroDivisionError('zero field element')
    return a/n, -b/n

def div(x: Q2, y: Q2) -> Q2:
    return mul(x,inv(y))

def power(x: Q2, n: int) -> Q2:
    if n < 0: return power(inv(x),-n)
    out=q(1)
    while n:
        if n&1: out=mul(out,x)
        x=mul(x,x); n>>=1
    return out

def tr(x: Q2) -> F:
    return 2*x[0]

def vp(x: F | int, p: int) -> int:
    x=F(x)
    if not x: raise ValueError('valuation of zero is not finite')
    def val(n):
        n=abs(n); r=0
        while n%p==0: n//=p; r+=1
        return r
    return val(x.numerator)-val(x.denominator)

def need(ok: bool, message: str) -> None:
    if not ok: raise AssertionError(message)

def crt_pair(a: int,m: int,b: int,n: int) -> tuple[int,int]:
    if m<=0 or n<=0: raise ValueError('positive moduli required')
    g=math.gcd(m,n)
    if (b-a)%g: raise ValueError('incompatible residues')
    nn=n//g
    k=0 if nn==1 else ((b-a)//g*pow(m//g,-1,nn))%nn
    mod=m*nn
    return (a+m*k)%mod,mod

def crt(congruences: Iterable[tuple[int,int]]) -> tuple[int,int]:
    r,m=0,1
    for a,n in congruences: r,m=crt_pair(r,m,a,n)
    return r,m

def test_model_unit():
    lam=q(3,-2); d=q(3,-1); d0=q(75,-53)
    P=(q(F(57,8),F(-7,2)),q(F(-165,8),F(417,32)))
    P0=(q(F(1641,8),F(-1160,8)),q(F(-123720,32),F(87483,32)))
    need(mul(lam,q(3,2))==q(1),'unit norm')
    need(mul(d,power(lam,2))==d0,'model parameter transport')
    need(mul(power(lam,2),P[0])==P0[0],'x transport')
    need(mul(power(lam,3),P[1])==P0[1],'y transport')
    need(power(P[1],2)==add(power(P[0],3),neg(mul(power(d,2),P[0]))),'curve')
    return {'checks':5,'lambda_norm':1}

def test_joint_local_witness():
    # K=Q(sqrt2), p=17 splits. D1,D2 are good at opposite places.
    p=17; D1=q(-6,1); D2=q(6,1)
    W1=add(q(1),scale(F(1,p),power(D1,2)))
    W2=add(q(1),scale(F(1,p),power(D2,2)))
    theta1=tr(inv(W1)); theta2=tr(inv(W2))
    W=mul(W1,W2); theta=tr(inv(W))
    B1=F(p)/theta1**2; B2=F(p)/theta2**2; B=F(p)/theta**2
    need(W==q(F(161,17)),'joint product')
    need(theta==F(34,161),'joint trace')
    need(B==F(25921,68),'joint pole input')
    need(vp(B1,p)==vp(B2,p)==1 and vp(B,p)==-1,'separate versus joint parity')
    return {'p':17,'individual_B':str(B1),'individual_vp':1,'joint_W':str(W[0]),
            'joint_theta':str(theta),'joint_B':str(B),'joint_vp':-1,
            'scope':'Local parity control only, not full pole-predicate witnesses.'}

def test_ordinate_atlas():
    vals=sorted({F(a,b) for a in range(-6,7) for b in (1,2,3)})
    counts={str(i):0 for i in range(1,5)}
    for y0 in vals:
        for y1 in vals:
            f0=y0*y0+2*y1*y1; f1=2*y0*y1
            if f1:
                need(y0**4-f0*y0*y0+f1*f1/2==0,'quartic elimination')
                need(f1/(2*y0)==y1,'ordinate reconstruction')
                need(f0*f0-2*f1*f1!=0,'nonzero discriminant condition')
                counts['1']+=1
            elif f0 and not y1:
                need(y0*y0==f0,'rational-axis chart'); counts['2']+=1
            elif f0 and not y0:
                need(y1*y1==f0/2,'sqrt2-axis chart'); counts['3']+=1
            else:
                need(y0==y1==f0==f1==0,'zero chart'); counts['4']+=1
    return {'cases':len(vals)**2,'chart_counts':counts}

def test_separator():
    s=q(0,1)
    tuples=[(scale(a,s),scale(b,s)) for a in (-1,1) for b in (-1,1)]
    values={b:[add(x,scale(b,y)) for x,y in tuples] for b in (1,2)}
    need(len(set(values[1]))==3,'collision control')
    need(q(0) in values[1],'spurious rational collapsed coordinate')
    need(all(any(z[1]!=0 for z in tup) for tup in tuples),'no rational tuple')
    need(len(set(values[2]))==4,'separating choice')
    need(all(z[1]!=0 for z in values[2]),'no false rational root after separation')
    N=2**44; k=26
    return {'bad_b':1,'good_b':2,'bad_projected_rational_root':0,
            'uniform_separator_candidate_count_bound':(k-1)*N*(N-1)//2+1}

def poly_mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return out

def poly_val(a,x):
    out=F(0)
    for c in reversed(a): out=out*x+c
    return out

def test_reciprocal_guard():
    cases=0; zero_guard_cases=0
    roots=[F(-2),F(0),F(1,2),F(3)]
    for shift in (0,1):
        rr=[r+shift for r in roots]
        poly=[F(1)]
        for r in rr: poly=poly_mul(poly,[-r,F(1)])
        d=len(poly)-1; D=math.lcm(*(c.denominator for c in poly))
        nums=[poly[d-j]*D for j in range(1,d+1)]
        for G in (-3,1,4):
            psi=[F(1)]+[nums[j-1]*D**(2*j-1)*G**j for j in range(1,d+1)]
            for t in rr:
                if not t: continue
                W=F(1,D*D*G)/t
                need(poly_val(psi,W)==0,'forward reciprocal root')
                cases+=1
            for W in [F(a,b) for a in range(-4,5) if a for b in (1,2,3)]:
                lhs=poly_val(psi,W)
                rhs=(D*D*G*W)**d*poly_val(poly,1/(D*D*G*W))
                need(lhs==rhs,'exact reciprocal identity'); cases+=1
        psi0=[F(1)]+[F(0)]*d
        for W in (-2,0,1,3):
            need(poly_val(psi0,W)==1,'failed guard is identically one');zero_guard_cases+=1
    return {'identity_and_forward_cases':cases,'zero_guard_cases':zero_guard_cases}

def test_determinant_countercontrol():
    out=[]
    for pi in (2,3,5,17):
        # DF=[[0,pi],[0,0]], DS=[[0,0],[0,pi^2]], J=diag(1,-1)
        uF=-F(1,pi); uS=F(1,pi*pi); delta=-1; qF=-pi*pi; qS=pi
        need(delta*uF/uS == -F(qF,qS)==pi,'normalization defect')
        out.append({'uniformizer':pi,'uF':str(uF),'uS':str(uS),'transported_ratio':pi})
    return {'models':out,'scope':'Countermodels to rank/primitivity-only inference, not arithmetic counterexamples.'}


def test_characterwise_descent_control():
    # In Q_2[(Z/2)^b], e = |G|^-1 sum_g g is the trivial idempotent.
    # Every character of u=1+2e is an integral unit, yet the group-basis
    # coefficients require the unbounded clearing factor 2^(b-1).
    rows=[]
    for b in range(1,9):
        n=1<<b
        coeff=[F(2,n)]*n
        coeff[0]+=1
        vals=[]
        for x in range(n):
            value=sum(((-1 if (x & g).bit_count()%2 else 1)*coeff[g] for g in range(n)),F(0))
            need(value==(3 if x==0 else 1),'characterwise unit values')
            need(vp(value,2)==0,'all scalar values are 2-adic units')
            vals.append(value)
        denominator=math.lcm(*(c.denominator for c in coeff))
        need(denominator==2**(b-1),'minimal common group-basis clearing factor')
        rows.append({'binary_dimension':b,'characters_checked':n,
                     'all_character_values_are_2_adic_units':True,
                     'group_basis_common_denominator':denominator})
    return {'families':rows,'scope':'Countercontrol to scalar-unit-to-universal-integrality inference; not an arithmetic-family counterexample.'}

def test_crt():
    cons=[(0,4*5*13),(64,64*11*17),(0,64*3*7),(128,256),(9,27),(7,49)]
    h,period=crt(cons)
    for a,m in cons: need((h-a)%m==0,'shared CRT residue')
    for p,a in [(2,7),(3,2),(7,1)]: need(vp(h,p)==a,'exact valuation')
    rejected=0
    for cs in [[(0,5),(1,5)],[(32,64),(128,256)]]:
        try: crt(cs)
        except ValueError: rejected+=1
        else: raise AssertionError('incompatible control accepted')
    return {'h':h,'period':period,'congruences':cons,'incompatible_controls_rejected':rejected,
            'scope':'Synthetic order moduli: no simultaneous prime theorem is being tested.'}

def spf_sieve(n):
    spf=list(range(n+1))
    for p in range(2,math.isqrt(n)+1):
        if spf[p]==p:
            for j in range(p*p,n+1,p):
                if spf[j]==j: spf[j]=p
    return spf

def factor(n,spf):
    out={}
    while n>1:
        p=spf[n]; out[p]=out.get(p,0)+1;n//=p
    return out

def test_e364(limit=20000):
    spf=spf_sieve(limit+1); cases=0; local_cases=0
    for N in range(2,limit+1,2):
        fs=[factor(N+i,spf) for i in (-1,0,1)]
        powers={}
        for f in fs:
            for p,k in f.items(): powers[p]=powers.get(p,0)+k
        D=math.prod(p for p,k in powers.items() if k%2)
        s=math.prod(p**(k//2) for p,k in powers.items())
        need(N*(N*N-1)==D*s*s,'squarefree decomposition')
        x=F(D*N);y=F(D*D*s)
        need(y*y==x**3-D*D*x,'marked point')
        slope=(3*x*x-D*D)/(2*y)
        xx=slope*slope-2*x;yy=slope*(x-xx)-y
        f=(N*N+1)*(N*N-2*N-1)*(N*N+2*N-1)
        need(xx==F((N*N+1)**2,4*s*s),'doubling x')
        need(yy==F(f,8*s**3),'doubling y')
        need(xx.denominator==4*s*s and yy.denominator==8*s**3,'reduced denominators')
        defect=D//math.gcd(D,s)
        need(defect==math.prod(p for p,k in powers.items() if k==1),'defect identity')
        is_powerful=all(all(k>=2 for k in ff.values()) for ff in fs)
        need(is_powerful==(D and s%D==0)==(defect==1),'powerful equivalence')
        z=-xx/yy
        for p,k in powers.items():
            if p!=2 and k%2:
                need(vp(z,p)==(k-1)//2,'formal-parameter valuation');local_cases+=1
        need(vp(z,2)==1+vp(s,2),'dyadic valuation')
        cases+=1
    # Odd N is outside the theorem: the unreduced denominator formula is not exact there.
    N=3;D=6;s=2
    need(F((N*N+1)**2,4*s*s).denominator!=4*s*s,'odd-midpoint adverse control')
    return {'even_midpoints':cases,'max_midpoint':limit,'odd_prime_depth_checks':local_cases,
            'odd_midpoint_denominator_control_rejected':True,
            'scope':'Bounded exact replay; the displayed identities have separate algebraic proofs.'}


def test_scalar_norm_tree():
    # At odd R, valuations in u^2+r*v^2 cannot cancel.
    # Paths refer to the seven ordered leaves in the displayed scalar tree.
    paths=('LLL','LLR','LRL','LRR','RL','RRL','RRR')
    weights=[]
    for path in paths:
        c=F(1,2)
        for step in path: c=c/2 if step=='L' else (c+1)/2
        weights.append(c)
    need(weights==list(map(F,('1/16','9/16','5/16','13/16','3/8','7/16','15/16'))),'scalar tree precision weights')
    cases=0;accepted=0
    for R in (1,3,5,7):
        values=sorted({-2*R,-R,-R+1,0,R})
        def node(a,b): return min(2*a,R+2*b)
        for z in itertools.product(values,repeat=6):
            a=node(0,z[0]);b=node(z[1],z[2]);d=node(z[4],z[5])
            root=node(node(a,b),node(z[3],d))
            if 2*root > -R:
                need(all(v > -R for v in z),'scalar certificate forces every leaf depth')
                accepted+=1
            cases+=1
    return {'exact_path_weights':list(map(str,weights)),'sampled_valuation_tuples':cases,
            'accepting_valuation_tuples':accepted,
            'scope':'Symbolic path arithmetic plus bounded valuation diagnostics; no global pole completeness claim.'}

def test_thresholds():
    kappa=24; degree=4
    need(F(kappa*degree,64)<2,'Lucas defect exponent')
    a=F(kappa,16)
    need(a<2 and a/(2-a)==3,'numerator feedback coefficient')
    need(F(kappa,48)<1,'scalar sublinear growth')
    return {'height_radical_exponent':kappa,'minimum_strict_thresholds':{'K_delta_gt':48,'K_numerator_gt':12,'K_scalar_gt':24},
            'actual_precisions':[64,16,48],'numerator_feedback_coefficient':3}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=Path('results.json'))
    args=ap.parse_args()
    results={name:fn() for name,fn in [
        ('model_unit',test_model_unit),('joint_local_witness',test_joint_local_witness),
        ('ordinate_atlas',test_ordinate_atlas),('separator',test_separator),
        ('reciprocal_guard',test_reciprocal_guard),('determinant_countercontrol',test_determinant_countercontrol),
        ('characterwise_descent',test_characterwise_descent_control),('crt',test_crt),('e364',test_e364),('scalar_norm_tree',test_scalar_norm_tree),('thresholds',test_thresholds)]}
    payload={'status':'PASS','scope':'Exact bounded interface diagnostics; NOT full-paper verification.',
             'python_dependencies':'standard library only', 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             'results':results}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps(payload,indent=2))

if __name__=='__main__': main()
