#!/usr/bin/env python3
"""Exact cochain tests, not an arithmetic Galois-cohomology proof.

Alexander--Whitney cups on an oriented simplicial 3x3 torus supply a
nontrivial differential, nonzero H1 x H1 trace pairing, and nonzero
representative corrections. All tests use integer arithmetic.
"""
from itertools import combinations
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import random
import sys

N = 3
vertices = list(range(N*N))
def vertex(x,y): return (x%N)+N*(y%N)
def parity(xs):
    return (-1)**sum(xs[i]>xs[j] for i in range(len(xs)) for j in range(i+1,len(xs)))
triangles = {}
for x in range(N):
    for y in range(N):
        a,b,c,d=vertex(x,y),vertex(x+1,y),vertex(x+1,y+1),vertex(x,y+1)
        for t in [(a,b,c),(a,c,d)]: triangles[tuple(sorted(t))]=parity(t)
faces = sorted(triangles)
edges = sorted({e for t in faces for e in combinations(t,2)})

def d0(q): return {e:q[e[1]]-q[e[0]] for e in edges}
def d1(a): return {t:a[(t[1],t[2])]-a[(t[0],t[2])]+a[(t[0],t[1])] for t in faces}
def cup10(a,q): return {e:a[e]*q[e[1]] for e in edges}
def cup01(q,a): return {e:q[e[0]]*a[e] for e in edges}
def cup11(a,b): return {t:a[(t[0],t[1])]*b[(t[1],t[2])] for t in faces}
def cup20(z,q): return {t:z[t]*q[t[2]] for t in faces}
def cup02(q,z): return {t:q[t[0]]*z[t] for t in faces}
def trace(z): return sum(triangles[t]*z[t] for t in faces)
def add(a,b): return {i:a[i]+b[i] for i in a}
def sub(a,b): return {i:a[i]-b[i] for i in a}
def neg(a): return {i:-a[i] for i in a}
def scale(c,a): return {i:c*a[i] for i in a}
def zero(a): return all(x==0 for x in a.values())
def wrap(d): return (d+1)%N-1
dx={e:wrap(e[1]%N-e[0]%N) for e in edges}
dy={e:wrap(e[1]//N-e[0]//N) for e in edges}

def rank(rows):
    a=[[Fraction(x) for x in row] for row in rows]; r=0
    for c in range(len(a[0]) if a else 0):
        pivot=next((i for i in range(r,len(a)) if a[i][c]),None)
        if pivot is None: continue
        a[r],a[pivot]=a[pivot],a[r]; p=a[r][c];a[r]=[x/p for x in a[r]]
        for i in range(len(a)):
            if i!=r:
                p=a[i][c]; a[i]=[x-p*y for x,y in zip(a[i],a[r])]
        r+=1
    return r

def main():
    rng=random.Random(20261109)
    assert (len(vertices),len(edges),len(faces))==(9,27,18)
    for v in vertices:
        q={u:int(u==v) for u in vertices}; assert zero(d1(d0(q)))
    for e in edges:
        a={f:int(f==e) for f in edges}; assert trace(d1(a))==0
    assert zero(d1(dx)) and zero(d1(dy))
    pairing=[[trace(cup11(x,y)) for y in [dx,dy]] for x in [dx,dy]]
    assert pairing==[[0,9],[-9,0]]
    matrix0=[[d0({v:int(v==w) for v in vertices})[e] for w in vertices] for e in edges]
    matrix1=[[d1({e:int(e==f) for e in edges})[t] for f in edges] for t in faces]
    ranks=[rank(matrix0),rank(matrix1)]
    assert ranks==[8,17] and len(edges)-sum(ranks)==2
    corrections=0; bad_sign=None; bad_trace=None; bad_cycle=None
    for _ in range(256):
        p={v:rng.randrange(-7,8) for v in vertices}
        q={v:rng.randrange(-7,8) for v in vertices}
        raw={e:rng.randrange(-7,8) for e in edges}
        l=add(add(scale(rng.randrange(-5,6),dx),scale(rng.randrange(-5,6),dy)),d0(p))
        m=add(scale(rng.randrange(-5,6),dx),scale(rng.randrange(-5,6),dy))
        local_condition=add(m,d0(q)); correction=d1(cup10(l,q))
        lhs=cup11(l,local_condition); rhs=sub(cup11(l,m),correction)
        assert lhs==rhs
        assert trace(lhs)==trace(cup11(l,m))
        assert d1(cup10(raw,q))==sub(cup20(d1(raw),q),cup11(raw,d0(q)))
        assert d1(cup01(q,raw))==add(cup11(d0(q),raw),cup02(q,d1(raw)))
        assert trace(cup11(d0(q),m))==0
        assert trace(cup11(m,d0(q)))==0
        if not zero(correction):
            corrections+=1
            if bad_sign is None:
                t=next(t for t in faces if correction[t])
                bad_sign={"triangle":t,"actual":lhs[t],"wrong_plus":cup11(l,m)[t]+correction[t]}
        if bad_trace is None:
            t=next((t for t in faces if lhs[t]!=cup11(l,m)[t]),None)
            if t is not None:bad_trace={"triangle":t,"condition_cup":lhs[t],"global_cup":cup11(l,m)[t]}
        wrong=sub(cup11(raw,local_condition),sub(cup11(raw,m),d1(cup10(raw,q))))
        if not zero(wrong) and bad_cycle is None:
            t=next(t for t in faces if wrong[t]);bad_cycle={"triangle":t,"unaccounted_term":wrong[t],"d_l_nonzero":not zero(d1(raw))}
    assert corrections>0 and bad_sign and bad_trace and bad_cycle
    result={"status":"PASS","scope":"exact cochain model only; no arithmetic global construction", "simplicial_torus":{"vertices":9,"edges":27,"triangles":18,"differential_ranks":ranks,"H1_dimension":2,"trace_pairing":pairing},"trials":256,"nonzero_corrections":corrections,"negative_controls":{"wrong_correction_sign":bad_sign,"trace_not_a_chain_map":bad_trace,"missing_closed_direction_guard":bad_cycle},"script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    data=json.dumps(result,indent=2)+"\n"
    if len(sys.argv)==2:Path(sys.argv[1]).write_text(data)
    else:print(data,end="")
if __name__=="__main__":main()
