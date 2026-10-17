"""Independent finite checks for the exponent-four classification manuscript.

No group-classification database or graph package is used.
"""
from itertools import product
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def qmul(a, b):
    u, sa = divmod(a, 2)
    v, sb = divmod(b, 2)
    if u == 0: return 2*v + (sa ^ sb)
    if v == 0: return 2*u + (sa ^ sb)
    if u == v: return sa ^ sb ^ 1
    w = ({1, 2, 3} - {u, v}).pop()
    negative = (u, v) not in [(1,2), (2,3), (3,1)]
    return 2*w + (sa ^ sb ^ negative)

def qinv(a):
    return a if a < 2 else a ^ 1

def qcoords(a, e):
    u, sign = divmod(a, 2)
    return u | (sign << 2) | (e << 3)

def adjacency_q(r, S):
    vertices = list(product(range(8), range(1 << r)))
    E = set()
    for q, e in vertices:
        for p, f in vertices:
            if (qmul(qinv(q), p), e ^ f) in S:
                E.add(tuple(sorted((qcoords(q,e), qcoords(p,f)))))
    return E

def symmetric_orbits(r):
    rem = set(product(range(8),range(1 << r))) - {(0,0)}
    orbits=[]
    while rem:
        q,e=min(rem)
        orb={(q,e),(qinv(q),e)}
        rem -= orb
        orbits.append(orb)
    return orbits

def is_bipartite(n,E):
    adj=[[] for _ in range(n)]
    for x,y in E: adj[x].append(y);adj[y].append(x)
    colors={}
    for root in range(n):
        if root in colors: continue
        colors[root]=0;todo=[root]
        while todo:
            x=todo.pop()
            for y in adj[x]:
                if y in colors:
                    if colors[x]==colors[y]: return False
                else: colors[y]=1-colors[x];todo.append(y)
    return True

def three_color(n,E):
    adj=[set() for _ in range(n)]
    for x,y in E: adj[x].add(y);adj[y].add(x)
    order=sorted(range(n),key=lambda x:-len(adj[x]))
    col={}
    def visit(k):
        if k==n: return [col[x] for x in range(n)]
        x=order[k]
        for c in range(3):
            if all(col.get(y,-1)!=c for y in adj[x]):
                col[x]=c
                ans=visit(k+1)
                if ans is not None:return ans
                del col[x]
        return None
    return visit(0)

assert all(qmul(qmul(a,b),c)==qmul(a,qmul(b,c))
           for a,b,c in product(range(8),repeat=3))
assert all(qmul(a,qinv(a))==0 for a in range(8))
results={"cubelike_orbit_checks":[],"full_inverse_closed_subset_checks":[]}
for r in range(4):
    n=8 << r
    orbits=symmetric_orbits(r)
    for S in orbits:
        T={qcoords(q,e) for q,e in S}
        expected={tuple(sorted((x,x^t))) for x in range(n) for t in T}
        assert adjacency_q(r,S)==expected
    results["cubelike_orbit_checks"].append({"r":r,"order":n,"orbits":len(orbits),"passed":True})
    if r<=1:
        counts={"bipartite":0,"not_three_colorable":0,"three_chromatic":0}
        for mask in range(1 << len(orbits)):
            S=set().union(*(orbits[i] for i in range(len(orbits)) if (mask>>i)&1))
            E=adjacency_q(r,S)
            if is_bipartite(n,E):counts["bipartite"]+=1
            elif three_color(n,E) is None:counts["not_three_colorable"]+=1
            else:counts["three_chromatic"]+=1
        assert counts["three_chromatic"]==0
        results["full_inverse_closed_subset_checks"].append({"r":r,"subsets":1<<len(orbits),**counts})

def dmul(x,y):
    a,b=x%4,x//4;c,d=y%4,y//4
    return (a+(-1 if b else 1)*c)%4 + 4*(b^d)
S=[2,4,5]
E={tuple(sorted((x,dmul(x,s)))) for x in range(8) for s in S}
colors=three_color(8,E)
assert colors is not None and not is_bipartite(8,E)
assert all(colors[x]!=colors[y] for x,y in E)
results["D8_witness"]={"vertices":"r^a s^b encoded a+4b","connection_set":["r^2","s","rs"],"edges":sorted(E),"coloring":colors,"nonbipartite":True}
(ROOT/"finite_verification.json").write_text(json.dumps(results,indent=2)+"\n")
print(json.dumps(results,indent=2))
