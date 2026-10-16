"""Exact integer validation of proposed support-pruned encodings."""
import itertools, math, random

PHI=[[(0,1),(3,1)],[(0,1),(4,1)],[(0,1)],
     [(1,1),(5,1)],[(1,1),(6,1)],[(1,1)],
     [(2,1),(3,-1),(5,-1)],[(2,1),(4,-1),(6,-1)],[(2,1)],
     [(0,-1),(1,-1),(2,-1)]]
PSI=[[(0,1),(3,1)],[(1,1),(4,1)],[(2,1),(3,-1),(4,-1)],
     [(0,1),(5,1)],[(1,1),(6,1)],[(2,1),(5,-1),(6,-1)],
     [(0,1)],[(1,1)],[(2,1)],[(0,1),(1,1),(2,1)]]

def encode(arr,L,forms,budget):
    out={}
    def rec(a,h,path,zeros):
        if h==0:
            out[path]=a[0]
            return
        size=7**(h-1)
        for label, form in enumerate(forms):
            nz=zeros+(label==9)
            if nz>budget:continue
            b=[sum(coeff*a[s*size+j] for s,coeff in form) for j in range(size)]
            rec(b,h-1,path+(label,),nz)
    rec(arr,L,(),0)
    return out

def index(s,base=7):
    out=0
    for j in s:out=base*out+j
    return out

def verify():
    rng=random.Random(20261013)
    tested=0
    for L in range(1,5):
      for m in range(L+1):
       a=[rng.randrange(-10,11) for _ in range(7**L)]
       for forms in (PHI,PSI):
        full=encode(a,L,forms,L)
        got=encode(a,L,forms,m)
        expected={t:v for t,v in full.items() if t.count(9)<=m}
        assert got==expected
        S=sum(math.comb(L,j)*9**(L-j) for j in range(m+1))
        assert len(got)==S
        work=sum(sum(math.comb(k,j)*9**(k-j) for j in range(min(k,m)+1))*7**(L-k) for k in range(L+1))
        assert 2*work<=9*S # geometric series bound
        tested+=1
    # End-to-end decoded matrix entries with all equal-weight products active.
    for L,m in [(2,1),(3,1),(3,2),(4,1)]:
      strs=list(itertools.product(range(7),repeat=L))
      a=[rng.randrange(-3,4) if sum(v>=3 for v in s)==m else 0 for s in strs]
      b=[rng.randrange(-3,4) if sum(v>=3 for v in s)==m else 0 for s in strs]
      A=encode(a,L,PHI,m);B=encode(b,L,PSI,m)
      for Q in itertools.combinations(range(L),m):
       for outer in itertools.product(range(9),repeat=L-m):
        it=iter(outer)
        output=[9 if k in Q else next(it) for k in range(L)]
        total=0
        for free in itertools.product(range(10),repeat=m):
         t=output.copy()
         for pos,value in zip(Q,free):t[pos]=value
         tt=tuple(t)
         total+=A[tt]*B[tt]
        expected=0
        for inner in itertools.product(range(4),repeat=m):
         u=[v//3 if v!=9 else 0 for v in output]
         v=[w%3 if w!=9 else 0 for w in output]
         for pos,value in zip(Q,inner):u[pos]=v[pos]=value+3
         expected+=a[index(u)]*b[index(v)]
        assert total==expected,(L,m,Q,output,total,expected)
        tested+=1
    print('PASS:',tested,'exact integer cases; full/pruned encodings, leaf counts, cost bound, and decoded matrix entries match.')

if __name__=='__main__': verify()
