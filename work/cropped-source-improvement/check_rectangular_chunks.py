#!/usr/bin/env python3
"""Exact ceiling/padding interface test, NOT a fast multiplication implementation."""
from fractions import Fraction
from random import Random

def ceil_power(s,a):
    # Small exact integer arithmetic, no floating ceil at a boundary.
    target=s**a.numerator
    out=1
    while out**a.denominator<target:out+=1
    return out

def run():
    rng=Random(20261020);cases=products=entries=0
    for s,a,k in [(2,Fraction(3,2),2),(3,Fraction(3,2),2),(4,Fraction(3,2),2),(2,Fraction(5,2),3)]:
        nr,nc=ceil_power(s,a),s**k
        for rows in [0,1,nr,nr+1,2*nr+1]:
            for cols in [nc,nc+1,2*nc-1]:
                A=[[rng.randrange(-9,10) for _ in range(s)] for _ in range(rows)]
                F=[[rng.randrange(-9,10) for _ in range(cols)] for _ in range(s)]
                expected=[[sum(A[i][l]*F[l][j] for l in range(s)) for j in range(cols)] for i in range(rows)]
                result=[[0]*cols for _ in range(rows)];count=0
                for i0 in range(0,rows,nr):
                    for j0 in range(0,cols,nc):
                        Ap=[A[i0+i] if i0+i<rows else [0]*s for i in range(nr)]
                        Fp=[[F[l][j0+j] if j0+j<cols else 0 for j in range(nc)] for l in range(s)]
                        C=[[sum(Ap[i][l]*Fp[l][j] for l in range(s)) for j in range(nc)] for i in range(nr)]
                        for i in range(min(nr,rows-i0)):
                            for j in range(min(nc,cols-j0)):result[i0+i][j0+j]=C[i][j]
                        count+=1;entries+=nr*s+s*nc+nr*nc
                assert result==expected
                assert count==((rows+nr-1)//nr)*((cols+nc-1)//nc)
                assert count<=2*(1+Fraction(rows,nr))*Fraction(cols,nc)
                cases+=1;products+=count
    print('PASS exact rational row ceilings and padded shared products:',cases,'cases,',products,'products,',entries,'explicit padded entries')
    print('Finite algebra only; the fast-MM exponent remains an external theorem dependency.')
if __name__=='__main__':run()
