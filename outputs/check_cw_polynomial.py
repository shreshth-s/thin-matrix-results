#!/usr/bin/env python3
"""Independent finite polynomial check; not a rank/exponent proof.

Variables are coefficients of three distinct vector spaces: 0 is the zero
label, 1..q are private labels, q+1 is the terminal label. The polynomial
variable lambda is separate. All operations below are exact integers, hence
also an independent check over Q. No Lean implementation is imported.
"""
def add(a, b):
    return [ (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
             for i in range(max(len(a), len(b))) ]

def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out

def form(label, degree, support):
    p = [0] * (degree+1)
    p[0] = int(label == 0)
    p[degree] = int(label in support)
    return p

def tensor_entry(q, x, y, z):
    # Direct definition of the big CW tensor, independent of the certificate.
    out = 0
    for i in range(1, q+1):
        out += int((x,y,z) in ((0,i,i),(i,0,i),(i,i,0)))
    out += int((x,y,z) in ((0,0,q+1),(0,q+1,0),(q+1,0,0)))
    return out

def certificate(q, x, y, z):
    terms = []
    for i in range(1, q+1):
        terms.append(mul(mul(mul([0,1], form(x,1,{i})), form(y,1,{i})), form(z,1,{i})))
    support = set(range(1, q+1))
    terms.append([-c for c in mul(mul(form(x,2,support), form(y,2,support)), form(z,2,support))])
    support = {q+1}
    terms.append(mul([1,-q], mul(mul(form(x,3,support), form(y,3,support)), form(z,3,support))))
    assert len(terms) == q+2
    p = [0]
    for term in terms:
        p = add(p, term)
    return p

def main():
    checked = 0
    for q in (0,1,2,3,16):
        for x in range(q+2):
            for y in range(q+2):
                for z in range(q+2):
                    p = certificate(q,x,y,z)
                    assert p[:3] == [0,0,0], (q,x,y,z,p)
                    assert p[3] == tensor_entry(q,x,y,z), (q,x,y,z,p)
                    assert all(c == 0 for c in p[11:]), (q,x,y,z,p)
                    checked += 1
        print(f'PASS q={q}: {(q+2)**3} coefficient triples; q+2 rank-one polynomial terms; orders <3 vanish, order 3 equals CW, degree <=10.')
    print(f'PASS: {checked} exact coefficient triples; no floating point, rank/exponent assumptions or external algebra package.')

if __name__ == '__main__':
    main()
