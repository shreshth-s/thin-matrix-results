#!/usr/bin/env python3
"""Changed private factor, distinguished-first sources, and ordinary bases.

Exact finite oracles check the full original-input embedding and complete
residual-plus-box outputs. No asymptotic APSP improvement is asserted.
"""
from itertools import combinations, product
from math import prod
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[3]/'outputs'))
import check_five_term_aligned_integration as integration

cache = integration.query
embedding = integration.embedding

# Moving p1 out of the two ordinary forms leaves their x coefficients
# unchanged. P=(-x1-x2+p1)(2s), H(z)=-x1-x2+(1+z)p1.
NEW_PHI = (((0,1,0),(3,1,0)), ((0,1,0),),
           ((1,1,0),(3,-1,0)), ((1,1,0),),
           ((0,-1,0),(1,-1,0),(2,1,0),(2,1,1)), ((3,1,0),))
NORMAL = ((1,0,1),(1,0,0),(0,1,-1),(0,1,0))
OPPOSITE = ((1,1,0),(1,-1,0),(1,1,-1),(1,-1,1))
RELATIONS = ((1,-1,1,-1),(1,1,-1,-1))


def local_checks():
    result = [[0]*3 for _ in range(4)]
    for left,right in zip(NEW_PHI[:5],cache.PSI[:5]):
        for i,a,degree in left:
            if degree:
                continue
            for j,b,_ in right:
                result[i][j] += a*b
    assert result == [[0,0,0],[0,0,0],[2,0,0],[0,0,1]]
    for forms,relation in zip((NORMAL,OPPOSITE),RELATIONS):
        assert all(sum(relation[i]*forms[i][j] for i in range(4))==0 for j in range(3))
        for omit in range(4):
            basis=[i for i in range(4) if i!=omit]
            a,b,c=[forms[i] for i in basis]
            determinant = (a[0]*(b[1]*c[2]-b[2]*c[1])
                           -a[1]*(b[0]*c[2]-b[2]*c[0])
                           +a[2]*(b[0]*c[1]-b[1]*c[0]))
            assert determinant != 0
    return 11


def fixed_arrays(source,L,Qnormal,Qopposite,Cnormal,Copposite,run,side,t):
    """Contract the distinguished positions first; crop outside p1.

    Only 3**(2*(L-m)) remaining cells are written. Direct source scans
    (including implicit zeros) are explicitly counted. Both H degrees are
    retained in the polynomial coefficients; channel z weights are external.
    """
    normal_out=[p for p in range(L) if p not in Qnormal]
    opposite_out=[p for p in range(L) if p not in Qopposite]
    positions=[(True,p) for p in normal_out]+[(False,p) for p in opposite_out]
    opposite_base=[0]*L
    for p in Copposite:
        opposite_base[p]=2
    opposite_scale=2**(len(Qopposite)-len(Copposite))
    forms=[NEW_PHI[cache.CHANNEL if p in Cnormal else cache.PRIVATE] for p in Qnormal]
    # Combine the two polynomial terms reading raw p1, rather than treating
    # them as separate source accesses.
    supported=[sorted({i for i,c,d in form}) for form in forms]
    array,scans={},0
    for raw in product(range(3),repeat=len(positions)):
        normal=[0]*L
        opposite=opposite_base.copy()
        for (is_normal,p),coordinate in zip(positions,raw):
            if is_normal:
                normal[p]=(0,1,3)[coordinate]
            else:
                opposite[p]=coordinate
        value=[0]*t
        for choices in product(*supported):
            polynomial=[1]+[0]*(t-1)
            for p,form,coordinate in zip(Qnormal,forms,choices):
                normal[p]=coordinate
                factor=[0]*t
                for i,c,d in form:
                    if i==coordinate and d<t:
                        factor[d]+=c
                polynomial=list(cache.multiply_truncated(polynomial,factor,t))
            physical=tuple(normal+opposite if side=='left' else opposite+normal)
            pair=source.get(physical)
            scalar=pair[1] if pair is not None and pair[0]==run else 0
            for j,c in enumerate(polynomial):
                value[j]+=opposite_scale*scalar*c
            scans+=1
        array[raw]=tuple(value)
    assert len(array)==3**len(positions)
    assert scans==3**(len(positions)+len(Qnormal)-len(Cnormal))
    return array,positions,scans


def transform(array,forms_by_axis,labels_by_axis):
    """Successive small transforms, charging every complete layer."""
    current=array
    volume=len(array)
    for axis,(forms,labels) in enumerate(zip(forms_by_axis,labels_by_axis)):
        following={}
        for key in current:
            if key[axis] != 0:
                continue
            for label in labels:
                vector=[0]*len(current[key])
                for raw in range(3):
                    before=current[key[:axis]+(raw,)+key[axis+1:]]
                    for j,x in enumerate(before):
                        vector[j]+=forms[label][raw]*x
                following[key[:axis]+(label,)+key[axis+1:]]=tuple(vector)
        current=following
        volume+=len(current)
    return current,volume


def partial_variants(array,positions,ell):
    r=len(positions)
    assert 0<=ell<=r
    forms=[NORMAL if normal else OPPOSITE for normal,p in positions]
    tables=[]
    volume=0
    for omitted in range(4):
        choices=[range(4) if i<r-ell else [j for j in range(4) if j!=omitted]
                 for i in range(r)]
        table,cells=transform(array,forms,choices)
        assert len(table)==4**(r-ell)*3**ell
        assert cells<=(r+1)*4**(r-ell)*3**ell
        tables.append(table)
        volume+=cells
    return tables,volume


def reconstruct(tables,positions,ordinary,ell):
    r=len(ordinary)
    prefix,suffix=ordinary[:r-ell],ordinary[r-ell:]
    omitted=min(range(4),key=suffix.count)
    choices=[]
    for index,label in enumerate(ordinary):
        if index<r-ell or label!=omitted:
            choices.append(((label,1),))
        else:
            relation=RELATIONS[0 if positions[index][0] else 1]
            choices.append(tuple((j,-relation[j]*relation[omitted])
                                 for j in range(4) if j!=omitted))
    value=[0]*len(next(iter(tables[omitted].values())))
    reads=0
    for terms in product(*choices):
        key=tuple(j for j,c in terms)
        scale=prod(c for j,c in terms)
        for degree,x in enumerate(tables[omitted][key]):
            value[degree]+=scale*x
        reads+=1
    assert reads==3**suffix.count(omitted)
    assert reads<=3**(ell//4)
    return tuple(value),reads


class View:
    def __init__(self,selected,canonical):
        self.selected,self.canonical=selected,canonical

    def __contains__(self,word):
        return word in self.canonical

    def __getitem__(self,word):
        return self.selected[word] if word in self.selected else self.canonical[word]


def check_case(L,m,gamma,delta,cyclic,t,ell,full):
    sources,requests=integration.fixture(L,m,gamma,delta,cyclic,full,230017+L+cyclic+t)
    numerators=[[0]*cyclic for _ in requests]
    stats=dict(source_scans=0,root_cells=0,transform_cells=0,cache_coefficients=0,
               reconstruction_reads=0,normalized=0)
    for run in range(-m,m+1):
        views=[]
        for residue in range(cyclic):
            pair=[]
            for side_index,side in enumerate(('left','right')):
                source=sources[residue][side_index]
                dense=integration.dense_source(source,L,run,side)
                canonical=cache.encode(dense,L,m,t,side,cache.new_stats())
                wanted={}
                for fixed,inner,_ in requests:
                    for h in range(t):
                        for C in combinations(inner,h):
                            word=list(fixed)
                            for p in inner:
                                word[p]=cache.CHANNEL if p in C else cache.PRIVATE
                            wanted[tuple(word)]=None
                grouped={}
                selected={}
                for word in wanted:
                    normal,opposite=(word[:L],word[L:]) if side=='left' else (word[L:],word[:L])
                    Qn=tuple(p for p,x in enumerate(normal) if x>=4)
                    Qo=tuple(p for p,x in enumerate(opposite) if x>=4)
                    Cn=tuple(p for p,x in enumerate(normal) if x==5)
                    Co=tuple(p for p,x in enumerate(opposite) if x==5)
                    group=(Qn,Qo,Cn,Co)
                    if group not in grouped:
                        array,positions,scans=fixed_arrays(source,L,Qn,Qo,Cn,Co,run,side,t)
                        tables,cells=partial_variants(array,positions,ell)
                        grouped[group]=(tables,positions)
                        stats['source_scans']+=scans
                        stats['root_cells']+=len(array)
                        stats['transform_cells']+=cells
                    tables,positions=grouped[group]
                    ordinary=tuple((normal if is_normal else opposite)[p]
                                   for is_normal,p in positions)
                    value,reads=reconstruct(tables,positions,ordinary,ell)
                    assert value==canonical[word]
                    selected[word]=value
                    stats['cache_coefficients']+=t
                    stats['reconstruction_reads']+=reads
                pair.append(View(selected,canonical))
            views.append(pair)
        for index,(fixed,inner,_) in enumerate(requests):
            for target,residue in product(range(cyclic),repeat=2):
                numerators[index][target]+=cache.complete_query(
                    views[residue][0],views[(target-residue)%cyclic][1],
                    fixed,inner,L,m,t,cache.new_stats())
    for index,(_,_,expected) in enumerate(requests):
        for target in range(cyclic):
            numerator=numerators[index][target]
            assert numerator % 4**L==0
            assert numerator//4**L==expected[target]
            stats['normalized']+=1
    return stats


def main():
    print('PASS local identity and ordinary-basis rank/relations:',local_checks())
    original=cache.PHI
    cache.PHI=NEW_PHI
    totals={}
    try:
        for args in ((2,1,(1,1),(1,1),2,2,2,True),
                     (3,2,(1,2,3),(1,1,1),1,2,1,True),
                     (3,1,(1,1,1),(1,2,3),1,2,4,False)):
            result=check_case(*args)
            print(f'PASS L={args[0]}, m={args[1]}, q={args[4]}, ell={args[6]}: {result}')
            for key,value in result.items():
                totals[key]=totals.get(key,0)+value
    finally:
        cache.PHI=original
    print('PASS totals:',totals)
    print('Original Walsh sources, both orientations, complete formal/cyclic coefficients, and 4^L normalization retained.')
    print('High boxes are a canonical-style finite oracle with the changed identity; no faster APSP bound is asserted.')


if __name__=='__main__':
    main()
