#!/usr/bin/env python3
"""Exact finite oracle for global middle translations and light source caps.

The finite list is ALL F_2^m, not an asymptotically polynomial construction.
The latter needs a separate small-bias theorem. Every gauge translates both
middle coordinates on both matrices; only the normal coordinate is masked.
Complete output numerators are summed over ALL gauge pairs before dividing.
"""
from itertools import combinations, product
from pathlib import Path
from random import Random
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'cropped-source-improvement'))
import check_cropped_opposite_backend as cropped

grouped=cropped.grouped
shifted=cropped.shifted
integration=cropped.integration
embedding=integration.embedding
cache=cropped.cache


def make_fixture(L,m,gamma,delta,cyclic,full=False):
    slots=[Q for Q in combinations(range(L),m)
           if embedding.independent([gamma[i] for i in Q])
           and embedding.independent([delta[i] for i in range(L) if i not in Q])]
    assert len(slots)>1
    width,middle=1<<(L-m),1<<(2*m)
    outer=width*width
    rng=Random(420201+100*L+10*m+cyclic)
    X=[{Q:[[0]*middle for _ in range(outer)] for Q in slots} for _ in range(cyclic)]
    Y=[{Q:[[0]*outer for _ in range(middle)] for Q in slots} for _ in range(cyclic)]
    for Q in slots:
        for row,h in product(range(outer),range(middle)):
            X[rng.randrange(cyclic)][Q][row][h]=rng.randrange(-3,4)
            Y[rng.randrange(cyclic)][Q][h][row]=rng.randrange(-3,4)
    requests=[]
    for qi,QL in enumerate(slots):
        for ri,QR in enumerate(slots):
            entries=product(range(outer),repeat=2) if full else [((3*qi+ri)%outer,(qi+2*ri)%outer)]
            for row,col in entries:
                xl,vl=divmod(row,width); vr,xr=divmod(col,width)
                fixed=embedding.output_word(QL,QR,xl,vl,vr,xr,L,delta)
                positions=QL+tuple(L+p for p in QR)
                expected=[sum(X[r][QL][row][h]*Y[(target-r)%cyclic][QR][h][col]
                              for r in range(cyclic) for h in range(middle))
                          for target in range(cyclic)]
                requests.append((QL,QR,row,col,fixed,positions,expected))
    return slots,X,Y,requests


def choices_for(slots,gamma,m,cap):
    inverses={}
    for Q in slots:
        inverse={embedding.linear_map(gamma,{Q[j] for j in range(m) if mask>>j&1}):mask
                 for mask in range(1<<m)}
        assert len(inverse)==1<<m
        inverses[Q]=inverse
    S=tuple(range(1<<m))
    chosen={Q:{h:next(d for d in S if inverses[Q][h^d].bit_count()<=cap)
               for h in range(1<<m)} for Q in slots}
    assert len({d for row in chosen.values() for d in row.values()})>1
    if m>=2:
        assert any(chosen[Q][h]!=chosen[R][h] for Q in slots for R in slots for h in S), \
            'Fixture must exercise good-set-dependent gauge choices.'
    return S,chosen,inverses


def translate_pair(X,Y,slots,chosen,m,d1,d2):
    cyclic=len(X); middle=1<<(2*m); half=1<<m
    outer=len(X[0][slots[0]])
    XX=[{Q:[[0]*middle for _ in range(outer)] for Q in slots} for _ in range(cyclic)]
    YY=[{Q:[[0]*outer for _ in range(middle)] for Q in slots} for _ in range(cyclic)]
    for r,Q,hprime in product(range(cyclic),slots,range(middle)):
        h1p,h2p=divmod(hprime,half)
        h1,h2=h1p^d1,h2p^d2
        h=h1*half+h2
        if chosen[Q][h1]==d1:
            for row in range(outer): XX[r][Q][row][hprime]=X[r][Q][row][h]
        if chosen[Q][h2]==d2:
            for col in range(outer): YY[r][Q][hprime][col]=Y[r][Q][h][col]
    return XX,YY


def check_source_caps(XX,YY,L,m,gamma,delta,slots,cap,stats):
    sources=[]
    for residue in range(len(XX)):
        xhat,yhat=embedding.walsh_inputs(XX[residue],YY[residue],slots,L-m,1<<(2*m))
        pair=[]
        for side,matrix in [('left',xhat),('right',yhat)]:
            src=embedding.source_arrays(matrix,L,m,gamma,delta,slots,side)
            for word,(_,value) in src.items():
                normal=word[:L] if side=='left' else word[L:]
                assert not value or normal.count(3)<=cap,('normal cap',side,normal,value,cap)
                stats['source_entries']+=1
                stats['nonzero_source_entries']+=bool(value)
            cut=cropped.crop(src,L,cap,side)
            stats['cropped_nonzero_entries']+=sum(bool(value) for word,(_,value) in src.items() if word not in cut)
            assert all(not value or (word[L:] if side=='left' else word[:L]).count(2)<=cap
                       for word,(_,value) in cut.items())
            pair.append(cut)
        sources.append(pair)
    return sources


def light_view(source,L,m,cap,t,run,side,requests,stats):
    dense=integration.dense_source(source,L,run,side)
    canonical=cache.encode(dense,L,m,t,side,stats)
    wanted={}
    for _,_,_,_,fixed,inner,_ in requests:
        for h in range(t):
            for C in combinations(inner,h):
                w=list(fixed)
                for p in inner:w[p]=cache.CHANNEL if p in C else cache.PRIVATE
                wanted[tuple(w)]=None
    memo={};selected={}
    for word in wanted:
        normal,opposite=(word[:L],word[L:]) if side=='left' else (word[L:],word[:L])
        Qn=tuple(p for p,x in enumerate(normal) if x>=4);Qo=tuple(p for p,x in enumerate(opposite) if x>=4)
        Cn=tuple(p for p,x in enumerate(normal) if x==5);Co=tuple(p for p,x in enumerate(opposite) if x==5)
        key=(Qn,Qo,Cn,Co);use_opp=len(Co)>len(Cn)
        if key not in memo:
            array,positions,scans=shifted.fixed_arrays(source,L,Qn,Qo,Cn,Co,run,side,t)
            k=L-m
            assert all(not any(v) or raw[:k].count(2)<=cap-len(Cn) for raw,v in array.items())
            assert all(not any(v) or raw[k:].count(2)<=cap-len(Co) for raw,v in array.items())
            budget=cap-max(len(Cn),len(Co))
            if budget<0:
                assert all(not any(v) for v in array.values())
                memo[key]=(None,None,positions)
                stats['forced_zero_roots']+=1
            else:
                if use_opp:
                    array,_=cropped.opposite_forward(array,k)
                    old=shifted.OPPOSITE;shifted.OPPOSITE=shifted.NORMAL
                    try:tables,Js,counts=grouped.build(array,k,k,budget)
                    finally:shifted.OPPOSITE=old
                    stats['opposite_grouped_roots']+=1
                else:
                    tables,Js,counts=grouped.build(array,k,k,budget)
                    stats['normal_grouped_roots']+=1
                memo[key]=(tables,Js,positions)
            stats['root_groups']+=1
            stats['root_source_scans']+=scans
        tables,Js,positions=memo[key]
        ordinary=tuple((normal if isn else opposite)[p] for isn,p in positions)
        if tables is None:value=(0,)*t
        else:
            if use_opp:
                k=L-m;mapping=(1,3,0,2)
                ordinary=tuple(mapping[x] for x in ordinary[k:])+ordinary[:k]
            value,_=grouped.read(tables,Js,ordinary)
        assert value==canonical[word],('light grouped residual',side,run,word,value,canonical[word])
        selected[word]=value
        stats['grouped_residual_values']+=1
    return shifted.View(selected,canonical)


def check_case(L,m,gamma,delta,cyclic,complete=False,t=2,full=False):
    cap=m//2
    slots,X,Y,requests=make_fixture(L,m,gamma,delta,cyclic,full)
    S,chosen,inverses=choices_for(slots,gamma,m,cap)
    stats=cache.new_stats()
    for key in ('source_entries','nonzero_source_entries','cropped_nonzero_entries',
                'gauge_pairs','normalized','direct_coefficients','root_groups','root_source_scans',
                'forced_zero_roots','normal_grouped_roots','opposite_grouped_roots','grouped_residual_values'):
        stats[key]=0
    direct=[[0]*cyclic for _ in requests]
    numerators=[[0]*cyclic for _ in requests]
    for d1,d2 in product(S,repeat=2):
        XX,YY=translate_pair(X,Y,slots,chosen,m,d1,d2)
        sources=check_source_caps(XX,YY,L,m,gamma,delta,slots,cap,stats)
        for qi,(QL,QR,row,col,_,_,_) in enumerate(requests):
            for target in range(cyclic):
                direct[qi][target]+=sum(XX[r][QL][row][h]*YY[(target-r)%cyclic][QR][h][col]
                                       for r in range(cyclic) for h in range(1<<(2*m)))
        if complete:
            # Crop is already applied globally to BOTH inputs before every encoder.
            for run in range(-m,m+1):
                views=[[light_view(sources[r][si],L,m,cap,t,run,side,requests,stats)
                        for si,side in enumerate(('left','right'))] for r in range(cyclic)]
                for qi,(_,_,_,_,fixed,inner,_) in enumerate(requests):
                    for target,r in product(range(cyclic),repeat=2):
                        numerators[qi][target]+=cache.complete_query(views[r][0],views[(target-r)%cyclic][1],
                                                                   fixed,inner,L,m,t,stats)
                        stats['queries']+=1
        stats['gauge_pairs']+=1
    for qi,(_,_,_,_,_,_,expected) in enumerate(requests):
        assert direct[qi]==expected,('original product decomposition',qi,direct[qi],expected)
        stats['direct_coefficients']+=cyclic
        if complete:
            for target in range(cyclic):
                numerator=numerators[qi][target]
                assert numerator%4**L==0
                assert numerator//4**L==expected[target],('complete gauge sum',qi,target,numerator,expected[target])
                stats['normalized']+=1
    assert stats['cropped_nonzero_entries']>0
    if complete and m>=2:
        assert stats['normal_grouped_roots']>0 and stats['opposite_grouped_roots']>0
        assert stats['box_reads']>0 and stats['residual_keys']>0
    return dict(L=L,m=m,cap=cap,cyclic=cyclic,good_sets=len(slots),translation_list=len(S),**stats)


def main():
    original=cache.PHI;cache.PHI=shifted.NEW_PHI
    try:
        for args in [(2,1,(1,1),(1,1),2,True,2,True),
                     (3,2,(1,2,3),(1,1,1),1,True,3,False),
                     (4,3,(1,2,4,7),(1,1,1,1),1,False,2,False)]:
            print('PASS global light-source gauges',check_case(*args),flush=True)
    finally:cache.PHI=original
    print('Finite list is full F_2^m. Polynomial-size small-bias construction is a separate asymptotic proof.')

if __name__=='__main__':main()
