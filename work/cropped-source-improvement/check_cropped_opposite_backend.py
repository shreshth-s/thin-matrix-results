#!/usr/bin/env python3
"""Crop opposite w>m globally, then check COMPLETE original products.

Also reconstruct every needed residual cache through whichever half has more
channel letters. Opposite grouping uses an integer forward evaluation map,
never a rational inverse. Individual cropped caches are checked only against
the cropped dense oracle, not against uncropped residual values.
"""
from itertools import product,combinations
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'structured-source-improvement'))
import check_grouped_sparse_backend as grouped
shifted=grouped.shifted
integration=grouped.integration
cache=grouped.cache


def crop(source,L,m,side):
    return {key:val for key,val in source.items()
            if (key[L:] if side=='left' else key[:L]).count(2)<=m}


def opposite_forward(array,k):
    """Map every opposite axis to (y1=s+v,y2=s-v,-w), then put it first."""
    current=array
    forms=((1,1,0),(1,-1,0),(0,0,-1))
    cells=len(current)
    for axis in range(k,2*k):
        following={}
        for key in current:
            if key[axis]!=0: continue
            for label in range(3):
                val=(0,)*len(current[key])
                for raw in range(3):
                    val=grouped.addto(val,current[key[:axis]+(raw,)+key[axis+1:]],forms[label][raw])
                following[key[:axis]+(label,)+key[axis+1:]]=val
        current=following; cells+=len(current)
    assert cells==(k+1)*len(array)
    return {key[k:]+key[:k]:val for key,val in current.items()},cells


def check_case(L,m,gamma,delta,cyclic,t,ell,full):
    raw_sources,requests=integration.fixture(L,m,gamma,delta,cyclic,full,381029+L+cyclic+t)
    sources=[]
    stats=dict(cropped_source_entries=0,source_entries=0,normalized=0,
               normal_groups=0,opposite_groups=0,forward_cells=0,
               residual_values=0,source_scans=0)
    for pair in raw_sources:
        nextpair=[]
        for idx,side in enumerate(('left','right')):
            src=crop(pair[idx],L,m,side)
            stats['source_entries']+=len(pair[idx])
            stats['cropped_source_entries']+=len(pair[idx])-len(src)
            nextpair.append(src)
        sources.append(nextpair)
    numerators=[[0]*cyclic for _ in requests]
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
                            for p in inner: word[p]=cache.CHANNEL if p in C else cache.PRIVATE
                            wanted[tuple(word)]=None
                memo={}; selected={}
                for word in wanted:
                    normal,opposite=(word[:L],word[L:]) if side=='left' else (word[L:],word[:L])
                    Qn=tuple(p for p,x in enumerate(normal) if x>=4)
                    Qo=tuple(p for p,x in enumerate(opposite) if x>=4)
                    Cn=tuple(p for p,x in enumerate(normal) if x==5)
                    Co=tuple(p for p,x in enumerate(opposite) if x==5)
                    key=(Qn,Qo,Cn,Co)
                    use_opp=len(Co)>len(Cn)
                    if key not in memo:
                        array,positions,scans=shifted.fixed_arrays(source,L,Qn,Qo,Cn,Co,run,side,t)
                        k=L-m
                        used_ell=ell(L,m,max(len(Cn),len(Co))) if callable(ell) else ell
                        assert all(not any(val) or raw[:k].count(2)<=m-len(Cn) for raw,val in array.items())
                        assert all(not any(val) or raw[k:].count(2)<=m-len(Co) for raw,val in array.items())
                        if use_opp:
                            array,cells=opposite_forward(array,k)
                            stats['forward_cells']+=cells
                            old=shifted.OPPOSITE
                            shifted.OPPOSITE=shifted.NORMAL
                            try:
                                tables,Js,counts=grouped.build(array,k,used_ell,m-len(Co))
                            finally: shifted.OPPOSITE=old
                            stats['opposite_groups']+=1
                        else:
                            tables,Js,counts=grouped.build(array,k,used_ell,m-len(Cn))
                            stats['normal_groups']+=1
                        memo[key]=(tables,Js,positions)
                        stats['source_scans']+=scans
                        for name,val in counts.items(): stats[name]=stats.get(name,0)+val
                    tables,Js,positions=memo[key]
                    ordinary=tuple((normal if is_normal else opposite)[p] for is_normal,p in positions)
                    if use_opp:
                        k=L-m
                        mapping=(1,3,0,2)
                        ordinary=tuple(mapping[x] for x in ordinary[k:])+ordinary[:k]
                    actual,reads=grouped.read(tables,Js,ordinary)
                    assert actual==canonical[word],('cropped cache',L,m,run,side,use_opp,word,actual,canonical[word])
                    selected[word]=actual
                    stats['residual_values']+=1
                    stats['reconstruction_reads']+=reads
                pair.append(shifted.View(selected,canonical))
            views.append(pair)
        for index,(fixed,inner,_) in enumerate(requests):
            for target,residue in product(range(cyclic),repeat=2):
                numerators[index][target]+=cache.complete_query(
                    views[residue][0],views[(target-residue)%cyclic][1],fixed,inner,L,m,t,cache.new_stats())
    for index,(_,_,expected) in enumerate(requests):
        for target in range(cyclic):
            numerator=numerators[index][target]
            assert numerator%4**L==0
            assert numerator//4**L==expected[target],('complete original product',L,m,index,target,numerator,expected[target])
            stats['normalized']+=1
    assert stats['cropped_source_entries']>0
    assert stats['opposite_groups']>0
    return stats


def main():
    original=cache.PHI;cache.PHI=shifted.NEW_PHI
    try:
        for args in [(2,1,(1,1),(1,1),3,2,1,True),
                     (3,1,(1,1,1),(1,2,3),2,2,2,False),
                     (3,2,(1,2,3),(1,1,1),1,3,1,False)]:
            print('PASS cropped complete products and selected-half grouping',args,check_case(*args),flush=True)
    finally: cache.PHI=original

if __name__=='__main__':main()
