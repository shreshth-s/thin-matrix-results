#!/usr/bin/env python3
"""Exact finite tests for cyclic source partition + grouped sparse selectors.

Checks are finite correctness evidence, not an asymptotic complexity proof.
All root, partial-transform, and duplicated-vector cells are explicitly counted.
The integration oracle uses canonical complete box queries and independently
replaces every requested low-degree cache value with this backend.
"""
from itertools import product, combinations
from math import comb
from pathlib import Path
import importlib.util
import random
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'outputs'))
spec=importlib.util.spec_from_file_location('shifted',ROOT/'work/sub299/round23/check_shifted_private.py')
shifted=importlib.util.module_from_spec(spec)
spec.loader.exec_module(shifted)
integration=shifted.integration
cache=shifted.cache


def addto(a,b,factor=1):
    return tuple(x+factor*y for x,y in zip(a,b))


def build(array,k,ell,budget):
    """Normal axes are first k, opposite axes are the remaining axes.

    Partition is chosen from the raw normal p2 pattern, before any transforms.
    Includes all zero cells in each of k component arrays and all duplicated
    source vectors. Polynomial/vector fibers are carried without truncating.
    """
    assert 1<=ell<=k
    d=len(next(iter(array))); width=len(next(iter(array.values())))
    r=min(ell,budget*ell//k)
    suffix_words=[w for w in product(range(3),repeat=ell) if w.count(2)<=r]
    Js=[J for j in range(r+1) for J in combinations(range(ell),j)]
    s=len(Js)
    assert s==sum(comb(ell,j) for j in range(r+1))
    raw_R=sum(comb(ell,j)*2**(ell-j) for j in range(r+1))
    assert len(suffix_words)==raw_R
    zero=(0,)*width
    comps=[]
    stats=dict(root_cells=len(array),partition_cells=0,transform_cells=0,
               duplicated_cells=0,selector_cells=0,reconstruction_reads=0)
    for start in range(k):
        suffix=tuple((start+j)%k for j in range(ell))
        prefix=tuple(p for p in range(d) if p not in suffix)
        order=prefix+suffix
        initial={a+b:zero for a in product(range(3),repeat=d-ell) for b in suffix_words}
        assert len(initial)==3**(d-ell)*raw_R
        comps.append([order,initial])
        stats['partition_cells']+=len(initial)
    for raw,val in array.items():
        if raw[:k].count(2)>budget:
            assert not any(val),('source cap violated',raw,val,budget)
            continue
        candidates=[j for j,(order,_) in enumerate(comps)
                    if sum(raw[p]==2 for p in order[-ell:])<=r]
        assert candidates,('cyclic averaging failed',raw,k,ell,budget)
        j=candidates[0]
        order,table=comps[j]
        table[tuple(raw[p] for p in order)]=val
    result=[]
    for order,current in comps:
        volume=len(current)
        for axis,p in enumerate(order[:-ell]):
            forms=shifted.NORMAL if p<k else shifted.OPPOSITE
            following={}
            for key in current:
                if key[axis]!=0:
                    continue
                for label in range(4):
                    value=zero
                    for a in range(3):
                        before=current[key[:axis]+(a,)+key[axis+1:]]
                        value=addto(value,before,forms[label][a])
                    following[key[:axis]+(label,)+key[axis+1:]]=value
            current=following
            volume+=len(current)
        assert len(current)==4**(d-ell)*raw_R
        assert volume<=(d-ell+1)*len(current)
        stats['transform_cells']+=volume
        grouped={}
        for prefix in product(range(4),repeat=d-ell):
            for i in product(range(2),repeat=ell):
                vector=[]
                for J in Js:
                    raw=tuple(2 if p in J else i[p] for p in range(ell))
                    sign=(-1)**sum(i[p] for p in J)
                    vector.append(tuple(sign*x for x in current[prefix+raw]))
                grouped[prefix,i]=tuple(vector)
        assert len(grouped)*s==4**(d-ell)*2**ell*s
        assert 2**ell*s>=raw_R
        stats['duplicated_cells']+=len(grouped)*s
        result.append((order,grouped))
    return result,tuple(Js),stats


def read(tables,Js,ordinary):
    ell=len(tables[0][0])-len(next(iter(tables[0][1]))[0])
    width=len(next(iter(tables[0][1].values()))[0])
    out=(0,)*width
    reads=0
    for order,grouped in tables:
        labels=tuple(ordinary[p] for p in order)
        prefix,suffix=labels[:-ell],labels[-ell:]
        i=tuple(a//2 for a in suffix)
        active=set(p for p,a in enumerate(suffix) if a%2==0)
        vector=grouped[prefix,i]
        for J,val in zip(Js,vector):
            if set(J)<=active:
                out=addto(out,val)
                reads+=1
    return out,reads


def dense_eval(array,k,ordinary):
    out=(0,)*len(next(iter(array.values())))
    for raw,val in array.items():
        scale=1
        for p,(a,label) in enumerate(zip(raw,ordinary)):
            scale*=(shifted.NORMAL if p<k else shifted.OPPOSITE)[label][a]
        out=addto(out,val,scale)
    return out


def synthetic_tests():
    rng=random.Random(20261020)
    totals={}
    for k,opposite,ell,budget in [(3,1,2,1),(6,1,4,2),(6,0,3,1)]:
        width=6  # two cyclic residues times three formal coefficients
        roots=[]
        built=[]
        for block in range(3):
            array={raw:tuple(rng.randrange(-8,9) for _ in range(width))
                   if raw[:k].count(2)<=budget else (0,)*width
                   for raw in product(range(3),repeat=k+opposite)}
            roots.append(array)
            tables,Js,stats=build(array,k,ell,budget)
            built.append((tables,Js))
            for name,val in stats.items(): totals[name]=totals.get(name,0)+val
        queries=[tuple(rng.randrange(4) for _ in range(k+opposite)) for j in range(25)]
        for block,(tables,Js) in enumerate(built):
            for ordinary in queries:
                actual,reads=read(tables,Js,ordinary)
                assert actual==dense_eval(roots[block],k,ordinary)
                totals['reconstruction_reads']+=reads
        # A single query group, batched across all blocks and every coefficient.
        # This is literal exact A_g F_g, with independent random data per block.
        for rotation in range(k):
            order,group0=built[0][0][rotation]
            for (prefix,i),_ in list(group0.items())[:7]:
                all_a=list(product(range(2),repeat=ell))
                A=[[int(all(a[p] for p in J)) for J in Js] for a in all_a]
                F=[[built[block][0][rotation][1][prefix,i][j][coef]
                    for block in range(3) for coef in range(width)]
                   for j in range(len(Js))]
                C=[[sum(x*y for x,y in zip(row,col)) for col in zip(*F)] for row in A]
                assert len(C)==2**ell and len(C[0])==3*width
                for ai,a in enumerate(all_a):
                    suffix=tuple(2*i[p]+(0 if a[p] else 1) for p in range(ell))
                    labels=prefix+suffix
                    original=[None]*(k+opposite)
                    for p,label in zip(order,labels): original[p]=label
                    # Check this component alone by its selector expansion.
                    for block in range(3):
                        vec=built[block][0][rotation][1][prefix,i]
                        expected=(0,)*width
                        for J,val in zip(Js,vec):
                            if all(a[p] for p in J): expected=addto(expected,val)
                        assert tuple(C[ai][block*width:(block+1)*width])==expected
                totals['selector_cells']+=len(A)*len(Js)
    return totals


def check_integration(L,m,gamma,delta,cyclic,t,ell,full):
    sources,requests=integration.fixture(L,m,gamma,delta,cyclic,full,590123+L+cyclic+t)
    numerators=[[0]*cyclic for _ in requests]
    stats=dict(source_scans=0,cache_coefficients=0,normalized=0)
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
                grouped={}; selected={}
                for word in wanted:
                    normal,opposite=(word[:L],word[L:]) if side=='left' else (word[L:],word[:L])
                    Qn=tuple(p for p,x in enumerate(normal) if x>=4)
                    Qo=tuple(p for p,x in enumerate(opposite) if x>=4)
                    Cn=tuple(p for p,x in enumerate(normal) if x==5)
                    Co=tuple(p for p,x in enumerate(opposite) if x==5)
                    group=(Qn,Qo,Cn,Co)
                    if group not in grouped:
                        array,positions,scans=shifted.fixed_arrays(source,L,Qn,Qo,Cn,Co,run,side,t)
                        # Stronger per-channel source cap is explicitly checked.
                        tables,Js,cells=build(array,L-m,ell,m-len(Cn))
                        grouped[group]=(tables,Js,positions)
                        stats['source_scans']+=scans
                        for name,val in cells.items(): stats[name]=stats.get(name,0)+val
                    tables,Js,positions=grouped[group]
                    ordinary=tuple((normal if is_normal else opposite)[p] for is_normal,p in positions)
                    value,reads=read(tables,Js,ordinary)
                    assert value==canonical[word],(L,m,run,side,word,value,canonical[word])
                    selected[word]=value
                    stats['cache_coefficients']+=t
                    stats['reconstruction_reads']+=reads
                pair.append(shifted.View(selected,canonical))
            views.append(pair)
        for index,(fixed,inner,_) in enumerate(requests):
            for target,residue in product(range(cyclic),repeat=2):
                numerators[index][target]+=cache.complete_query(
                    views[residue][0],views[(target-residue)%cyclic][1],
                    fixed,inner,L,m,t,cache.new_stats())
    for index,(_,_,expected) in enumerate(requests):
        for target in range(cyclic):
            numerator=numerators[index][target]
            assert numerator%4**L==0
            assert numerator//4**L==expected[target]
            stats['normalized']+=1
    return stats


def main():
    print('PASS local shifted identity:',shifted.local_checks(),flush=True)
    print('PASS arbitrary-root shared-selector tests:',synthetic_tests(),flush=True)
    original=cache.PHI; cache.PHI=shifted.NEW_PHI
    try:
        for args in [(2,1,(1,1),(1,1),2,2,1,True),
                     (3,1,(1,1,1),(1,2,3),1,2,2,False)]:
            print('PASS full original-product integration',args,check_integration(*args),flush=True)
    finally: cache.PHI=original

if __name__=='__main__': main()
