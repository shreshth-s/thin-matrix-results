#!/usr/bin/env python3
"""Finite validation of deterministic omission-cover tables.
Does not prove the asymptotic bound; independent integer oracles are used.
"""
from itertools import product, combinations
from functools import lru_cache
from math import comb,prod
from pathlib import Path
import importlib.util, random, sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'outputs'))
p=Path(__file__).resolve().parents[1]/'sub299/round23/check_shifted_private.py'
spec=importlib.util.spec_from_file_location('shift',p)
shift=importlib.util.module_from_spec(spec);spec.loader.exec_module(shift)

@lru_cache(None)
def greedy_cover(d,h):
    words=list(product(range(4),repeat=d))
    neighborhoods=[]
    for o in words:
        mask=0
        for i,x in enumerate(words):
            if sum(u==v for u,v in zip(o,x))<=h:mask|=1<<i
        assert mask.bit_count()==sum(comb(d,j)*3**(d-j) for j in range(h+1))
        neighborhoods.append(mask)
    remaining=(1<<len(words))-1; family=[]; lookup={}
    while remaining:
        i=max(range(len(words)),key=lambda i:(neighborhoods[i]&remaining).bit_count())
        fresh=neighborhoods[i]&remaining
        assert fresh
        family.append(words[i])
        while fresh:
            low=fresh&-fresh;j=low.bit_length()-1
            lookup[words[j]]=words[i];fresh-=low
        remaining&=~neighborhoods[i]
    assert len(lookup)==4**d
    assert all(sum(a==b for a,b in zip(x,o))<=h for x,o in lookup.items())
    return tuple(family),lookup

def cover_variant(array,positions,ell,d,h):
    r=len(positions); blocks=ell//d;free=r-blocks*d
    forms=[shift.NORMAL if n else shift.OPPOSITE for n,p in positions]
    fam,lookup=greedy_cover(d,h)
    tables={};volume=0
    for choice in product(fam,repeat=blocks):
        omit=tuple(y for x in choice for y in x)
        labels=[range(4) if i<free else tuple(j for j in range(4) if j!=omit[i-free]) for i in range(r)]
        table,cells=shift.transform(array,forms,labels)
        assert len(table)==4**free*3**(blocks*d)
        assert cells<=(r+1)*len(table)
        tables[omit]=table;volume+=cells
    return (tables,lookup,d,h,free),volume

def read_variant(bundle,positions,ordinary,ell):
    tables,lookup,d,h,free=bundle
    omit=tuple(y for i in range(free,len(ordinary),d) for y in lookup[tuple(ordinary[i:i+d])])
    choices=[];matches=0
    for index,label in enumerate(ordinary):
        if index<free or label!=omit[index-free]:choices.append(((label,1),))
        else:
            relation=shift.RELATIONS[0 if positions[index][0] else 1]
            choices.append(tuple((j,-relation[j]*relation[label]) for j in range(4) if j!=label));matches+=1
    value=[0]*len(next(iter(tables[omit].values())))
    reads=0
    for terms in product(*choices):
        key=tuple(j for j,c in terms);sign=prod(c for j,c in terms)
        for j,z in enumerate(tables[omit][key]):value[j]+=sign*z
        reads+=1
    assert reads==3**matches
    assert matches<=h*((len(ordinary)-free)//d)
    return tuple(value),reads

def direct(array,positions,word):
    forms=[shift.NORMAL if n else shift.OPPOSITE for n,p in positions]
    result=[0]*len(next(iter(array.values())))
    for raw,value in array.items():
        scale=prod(forms[i][word[i]][x] for i,x in enumerate(raw))
        for j,z in enumerate(value):result[j]+=scale*z
    return tuple(result)

def small_tests():
    rng=random.Random(20261020);count=0
    for d,h,r,ell in ((1,0,3,2),(2,0,4,4),(3,0,4,3),(4,1,4,4),(5,1,5,5)):
        fam,lookup=greedy_cover(d,h)
        pos=[(i%2==0,i) for i in range(r)]
        array={raw:tuple(rng.randrange(-4,5) for _ in range(3)) for raw in product(range(3),repeat=r)}
        bundle,volume=cover_variant(array,pos,ell,d,h)
        words=list(product(range(4),repeat=r))
        if len(words)>300:words=rng.sample(words,300)
        for word in words:
            got,reads=read_variant(bundle,pos,word,ell)
            assert got==direct(array,pos,word);count+=1
        print('PASS cover',dict(d=d,h=h,family=len(fam),universe=4**d,checked=len(words),all_intermediate_cells=volume))
    return count

def box_encoder(array,L,m,side):
    """Independent ordinary/private encoder; no polynomial/channel cache."""
    table={};volumes=[0]*(2*L+1)
    def visit(values,pos,word,counts):
        volumes[pos]+=len(values)
        if pos==2*L:
            table[word]=(values[0],);return
        normal=shift.cache.normal(pos,L,side)
        forms,dim=(shift.NEW_PHI,4) if normal else (shift.cache.PSI,3)
        width=len(values)//dim
        for label in range(5):
            if label==4 and counts[pos//L]>=m:continue
            child=[sum(c*values[i*width+j] for i,c,d in forms[label] if d==0) for j in range(width)]
            new=list(counts);new[pos//L]+=int(label==4)
            visit(child,pos+1,word+(label,),new)
    visit(array,0,(),[0,0])
    U=sum(comb(L,j)*4**(L-j) for j in range(m+1))
    assert len(table)==U**2
    assert all(v<=U**2 for v in volumes)
    return table,sum(volumes)

class SeparateView:
    def __init__(self,selected,ordinary):self.selected,self.ordinary=selected,ordinary
    def __contains__(self,word):return word in self.selected or word in self.ordinary
    def __getitem__(self,word):return self.selected[word] if word in self.selected else self.ordinary[word]

def complete_case(L,m,gamma,delta,cyclic,t,ell,full):
    sources,requests=shift.integration.fixture(L,m,gamma,delta,cyclic,full,240017+L+cyclic+t)
    numerators=[[0]*cyclic for _ in requests]
    stats=dict(source_scans=0,root_cells=0,transform_cells=0,cache_coefficients=0,
               reconstruction_reads=0,normalized=0,distinguished_groups=0,box_encoder_cells=0)
    for run in range(-m,m+1):
        views=[]
        for residue in range(cyclic):
            pair=[]
            for si,side in enumerate(('left','right')):
                source=sources[residue][si]
                dense=shift.integration.dense_source(source,L,run,side)
                canonical=shift.cache.encode(dense,L,m,t,side,shift.cache.new_stats())
                ordinary,cells=box_encoder(dense,L,m,side)
                assert all(value[0]==canonical[word][0] for word,value in ordinary.items())
                stats['box_encoder_cells']+=cells
                wanted={}
                for fixed,inner,_ in requests:
                    for h in range(t):
                        for C in combinations(inner,h):
                            word=list(fixed)
                            for p in inner:word[p]=5 if p in C else 4
                            wanted[tuple(word)]=None
                grouped={};selected={};Qs=[set(),set()]
                for word in wanted:
                    normal,opposite=(word[:L],word[L:]) if side=='left' else (word[L:],word[:L])
                    Qn=tuple(p for p,x in enumerate(normal) if x>=4);Qo=tuple(p for p,x in enumerate(opposite) if x>=4)
                    Cn=tuple(p for p,x in enumerate(normal) if x==5);Co=tuple(p for p,x in enumerate(opposite) if x==5)
                    Qs[0].add(Qn);Qs[1].add(Qo);group=Qn,Qo,Cn,Co
                    if group not in grouped:
                        array,positions,scans=shift.fixed_arrays(source,L,Qn,Qo,Cn,Co,run,side,t)
                        d=min(ell,4);h=int(d==4)
                        tables,cells=cover_variant(array,positions,ell,d,h)
                        grouped[group]=(tables,positions)
                        stats['source_scans']+=scans;stats['root_cells']+=len(array);stats['transform_cells']+=cells
                    tables,positions=grouped[group]
                    labels=tuple((normal if n else opposite)[p] for n,p in positions)
                    value,reads=read_variant(tables,positions,labels,ell)
                    assert value==canonical[word]
                    selected[word]=value;stats['cache_coefficients']+=t;stats['reconstruction_reads']+=reads
                if full:
                    assert len(grouped)==len(Qs[0])*len(Qs[1])*sum(comb(2*m,h) for h in range(t))
                stats['distinguished_groups']+=len(grouped)
                pair.append(SeparateView(selected,ordinary))
            views.append(pair)
        for index,(fixed,inner,_) in enumerate(requests):
            for target,residue in product(range(cyclic),repeat=2):
                numerators[index][target]+=shift.cache.complete_query(views[residue][0],views[(target-residue)%cyclic][1],fixed,inner,L,m,t,shift.cache.new_stats())
    for index,(_,_,expected) in enumerate(requests):
        for target in range(cyclic):
            assert numerators[index][target]%4**L==0
            assert numerators[index][target]//4**L==expected[target]
            stats['normalized']+=1
    return stats

def integration_tests():
    original=shift.cache.PHI;shift.cache.PHI=shift.NEW_PHI
    totals={}
    try:
        for args in ((2,1,(1,1),(1,1),2,2,2,True),
                     (3,2,(1,2,3),(1,1,1),1,2,1,True),
                     (3,1,(1,1,1),(1,2,3),1,2,4,False)):
            out=complete_case(*args)
            for k,v in out.items():totals[k]=totals.get(k,0)+v
            print('PASS complete Walsh/source product',args[:2],out)
    finally:shift.cache.PHI=original
    return totals

if __name__=='__main__':
    print('PASS local shifted identities:',shift.local_checks())
    print('PASS arbitrary signed polynomial reconstructions:',small_tests())
    print('PASS complete-product totals:',integration_tests())
    print('Finite evidence only: no asymptotic proof or complete fast implementation implied.')
