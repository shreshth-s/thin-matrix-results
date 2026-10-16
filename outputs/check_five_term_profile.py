"""Complete fixed-profile queries, from original arrays and restricted tables.

Standard library only.  This validates the algebraic query for arbitrary input
arrays; it does not reproduce the separate good-set/full-grid embedding theorem
or implement the complete APSP algorithm.  No full ordinary encoding is built.
Product-and-filter enumeration below is a finite oracle only: the asymptotic
algorithm must generate the truncated grids directly, as the lemma requires.
"""
from functools import lru_cache
from itertools import combinations, product
from math import comb
import random

PHI = (((0,1),(2,1)), ((0,1),(3,-1)), ((1,1),),
       ((1,1),(3,1)), ((0,-1),(1,-1)))
PSI = (((0,1),), ((1,1),), ((0,1),(2,-1)),
       ((1,1),(2,1)), ((0,1),(1,1)))
P, NEW1, NEW2, STAR = 4, 5, 6, 7
S_NORMAL = {'z':((P,1),), 'a':((0,1),(P,1),(2,1)),
            'b':((3,1),(2,-1))}
S_OPPOSITE = {'z':((P,1),), 'a':((0,1),), 'b':((0,1),(2,-1))}
PRE_NORMAL = {'a':((NEW1,1),), 'b':((NEW2,1),)}
PRE_OPPOSITE = {'a':((0,1),), 'b':((0,1),(2,-1))}


def normal(pos,L,side):
    return (pos<L)==(side=='left')


def restricted_encode(array,L,Lpre,m,ell,t,side,augmented):
    """Build only one of the two permitted tables, charging internal arrays."""
    table={}; volume=[0]*(2*L+1)
    def visit(values,pos,word,new,zeros):
        volume[pos]+=len(values)
        if pos==2*L:
            table[word]=values[0]
            return
        is_normal=normal(pos,L,side)
        forms=PHI if is_normal else PSI
        dimension=4 if is_normal else 3
        width=len(values)//dimension
        choices={j:forms[j] for j in range(4)}
        if augmented:
            if pos%L<Lpre:
                if is_normal and new<ell:
                    choices[NEW1]=((2,1),)
                    choices[NEW2]=((3,1),)
            elif zeros[pos//L]<m-ell:
                choices[P]=forms[P]
        elif zeros[pos//L]<m and sum(zeros)<2*m-t:
            choices[P]=forms[P]
        for label,form in choices.items():
            next_zeros=list(zeros)
            next_zeros[pos//L]+=label==P
            child=[sum(coefficient*values[index*width+j]
                       for index,coefficient in form) for j in range(width)]
            visit(child,pos+1,word+(label,),new+(label in (NEW1,NEW2)),next_zeros)
    visit(array,0,(),0,[0,0])
    # Every prefix has all four ordinary extensions.  Dimensions are at most4.
    assert all(v<=len(table) for v in volume)
    assert sum(volume)<=(2*L+1)*len(table)
    if augmented:
        prefix=sum(comb(Lpre,j)*2**j*4**(Lpre-j) for j in range(min(ell,Lpre)+1))
        suffix=sum(comb(L-Lpre,j)*4**(L-Lpre-j) for j in range(m-ell+1))
        expected=prefix*4**Lpre*suffix**2
    else:
        expected=sum(comb(L,a)*comb(L,b)*4**(2*L-a-b)
                     for a in range(m+1) for b in range(m+1) if a+b<=2*m-t)
    assert len(table)==expected
    return table


def accepted_profile_leaf(word,L,Lpre,m,ell,side):
    new=0; zeros=[0,0]
    for pos,label in enumerate(word):
        if label in (NEW1,NEW2):
            if not normal(pos,L,side) or pos%L>=Lpre:return False
            new+=1
        elif label==P:
            if pos%L<Lpre:return False
            zeros[pos//L]+=1
        elif not 0<=label<4:return False
    return new<=ell and max(zeros)<=m-ell


def projected(table,fixed,inner,prefix,L,Lpre,m,ell,t,side,stats):
    """Finite grid oracle; asserts the states a pruned implementation visits."""
    transforms=[]; dimensions=[]; zero=[]; suffix=[]
    for axis,pos in enumerate(inner):
        pre=pos in prefix; is_normal=normal(pos,L,side)
        forms=(PRE_NORMAL if is_normal else PRE_OPPOSITE) if pre else (S_NORMAL if is_normal else S_OPPOSITE)
        transforms.append(forms)
        dimensions.append(sorted({label for form in forms.values() for label,_ in form}))
        zero.append(None if pre else P)
        if not pre:suffix.append(axis)
    def degree(word):return sum(word[j]!=zero[j] for j in suffix)
    values={}
    for word in product(*dimensions):
        if degree(word)>=t:continue
        leaf=list(fixed)
        for pos,label in zip(inner,word):leaf[pos]=label
        leaf=tuple(leaf)
        assert accepted_profile_leaf(leaf,L,Lpre,m,ell,side)
        values[word]=table[leaf] # A missing key is a genuine retention failure.
        stats['source_lookups']+=1
    count=len(values)
    expected=4**ell*sum(comb(m-ell,a)*comb(m-ell,b)*3**a*2**b
                       for a in range(m-ell+1) for b in range(m-ell+1) if a+b<t)
    assert count==expected
    for axis,forms in enumerate(transforms):
        old_zero=zero[:]
        dimensions[axis]=list(forms)
        if axis in suffix:zero[axis]='z'
        updated={}
        for word in product(*dimensions):
            if degree(word)>=t:continue
            value=0
            for label,coefficient in forms[word[axis]]:
                predecessor=word[:axis]+(label,)+word[axis+1:]
                before=sum(predecessor[j]!=old_zero[j] for j in suffix)
                assert before<=degree(word)<t
                assert predecessor in values
                value+=coefficient*values[predecessor]
                stats['predecessors']+=1
            updated[word]=value
        values=updated
        assert len(values)<=count
    return values,suffix


def block_order(L,Lpre):
    return tuple(range(Lpre))+tuple(range(L,L+Lpre))+tuple(range(Lpre,L))+tuple(range(L+Lpre,2*L))


def valid_box(word,L,Lpre,m,t):
    if sum(label in (P,STAR) for label in word)>2*m-t:return False
    for half in (word[:L],word[L:]):
        special=[label for label in half if label in (P,STAR)]
        if len(special)>m:return False
    special=[word[pos] for pos in block_order(L,Lpre) if word[pos] in (P,STAR)]
    if special!=sorted(special,reverse=True):return False
    return True


def complete_query(aug_left,aug_right,ordinary_left,ordinary_right,fixed,inner,L,Lpre,m,ell,t,stats):
    prefix={pos for pos in inner if pos%L<Lpre}
    assert len(prefix)==2*ell
    suffix=tuple(pos for pos in inner if pos not in prefix)
    left,suffix_axes=projected(aug_left,fixed,inner,prefix,L,Lpre,m,ell,t,'left',stats)
    right,_=projected(aug_right,fixed,inner,prefix,L,Lpre,m,ell,t,'right',stats)
    assert left.keys()==right.keys()
    answer=0
    for word,value in left.items():
        d=sum(word[j]!='z' for j in suffix_axes)
        coefficient=(-1)**(t-d-1)*comb(len(suffix)-d-1,t-d-1)
        answer+=coefficient*value*right[word]
    @lru_cache(None)
    def box(word):
        assert valid_box(word,L,Lpre,m,t)
        stats['box_states']+=1
        stars=[pos for pos in block_order(L,Lpre) if word[pos]==STAR]
        if not stars:
            assert all(label<=P for label in word)
            assert max(word[:L].count(P),word[L:].count(P))<=m
            assert word.count(P)<=2*m-t
            stats['box_leaves']+=1
            return ordinary_left[word]*ordinary_right[word]
        pos=stars[-1]
        return sum(box(word[:pos]+(label,)+word[pos+1:]) for label in range(5))
    top_boxes=0
    for marked_tuple in combinations(suffix,len(suffix)-t):
        marked=set(marked_tuple); stars=set(prefix)
        for pos in suffix:
            if pos not in marked:break
            stars.add(pos)
        switched=tuple(pos for pos in suffix if pos not in marked)
        for labels in product(range(4),repeat=t):
            word=list(fixed)
            for pos in stars:word[pos]=STAR
            for pos,label in zip(switched,labels):word[pos]=label
            answer+=box(tuple(word));top_boxes+=1
    assert top_boxes==4**t*comb(2*(m-ell),t)
    return answer


def direct_scalar(array,dimensions,forms):
    value=0
    for entries in product(*forms):
        index=0; coefficient=1
        for dimension,(entry,weight) in zip(dimensions,entries):
            index=index*dimension+entry;coefficient*=weight
        value+=coefficient*array[index]
    return value


def original_array_oracle(left,right,L,fixed,inner):
    """Contract the rank-two local identity directly on unencoded arrays."""
    answer=0
    for choices in product(range(2),repeat=len(inner)):
        choice=dict(zip(inner,choices));left_forms=[];right_forms=[]
        for pos in range(2*L):
            if pos in choice:
                phi=((2+choice[pos],1),)
                psi=((0 if choice[pos]==0 else 2,1),)
            else:phi,psi=PHI[fixed[pos]],PSI[fixed[pos]]
            left_forms.append(phi if pos<L else psi)
            right_forms.append(psi if pos<L else phi)
        answer+=direct_scalar(left,[4]*L+[3]*L,left_forms)*direct_scalar(right,[3]*L+[4]*L,right_forms)
    return answer


def main():
    rng=random.Random(2026101506320)
    stats={key:0 for key in ('queries','asymmetric_slots','small_cutoffs','source_lookups','predecessors','box_states','box_leaves','encoders')}
    fixtures=[(1,0,1,0),(2,0,1,0),(2,1,1,0),(2,1,2,1),
              (3,1,2,1),(3,2,2,1),(3,1,3,1),(3,2,3,2)]
    for L,Lpre,m,ell in fixtures:
        slots=[pre+post for pre in combinations(range(Lpre),ell)
               for post in combinations(range(Lpre,L),m-ell)]
        assert slots and m>ell
        for pattern in ('signed','sparse'):
            n=12**L
            if pattern=='signed':
                left=[rng.randrange(-4,5) for _ in range(n)]
                right=[rng.randrange(-4,5) for _ in range(n)]
            else:
                left=[0]*n;right=[0]*n
                for _ in range(2*L+3):
                    left[rng.randrange(n)]=rng.choice([-3,-1,2,4])
                    right[rng.randrange(n)]=rng.choice([-4,-2,1,3])
            aug_left=restricted_encode(left,L,Lpre,m,ell,1,'left',True)
            aug_right=restricted_encode(right,L,Lpre,m,ell,1,'right',True)
            stats['encoders']+=2
            for t in range(1,2*(m-ell)+1):
                ordinary_left=restricted_encode(left,L,Lpre,m,ell,t,'left',False)
                ordinary_right=restricted_encode(right,L,Lpre,m,ell,t,'right',False)
                stats['encoders']+=2
                for q0,q1 in product(slots,repeat=2):
                    inner=q0+tuple(L+j for j in q1)
                    for fixed_choice in ('zero','last','random'):
                        fixed=tuple(P if pos in inner else (0 if fixed_choice=='zero' else 3 if fixed_choice=='last' else rng.randrange(4)) for pos in range(2*L))
                        expected=original_array_oracle(left,right,L,fixed,inner)
                        got=complete_query(aug_left,aug_right,ordinary_left,ordinary_right,fixed,inner,L,Lpre,m,ell,t,stats)
                        assert got==expected,(L,Lpre,m,ell,t,q0,q1,fixed_choice,pattern,got,expected)
                        stats['queries']+=1
                        stats['asymmetric_slots']+=q0!=q1
                        stats['small_cutoffs']+=t<2*ell
    assert stats['asymmetric_slots'] and stats['small_cutoffs']
    print('PASS complete fixed-profile query versus original-array oracle:',stats)
    print('All table counts, all internal-array bounds, sparse predecessor closures, augmented-source acceptance, and restricted box-leaf lookups passed.')


if __name__=='__main__':main()
