#!/usr/bin/env python3
"""Exact conditional-expectation construction of the proposed bias list.

Every comparison uses Fraction. Common untouched-entry factors C**(N-t-1)
are cancelled, not approximated. Full-list repetition is permitted and list
indices, rather than vector values, define the later gauge partition.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache

R=F(101,100)
C=(R+1/R)/2
assert C==F(20201,20200)

@lru_cache(None)
def power(s):return R**s


def initial_threshold(m):
    """Check 2(2^m-1) C^(10000m) < R^(200m), by integer products."""
    N=10000*m
    lhs=2*((1<<m)-1)*pow(C.numerator,N)*pow(R.denominator,200*m)
    rhs=pow(C.denominator,N)*pow(R.numerator,200*m)
    assert lhs<rhs
    return max(lhs.bit_length(),rhs.bit_length())


def construct(m):
    N=10000*m
    chars=tuple(range(1,1<<m))
    sums={u:0 for u in chars}
    histogram=Counter()
    list_values=[]
    comparisons=0
    greatest_abs=0

    def expectation(prefix,exposed):
        value=F(0)
        for u in chars:
            s=sums[u]
            if u>>exposed:
                # At least one nonzero character bit remains uniform.
                value+=(power(s)+power(-s))*C
            else:
                sign=1 if (u&prefix).bit_count()%2==0 else -1
                value+=power(s+sign)+power(-s-sign)
        return value

    for t in range(N):
        prefix=0
        before=expectation(prefix,0)
        previous=sum((power(s)+power(-s) for s in sums.values()),F(0))
        assert before==previous*C
        for bit in range(m):
            candidates=[expectation(prefix|(v<<bit),bit+1) for v in (0,1)]
            assert candidates[0]+candidates[1]==2*before
            chosen=0 if candidates[0]<=candidates[1] else 1
            assert candidates[chosen]<=before
            prefix|=chosen<<bit
            before=candidates[chosen]
            comparisons+=1
        for u in chars:
            sums[u]+=1 if (u&prefix).bit_count()%2==0 else -1
        final=sum((power(s)+power(-s) for s in sums.values()),F(0))
        assert final==before and final<=previous*C
        greatest_abs=max(greatest_abs,max(map(abs,sums.values())))
        histogram[prefix]+=1
        list_values.append(prefix)
    threshold=N//50
    assert N%50==0
    assert all(abs(s)<threshold for s in sums.values())
    # Check the final exact rational potential against the same strict threshold.
    assert sum((power(s)+power(-s) for s in sums.values()),F(0))<power(threshold)
    # Independently recompute every character sum from the output histogram.
    fresh={u:sum(count*(1 if (u&d).bit_count()%2==0 else -1)
                 for d,count in histogram.items()) for u in chars}
    assert fresh==sums and sum(histogram.values())==N and len(list_values)==N
    return dict(m=m,N=N,character_count=len(chars),bit_comparisons=comparisons,
                largest_intermediate_character_sum=greatest_abs,
                final_character_sums=sums,histogram=dict(sorted(histogram.items())),
                strict_bias_threshold=threshold,initial_integer_bits=initial_threshold(m))


def main():
    # Fixed rational inequality used in the all-m proof.
    lhs=pow(101,200)*pow(20200,10000)
    rhs=4*pow(100,200)*pow(20201,10000)
    assert lhs>rhs
    print('PASS exact fixed threshold: (101/100)^200 > 4*(20201/20200)^10000; integer bits',
          max(lhs.bit_length(),rhs.bit_length()),flush=True)
    for m in (1,2,3):
        print('PASS exact small-bias conditional expectation',construct(m),flush=True)

if __name__=='__main__':main()
