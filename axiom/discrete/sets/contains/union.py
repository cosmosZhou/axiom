from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy.sets.contains import Contains, Subset
from sympy.core.relational import Equality
from axiom.discrete.sets import subset

# given: A in B 
# => A | B = B
@plausible
def apply(given):
    assert given.is_Contains
    A, B = given.args
    
    return Equality(A.set | B, B, given=given)


from sympy.utility import check


@check
def prove(Eq):
    e = Symbol('e', integer=True)
    s = Symbol('s', dtype=dtype.integer)
    contains = Contains(e, s)
    
    Eq << apply(contains)
    
    Eq << Eq[0].asSubset()
    
    Eq << subset.union.apply(Eq[-1])

if __name__ == '__main__':
    prove(__file__)
