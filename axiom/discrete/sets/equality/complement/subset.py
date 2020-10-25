from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Subset
from sympy.sets.sets import EmptySet
from sympy import Symbol
# given: B - A = {} 
# B in A


@plausible
def apply(given):
    assert given.is_Equality
    A_minus_B, emptyset = given.args
    assert emptyset.is_EmptySet and A_minus_B.is_Complement
    
    B, A = A_minus_B.args

    return Subset(B, A, given=given)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(dtype=dtype.integer, given=True)
    B = Symbol.B(dtype=dtype.integer, given=True)

    Eq << apply(Equality(B - A, EmptySet()))
    
    Eq << Eq[0].union(A).reversed
    
    Eq << Eq[1].subs(Eq[-1])

if __name__ == '__main__':
    prove(__file__)

