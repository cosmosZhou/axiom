from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets
import axiom
# given: |A| >= 1
# A != {}


@apply(imply=True)
def apply(given):
    n, b = axiom.is_StrictGreaterThan(given)

    return Contains(n, Interval(b, oo, left_open=True, integer=n.is_integer))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    
    Eq << apply(n > b)
    
    Eq << Eq[-1].simplify()    

if __name__ == '__main__':
    prove(__file__)
