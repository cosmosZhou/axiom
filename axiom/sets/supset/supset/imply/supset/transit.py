from axiom.utility import prove, apply
from sympy import Subset, Symbol, Supset
import axiom
from sympy.core.symbol import dtype
from axiom import sets


@apply(imply=True)
def apply(*given):
    a_less_than_x, x_less_than_b = given
    X, A = axiom.is_Supset(a_less_than_x)    
    B, _X = axiom.is_Supset(x_less_than_b)
    if X != _X:
        A, X, _X, B = _X, B, A, X
    assert X == _X
    return Supset(B, A)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.complex)
    X = Symbol.X(etype=dtype.complex)
    B = Symbol.B(etype=dtype.complex)

    Eq << apply(Supset(X, A), Supset(B, X))
       
    Eq << Eq[0].reversed
    
    Eq << sets.subset.supset.imply.supset.transit.apply(Eq[-1], Eq[1])    
    
if __name__ == '__main__':
    prove(__file__)