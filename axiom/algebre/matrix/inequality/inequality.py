from axiom.utility import plausible
from sympy.core.relational import Unequal, Equality
from sympy import Symbol
from sympy.matrices.expressions.determinant import Determinant
from sympy.matrices.expressions.inverse import Inverse
from sympy.matrices.expressions.cofactor import Cofactors
from axiom import algebre


@plausible
def apply(*given):
    unequality, eq = given
    if not unequality.is_Unequality:
        unequality, eq = eq, unequality
    assert unequality.is_Unequality
    unequality.rhs.is_zero
    
    assert unequality.lhs.is_Determinant
    divisor = unequality.lhs.arg    
    return Unequal(eq.lhs @ Inverse(divisor), eq.rhs @ Inverse(divisor), given=given)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True)
    A = Symbol.A(real=True, shape=(n, n), given=True)
    a = Symbol.a(real=True, shape=(n,), given=True)
    b = Symbol.b(real=True, shape=(n,), given=True)
    Eq << apply(Unequal(Determinant(A), 0), Unequal(a @ A, b))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].split()
    
    Eq << Eq[-2] @ A
    
    Eq <<= Eq[1].subs(Eq[-1])
    
    Eq <<= Eq[-2] & Eq[0]
    
    

if __name__ == '__main__':
    prove(__file__)
