from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, Ref
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap

@plausible
def apply(x):
    n = x.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))    
    w = IndexedBase('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Swap(n, i, j)))
    
    return Equality((w[i, j] @ x).set_comprehension(), x.set_comprehension())


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))    
    x = IndexedBase('x', (n,), integer=True)    
    
    Eq << apply(x)
    
    k = Eq[1].lhs.variable
    
    Eq << Eq[0][k]
    
    Eq << Eq[0][k] @ x
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].set
    
    Eq << Eq[-1].union_comprehension((k, 0, n - 1))

        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html