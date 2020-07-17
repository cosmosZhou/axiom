from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, Ref, identity
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import Forall
from axiom import Algebre


@plausible
def apply(n):
    domain = Interval(0, n - 1, integer=True)
    t = Symbol('t', domain=domain)
    i = Symbol('i', domain=domain)
    j = Symbol('j', domain=domain)
    assert n >= 2
    w = IndexedBase('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Swap(n, i, j)))
    
    return Forall(Equality(w[t, i] @ w[t, j] @ w[t, i], w[i, j]), (j, domain - {i, t}))


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    Eq << apply(n)
    
    i, j = Eq[-1].rhs.indices
    
    w = Eq[0].lhs.base
    
    t = Eq[1].function.lhs.args[0].indices[0]
    
    p = Symbol('p')
    
    x = Ref[i:n](p ** i)
    Eq << identity(w[t, i] @ x).subs(Eq[0].subs(i, t).subs(j, i))
    Eq << Eq[-1].this.rhs.expand().simplify(deep=True)
    
    Eq << w[t, j] @ Eq[-1]
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].forall(*Eq[1].limits[0])
    
    Eq << Eq[-1].this.function.rhs.simplify(deep=True)
    
    Eq << w[t, i] @ Eq[-1]
    
    Eq << Eq[-1].this.function.rhs.expand()
    
    Eq << Eq[-1].this.simplify(deep=True)

    Eq << Eq[-1].this.function.rhs.function.asKroneckerDelta()
    
    Eq.www_expansion = Eq[-1].this.simplify(deep=True)
    
    Eq << identity(w[i, j] @ x).expand().simplify(deep=True)
    
    Eq << Eq[-1].this.rhs.function.asKroneckerDelta()
    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq.www_expansion.subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(Algebre.matrix.independence.rmatmul_equality)


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html