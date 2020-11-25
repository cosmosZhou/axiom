
from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.relational import Equality
from axiom.utility import plausible

from sympy.functions.combinatorial.numbers import Stirling
from axiom.discrete.combinatorics import stirling
from axiom.discrete import combinatorics
from sympy.concrete.summations import Sum
from sympy.concrete.expr_with_limits import LAMBDA
from sympy import Symbol, Slice


@plausible
def apply(n, k):
    i = n.generate_free_symbol(k.free_symbols, integer=True)
    return Equality(Stirling(n, k), Sum[i:0:k]((-1) ** (k - i) * binomial(k, i) * i ** n) / factorial(k))


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, nonnegative=True)
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(n, k)

    i = Eq[-1].rhs.args[1].variable
    
    Eq << Eq[-1].subs(k, 0).doit()

    Eq << stirling.second.recurrence.apply(n, k)

    Eq << Eq[-1].subs(Eq[0])

    from sympy import oo
    y = Symbol.y(shape=(oo,), definition=LAMBDA[n](Stirling(n, k + 1)))

    Eq << y.equality_defined()

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)

    Eq << Eq[-1].rsolve(y[n])

    Eq << combinatorics.binomial.fraction.apply(k + 1, i).reversed * (k + 1 - i)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq.stirling_solution = Eq[-1].subs(Eq[3])
    
    Eq << Eq.stirling_solution.subs(n, k + 1)

    Eq << Eq[-1].this.function / (k + 1) ** (k + 1)
    
    Eq << Eq.stirling_solution.this.function / (k + 1) ** n
    Eq << Eq[-1] - Eq[-2]
    
    Eq << Eq[-1] * (k + 1) ** n
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq.ratsimp = Eq[-1].this.rhs.args[0].ratsimp()
    
    Eq.powsimp = Eq[-1].rhs.args[1].args[-1].this.function.powsimp()
    
    Eq << combinatorics.permutation.factorial.sum.apply(k + 1)
    
    Eq << Eq[-1] * (-1) ** (k + 1)
    
    Eq << Eq[-1].this.rhs.distribute()
    
    Eq << Eq[-1].this.rhs.bisect(Slice[-1:]).reversed
    
    Eq << Eq[-1].subs(Eq.powsimp.reversed)
    
    Eq << Eq[-1] - Eq[-1].lhs.args[0]
    
    Eq << Eq.ratsimp.subs(Eq[-1])
    
    Eq << Eq[-1] - Eq[-1].lhs.args[0] - Eq[-1].rhs.args[0]
    
    Eq << Eq[-1] * factorial(k + 1)
    
    Eq << Eq[-1].this.lhs.expand()    
    
    Eq.k_factorial_expand = combinatorics.permutation.factorial.expand.apply(k + 1).this.rhs.expand()
    
    Eq << Eq[-1].this.lhs.args[1].subs(Eq.k_factorial_expand)
    
    Eq << Eq[-1].this.rhs.subs(Eq.k_factorial_expand)
    
    Eq << Eq[-1].this.rhs.ratsimp()    
    
    Eq << Eq[0].subs(k, k + 1) * factorial(k + 1)

    Eq << Eq[-1].this.rhs.bisect(Slice[-1:])
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << Eq[-1] - Eq[-1].lhs.args[0]
    
    Eq << Eq[-1].this.rhs.distribute()


if __name__ == '__main__':
    prove(__file__)
