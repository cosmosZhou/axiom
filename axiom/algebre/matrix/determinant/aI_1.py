from axiom.utility import plausible
from sympy.core.relational import Equality
from sympy import Symbol, Slice
from sympy.matrices.expressions.determinant import Det
from sympy.concrete.products import Product
from sympy.concrete.expr_with_limits import LAMBDA
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.concrete.summations import Sum 
from sympy.core.numbers import oo
from sympy.matrices.expressions.matexpr import Identity
from sympy.functions.elementary.piecewise import Piecewise
from axiom.algebre.matrix.determinant import expansion_by_minors
from sympy.sets.sets import Interval


@plausible
def apply(n, a):
    i = Symbol.i(integer=True)
    return Equality(Det(1 + a[:n] * Identity(n)), (1 + Sum[i:0:n - 1](1 / a[i])) * Product[i:0:n - 1](a[i]))


from axiom.utility import check


def column_transformation(*limits):
    n = limits[0][-1] + 1
    (i, *_), (j, *_) = limits    
#     return Identity(n) + LAMBDA[j:n, i:n](Piecewise((0, i < n - 1), (KroneckerDelta(j, n - 1) - 1, True)))
#     return Identity(n) + LAMBDA[j:n, i:n](Piecewise((KroneckerDelta(j, n - 1) - 1, Equality(i, n - 1)), (0, True)))
    return Identity(n) + LAMBDA[j:n, i:n](KroneckerDelta(i, n - 1) * (KroneckerDelta(j, n - 1) - 1))
    return LAMBDA(Piecewise((KroneckerDelta(i, j), i < n - 1), (2 * KroneckerDelta(j, n - 1) - 1, True)), *limits)


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(shape=(oo,), complex=True, zero=False)
    Eq << apply(n, a)
    
    Eq << Eq[-1].subs(n, 1)
    
    Eq << Eq[-1].this.lhs.doit()
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[0].subs(n, n + 1)
    
    Eq << expansion_by_minors.apply(Eq[-1].lhs.arg, i=n)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].this.lhs.bisect(Slice[-1:])
    
    Eq << Eq[-1].this.lhs.args[1]().function.args[1].simplify()
    
    Eq << Eq[-1].this.lhs.args[0].args[1].arg().function.simplify() 
    
    Eq.deduction = (Eq[-1] - Eq[-1].lhs.args[0]).subs(Eq[0])
    
    Eq << Eq.deduction.rhs.args[0].args[1].this.bisect(Slice[-1:])
    
    Eq << Eq.deduction.rhs.args[0].args[0].args[1].this.bisect(Slice[-1:])
    
    Eq << Eq.deduction.rhs.this.subs(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq.deduction = Eq.deduction.subs(Eq[-1])
    
    D = Eq.deduction.lhs.function.args[1].arg
    
    i = Eq.deduction.lhs.variable.copy(domain=Interval(0, n - 1, integer=True))
    D = D._subs(Eq.deduction.lhs.variable, i)
    Eq << (D @ column_transformation(*D.limits)).this.expand()
    
    Eq << Eq[-1].this.rhs.function.args[1].bisect(Slice[-1:])
    
    Eq << Eq[-1].rhs.args[1].function.args[3].this().function.args[1].simplify()
    
    Eq << Eq[-2].rhs.args[1].function.args[2].this().function.args[1].simplify() 
    
    Eq << Eq[-3].this.rhs.subs(Eq[-2] + Eq[-1])
    
#     Eq.column_transformation = Eq[-1].this.rhs.args[0]().function.simplify()
    Eq.column_transformation = Eq[-1].this.rhs.simplify(deep=True)
#     Eq << expansion_by_minors.apply(Eq.column_transformation.rhs, i=i).this.rhs.args[-1].arg().function.simplify()
    Eq << expansion_by_minors.apply(Eq.column_transformation.rhs, i=i).this.rhs.simplify(deep=True)

    Eq << Eq[-1].this.rhs.args[1].doit()
    
    v = Eq[-1].rhs.args[1].variable
    Eq << Eq[-1].this.rhs.args[1].limits_subs(v, v - 1)
    
    k = Eq[-1].rhs.args[1].variable
    Eq << Product[k:n](Eq[-1].rhs.args[1].function).this.bisect({i})
    
    Eq << Eq[-2].subs((Eq[-1] / Eq[-1].rhs.args[0]).reversed)

    Eq << Eq.column_transformation.det().subs(Eq[-1]).forall((i,))
         
    Eq << Eq.deduction.subs(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
