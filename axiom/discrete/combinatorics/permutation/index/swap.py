from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy import Symbol
from sympy.concrete.expr_with_limits import LAMBDA
from axiom.discrete.combinatorics.permutation.index.equality import index_function
from sympy.matrices.expressions.matexpr import Swap
from axiom import discrete, sets
from sympy.functions.special.tensor_functions import KroneckerDelta


@plausible
def apply(given, i=None, j=None, w=None):
    assert given.is_Equality
    x_set_comprehension, interval = given.args
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert b - a == n - 1
    x = LAMBDA(x_set_comprehension.function.arg, *x_set_comprehension.limits).simplify()
    
    if j is None:
        j = Symbol.j(domain=[0, n - 1], integer=True, given=True)
    
    if i is None:
        i = Symbol.i(domain=[0, n - 1], integer=True, given=True)

    assert j >= 0 and j < n
    assert i >= 0 and i < n
        
    index = index_function(n)
    if w is None:
        _i = Symbol.i(integer=True)
        _j = Symbol.j(integer=True)
        w = Symbol.w(definition=LAMBDA[_j:n, _i:n](Swap(n, _i, _j)))
    
    return Equality(index[i](w[index[i](x[:n]), index[j](x[:n])] @ x[:n]), index[j](x[:n]), given=given)


@check
def prove(Eq): 
    
    n = Symbol.n(domain=[2, oo], integer=True)
    
    x = Symbol.x(shape=(n,), integer=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=[0, n - 1], integer=True, given=True)
    i = Symbol.i(domain=[0, n - 1], integer=True, given=True)
    
    Eq << apply(Equality(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True)), i, j)
        
    _, di, dj = Eq[2].lhs.arg.args[0].args
    dj = Symbol("d_j", definition=dj)
    di = Symbol("d_i", definition=di)
    
    Eq.dj_definition = dj.this.definition
    Eq.di_definition = di.this.definition
    
    Eq << Eq[-1].subs(Eq.di_definition.reversed).subs(Eq.dj_definition.reversed)
    
    _i, _j = Eq[0].lhs.indices
    Eq << Eq[0].subs(_i, di).subs(_j, dj)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq.definition = Eq[-1].this.lhs.definition
    
    Eq.expand = Eq.definition.lhs.args[0].function.args[1].this.expand()
    
    Eq << discrete.combinatorics.permutation.index.equality.apply(Eq[1], j=j)
        
    Eq.dj_domain, Eq.x_dj_eqaulity = Eq[-2].subs(Eq.dj_definition.reversed), Eq[-1].subs(Eq.dj_definition.reversed)

    Eq.expand = Eq.expand.subs(Eq.x_dj_eqaulity)
    
    Eq << discrete.combinatorics.permutation.index.equality.apply(Eq[1], j=i)
    Eq.di_domain, Eq.x_di_eqaulity = Eq[-2].subs(Eq.di_definition.reversed), Eq[-1].subs(Eq.di_definition.reversed)
    
    Eq <<= Eq.dj_domain & Eq.di_domain
    Eq << Eq.expand.subs(Eq.x_di_eqaulity)
    
    Eq.union_equality, Eq.piecewise_equality = sets.subset.imply.equality.union.apply(Eq[-2]), Eq.definition.subs(Eq[-1])
    
    Eq.piecewise_equality = Eq.piecewise_equality.this.lhs.expand()
    
    Eq << Eq.piecewise_equality.lhs.args[-1].this.bisect({di, dj})
    
    Eq << Eq[-1].subs(Eq.x_dj_eqaulity).subs(Eq.x_di_eqaulity)
    
    Eq << Eq[-1].this.rhs.subs(Eq.union_equality)
    
    Eq << Eq.di_definition.this.rhs.definition.this.rhs.expand()
    
    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.piecewise_equality = Eq.piecewise_equality.subs(Eq[-1])

    Eq << sets.contains.imply.equality.piecewise.apply(Eq.dj_domain, Interval(1, n - 1, integer=True), dj, 0)
    
    Eq << sets.contains.imply.equality.piecewise.apply(Eq.di_domain, Interval(0, n - 1, integer=True) - dj.set, di * KroneckerDelta(i, j), 0)

    Eq << sets.contains.imply.equality.intersection.apply(Eq.dj_domain)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-4] + Eq[-1]
    
    Eq << Eq.piecewise_equality.subs(Eq[-1]) 

    Eq << discrete.combinatorics.permutation.index.kronecker_delta.indexOf.apply(Eq[1], i, j)
    
    Eq << Eq[-1].subs(Eq.di_definition.reversed).subs(Eq.dj_definition.reversed)
    
    Eq << Eq[-3].subs(Eq[-1].reversed)
    
        
if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
