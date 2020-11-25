from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.sets.contains import Contains
from sympy.sets.sets import Interval
from sympy import Symbol
from sympy.concrete.expr_with_limits import ForAll
from sympy.core.numbers import oo
from sympy.sets.conditionset import conditionset
# P is condition set;


@plausible
def apply(P):
    definition = P.definition
    assert definition.is_ConditionSet    
    x = definition.variable
    return ForAll[x:P](definition.limits[0][1])


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    P = Symbol.P(definition=conditionset(x[:n], Equality(x[:n].set, Interval(0, n - 1, integer=True))))
    Eq << apply(P)
    
    Eq << ForAll[x[:n]:P](Contains(x[:n], P), plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[-1].this.function.subs(Eq[0])
    

if __name__ == '__main__':
    prove(__file__)

