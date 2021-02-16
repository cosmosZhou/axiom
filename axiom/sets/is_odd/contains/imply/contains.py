from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebre
from sympy.sets.sets import image_set


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply(imply=True)
def apply(*given):
    is_odd, contains_n = given     
    n = axiom.is_odd(is_odd)
    n_, ab = axiom.is_Contains(contains_n)
    
    assert n == n_
    axiom.is_integer_Interval(ab)
    a, b = ab.min(), ab.max()
    
    return Contains(n, image_set(2 * n + 1, n, Interval(a // 2, (b - 1) // 2, integer=True)))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(Equal(n % 2, 1), Contains(n, Interval(a, b, integer=True)))
    
    Eq << algebre.is_odd.imply.exists.apply(Eq[0])
    
    Eq << Eq[-1].this.function.apply(algebre.equal.condition.imply.condition.subs, Eq[1])
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.contains.interval.divide.integer, 2, simplify=None)
    
    Eq << (Eq[-3] - 1).this.function.apply(algebre.equal.imply.equal.divide, 2, simplify=None)
        
    Eq << Eq[-1].this.function.apply(algebre.equal.imply.equal.reversed, simplify=None)
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.args[0].apply(algebre.imply.equal.ceiling.astype.floor)
    
    S = Symbol.S(definition=conditionset.conditionset(n, Eq[-1]))
    Eq << S.this.definition
    
    Eq << Eq[-1].this.rhs.limits_subs(n, 2 * n + 1)
    
    Eq << Contains(n, S, plausible=True)
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].subs(Eq[-2])

    
if __name__ == '__main__':
    prove(__file__)
