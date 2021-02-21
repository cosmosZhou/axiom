from sympy import *
from axiom.utility import prove, apply
from sympy.concrete.limits import limits_dict
from axiom import algebre


@apply
def apply(given, index=0):
    assert given.is_ForAll
    limits = [*given.limits]
    limit = limits.pop(index) 
    
    limitsDict = limits_dict([limit]) 
    eqs = []
    for var, domain in limitsDict.items():
        if isinstance(domain, list):
            cond = conditionset.conditionset(var, *domain).simplify()
        elif domain.is_set:
            cond = Contains(var, domain).simplify()
        else:
            assert domain.is_boolean
            cond = domain
        eqs.append(cond.invert().simplify())

    if given.function.is_Or:
        eqs += given.function.args
    else:
        eqs.append(given.function)

    if limits:
        return ForAll(Or(*eqs), *limits)        
    return Or(*eqs)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(shape=(), integer=True)    
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(ForAll[x:A, y:B](f(x, y) > 0), index=1)
    
    Eq << algebre.forall.given.ou.apply(Eq[1])
    
    Eq << algebre.forall.imply.ou.rewrite.apply(Eq[0])
#     


if __name__ == '__main__':
    prove(__file__)
