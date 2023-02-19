from util import *


@apply(given=None)
def apply(given, index=-1):
    x, args = given.of(Expr < Min)
    if index is None:
        eqs = [x < arg for arg in args]
    else:
        first = args[:index]
        second = args[index:]
        eqs = x < Min(*first), x < Min(*second)
        
    return Equivalent(given, And(*eqs), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    
    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x < Min(y, z))
    
    Eq << algebra.iff.given.et.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(algebra.lt_min.imply.et.lt)
    
    Eq << Eq[-1].this.rhs.apply(algebra.lt.lt.imply.lt.min)


if __name__ == '__main__':
    run()
# created on 2022-01-01
