from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr < 0)
    return Greater(y, x)


@prove
def prove(Eq):
    from axiom import algebra
    
    a, b = Symbol(real=True, given=True)
    Eq << apply(Greater(0, a - b))
    
    Eq << algebra.iff.given.et.infer.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(algebra.lt_zero.imply.gt)
    
    Eq << Eq[-1].this.rhs.apply(algebra.lt_zero.given.gt)


if __name__ == '__main__':
    run()
# created on 2023-06-20
