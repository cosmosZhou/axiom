from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr <= 0)
    return GreaterEqual(y, x)


@prove
def prove(Eq):
    from axiom import algebra
    
    a, b = Symbol(real=True, given=True)
    Eq << apply(GreaterEqual(0, a - b))
    
    Eq << algebra.iff.given.et.infer.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(algebra.le_zero.imply.ge)
    
    Eq << Eq[-1].this.rhs.apply(algebra.le_zero.given.ge)


if __name__ == '__main__':
    run()
# created on 2023-06-20
