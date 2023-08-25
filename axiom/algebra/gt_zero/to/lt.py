from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr > 0)
    return Less(y, x)


@prove
def prove(Eq):
    from axiom import algebra
    
    a, b = Symbol(real=True, given=True)
    Eq << apply(Less(0, a - b))
    
    Eq << algebra.iff.given.et.infer.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(algebra.gt_zero.imply.lt)
    
    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.given.lt)


if __name__ == '__main__':
    run()
# created on 2023-06-20
