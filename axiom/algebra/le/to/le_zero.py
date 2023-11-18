from util import *


@apply
def apply(self):
    x, y = self.of(LessEqual)
    return LessEqual(x - y, ZeroMatrix(*x.shape))


@prove
def prove(Eq):
    from axiom import algebra
    
    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)
    
    Eq << algebra.iff.given.et.infer.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(algebra.le.imply.le_zero)
    
    Eq << Eq[-1].this.rhs.apply(algebra.le.given.le_zero)


if __name__ == '__main__':
    run()
# created on 2023-04-18
