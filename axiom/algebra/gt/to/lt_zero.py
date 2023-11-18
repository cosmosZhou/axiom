from util import *


@apply
def apply(self):
    x, y = self.of(Greater)
    return Less(y - x, ZeroMatrix(*x.shape))


@prove
def prove(Eq):
    from axiom import algebra
    
    x, y = Symbol(real=True, given=True)
    Eq << apply(x > y)
    
    Eq << Eq[0].this.lhs.apply(algebra.gt.to.gt_zero)
    
    Eq << -Eq[-1].this.lhs


if __name__ == '__main__':
    run()
# created on 2023-06-19
