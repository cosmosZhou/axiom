from util import *


@apply
def apply(self):
    x, y = self.of(Less)
    return Greater(y - x, ZeroMatrix(*x.shape))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x < y)

    Eq << Eq[0].this.lhs.apply(Algebra.Lt.equ.Lt_0)

    Eq << -Eq[-1].this.lhs




if __name__ == '__main__':
    run()
# created on 2023-06-19
