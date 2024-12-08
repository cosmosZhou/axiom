from util import *


@apply
def apply(self):
    x, y = self.of(Less)
    return Less(x - y, ZeroMatrix(*x.shape))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x < y)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Lt.to.Lt_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lt.of.Lt_0)


if __name__ == '__main__':
    run()
# created on 2023-04-18
