from util import *


@apply
def apply(self):
    args = self.of(Add ** 2)

    return Equal(self, Add(*(-arg for arg in args)) ** 2)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(real=True)

    Eq << apply((x - y) ** 2)

    Eq << Eq[-1].this.lhs.apply(Algebra.Square.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Algebra.Square.eq.Add)


if __name__ == '__main__':
    run()
# created on 2019-11-07
