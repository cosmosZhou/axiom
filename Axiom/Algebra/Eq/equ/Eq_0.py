from util import *


@apply
def apply(self):
    x, y = self.of(Equal)

    return Equal(x - y, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    a = Symbol(real=True)
    b = Symbol(real=True, zero=False)
    Eq << apply(Equal(a, b))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Eq.to.Eq_0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq.of.Eq_0)


if __name__ == '__main__':
    run()
# created on 2021-12-29
