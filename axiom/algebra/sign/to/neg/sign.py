from util import *


@apply
def apply(self):
    x = self.of(Sign)
    return Equal(self, -Sign(-x))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(complex=True)
    Eq << apply(Sign(x - y))

    Eq << Eq[-1].this.lhs.apply(algebra.sign.to.piece)

    Eq << Eq[-1].this.find(Sign).apply(algebra.sign.to.piece)

    Eq << Eq[-1].this.find(Equal[0]).apply(algebra.eq.transport)

    Eq << Eq[-1].this.find(Equal[0]).apply(algebra.eq.transport)

    Eq << Eq[-1].this.find(Equal).reversed

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.piece)

    Eq << Eq[-1].this.rhs.find(Mul).apply(algebra.mul.negate)

    Eq << Eq[-1].this.rhs.find(Abs).apply(algebra.abs.neg)


if __name__ == '__main__':
    run()
# created on 2023-05-25
