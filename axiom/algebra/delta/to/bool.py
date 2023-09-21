from util import *


@apply
def apply(self, swap=False):
    x, y = self.of(KroneckerDelta)
    if swap:
        x, y = y, x
    return Equal(self, Bool(Equal(x, y)))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    Eq << apply(KroneckerDelta(x, y))

    Eq << Eq[0].this.rhs.apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.delta.to.piece)


if __name__ == '__main__':
    run()
# created on 2023-08-20
