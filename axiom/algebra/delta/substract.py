from util import *


@apply
def apply(self, reverse=False):
    x, y = self.of(KroneckerDelta)
    if reverse:
        diff = y - x
    else:
        diff = x - y
    return Equal(self, KroneckerDelta(diff, 0))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    Eq << apply(KroneckerDelta(x, y))

    Eq << Eq[-1].this.lhs.apply(algebra.delta.to.piece)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.to.is_zero)

    Eq << Eq[-1].this.rhs.apply(algebra.delta.to.piece, swap=True)





if __name__ == '__main__':
    run()
# created on 2021-12-29
# updated on 2023-05-23
