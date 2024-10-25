from util import *


@apply
def apply(self):
    assert self.is_KroneckerDelta
    return Element(self, {0, 1})


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(real=True)
    Eq << apply(KroneckerDelta(x, y))

    Eq << Eq[-1].this.lhs.apply(algebra.delta.to.piece)

    Eq << sets.then.el.bool.apply(Bool(Equal(x, y)))

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piece)


if __name__ == '__main__':
    run()

# created on 2021-04-22
