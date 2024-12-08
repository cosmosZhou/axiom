from util import *


@apply
def apply(self):
    x = self.of(Abs)
    return Equal(self, Piecewise((-x, x <= 0), (x, True)))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    Eq << apply(abs(x))

    Eq << Algebra.Abs.eq.Piece.Gt_0.apply(abs(x))

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.swap)


if __name__ == '__main__':
    run()
# created on 2018-01-18
