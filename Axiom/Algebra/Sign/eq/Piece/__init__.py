from util import *


@apply
def apply(self):
    x = self.of(Sign)
    assert not x.shape
    assert x.is_extended_real
    return Equal(self, Piecewise((1, x > 0), (-1, x < 0), (0, True)))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    Eq << apply(Sign(x))

    Eq << Eq[0].this.lhs.apply(Algebra.Sign.eq.Piece.Abs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.swap, 1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.And.invert)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.swap)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=Equal(x, 0))

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-2])

    Eq << Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1], invert=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne_0.to.Or)

    Eq.lt_zero, Eq.gt_zero = Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Imply.of.Imply.subs.Bool.apply(Eq.gt_zero)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.to.Eq.Abs)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Eq.lt_zero.this.rhs.apply(Algebra.Cond_Piece.of.And.Imply)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    Eq << Eq[-2].this.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.lhs.apply(Algebra.Lt_0.to.Eq.Abs)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-22

del Abs
from . import Abs
