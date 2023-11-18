from util import *


@apply
def apply(self):
    x = self.of(Sign)
    assert not x.shape
    assert x.is_extended_real
    return Equal(self, Piecewise((1, x > 0), (-1, x < 0), (0, True)))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(Sign(x))

    Eq << Eq[0].this.lhs.apply(algebra.sign.to.piece.abs)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap, 1)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.et.invert)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=Equal(x, 0))

    Eq << algebra.infer.given.infer.subs.apply(Eq[-2])

    Eq << algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq << Eq[-1].this.lhs.apply(algebra.ne_zero.imply.ou)

    Eq.lt_zero, Eq.gt_zero = algebra.infer_ou.given.et.infer.apply(Eq[-1])

    Eq << algebra.infer.given.infer.subs.bool.apply(Eq.gt_zero)

    Eq << Eq[-1].this.lhs.apply(algebra.gt_zero.imply.eq.abs)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq << Eq.lt_zero.this.rhs.apply(algebra.cond_piece.given.et.infer)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq << Eq[-2].this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.lhs.apply(algebra.lt_zero.imply.eq.abs)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-22

from . import abs
