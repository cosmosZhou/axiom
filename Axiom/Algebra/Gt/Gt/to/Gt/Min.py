from util import *


@apply
def apply(gt_0, gt_1):
    x, a = gt_0.of(Greater)
    y, b = gt_1.of(Greater)
    return Greater(Min(x, y), Min(a, b))


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b, x, y = Symbol(real=True, given=True)
    Eq << apply(x > a, y > b)

    Eq << Eq[-1].this.lhs.apply(Algebra.Min.eq.Piece)

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Algebra.Ge_Min.apply(a, b)

    Eq << Algebra.Ge.Gt.to.Gt.trans.apply(Eq[0], Eq[-1])

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[-1], Eq[-3], invert=True)

    Eq << Algebra.Ge_Min.apply(b, a)

    Eq << Algebra.Gt.Ge.to.Gt.trans.apply(Eq[1], Eq[-1])

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[-1], Eq[-3], invert=True)





if __name__ == '__main__':
    run()
# created on 2019-07-18
# updated on 2023-04-29
