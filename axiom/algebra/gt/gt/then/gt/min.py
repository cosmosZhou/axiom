from util import *


@apply
def apply(gt_0, gt_1):
    x, a = gt_0.of(Greater)
    y, b = gt_1.of(Greater)
    return Greater(Min(x, y), Min(a, b))


@prove
def prove(Eq):
    from axiom import algebra

    a, b, x, y = Symbol(real=True, given=True)
    Eq << apply(x > a, y > b)

    Eq << Eq[-1].this.lhs.apply(algebra.min.to.piece)

    Eq << algebra.cond_piece.of.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.then.ge_min.apply(a, b)

    Eq << algebra.ge.gt.then.gt.trans.apply(Eq[0], Eq[-1])

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq[-1], Eq[-3], invert=True)

    Eq << algebra.then.ge_min.apply(b, a)

    Eq << algebra.gt.ge.then.gt.trans.apply(Eq[1], Eq[-1])

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq[-1], Eq[-3], invert=True)





if __name__ == '__main__':
    run()
# created on 2019-07-18
# updated on 2023-04-29
