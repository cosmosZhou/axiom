from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    S[x], M = lt.of(Less)

    return Less(sqrt(x), sqrt(M))


@prove
def prove(Eq):
    from axiom import algebra

    x, M = Symbol(real=True)
    Eq << apply(x >= 0, x < M)

    Eq << algebra.ge.lt.then.gt.trans.apply(Eq[0], Eq[1])

    Eq << algebra.gt_zero.then.gt_zero.sqrt.apply(Eq[-1])

    Eq << algebra.ge_zero.then.ge_zero.sqrt.apply(Eq[0])

    Eq << algebra.gt.ge.then.gt.add.apply(Eq[-2], Eq[-1])

    Eq << algebra.lt.then.lt_zero.apply(Eq[1])

    Eq << Eq[-1].this.lhs.apply(algebra.sub.square.to.mul)

    Eq << algebra.gt_zero.lt.then.lt.div.apply(Eq[-3], Eq[-1])

    Eq << algebra.lt_zero.then.lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-28
