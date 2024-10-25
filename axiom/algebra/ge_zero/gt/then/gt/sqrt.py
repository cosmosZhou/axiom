from util import *


@apply
def apply(is_nonnegative, gt):
    x = is_nonnegative.of(Expr >= 0)
    y, S[x] = gt.of(Greater)
    return Greater(sqrt(y), sqrt(x))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, y > x)

    Eq << algebra.gt.ge.then.gt.trans.apply(Eq[1], Eq[0])

    Eq << algebra.gt_zero.then.gt_zero.sqrt.apply(Eq[-1])

    Eq << algebra.ge_zero.then.ge_zero.sqrt.apply(Eq[0])

    Eq.is_positive = algebra.gt.ge.then.gt.add.apply(Eq[-2], Eq[-1])

    Eq << algebra.gt.then.gt_zero.apply(Eq[1])

    Eq << algebra.gt_zero.gt.then.gt.div.apply(Eq.is_positive, Eq[-1])

    Eq << ((sqrt(x) + sqrt(y))(-sqrt(x) + sqrt(y))).this.apply(algebra.mul.to.add, deep=True)

    Eq << algebra.gt_zero.eq.then.eq.div.apply(Eq.is_positive, Eq[-1], simplify=None)

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << algebra.gt.of.gt_zero.apply(Eq[2])




if __name__ == '__main__':
    run()
# created on 2019-06-13
# updated on 2023-05-02
