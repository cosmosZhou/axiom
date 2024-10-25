from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(Greater)
    assert n.is_finite
    assert b > 0
    return Element(1 / n, Interval.open(0, 1 / b))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(real=True)
    b = Symbol(real=True, positive=True)
    Eq << apply(n > b)

    Eq << sets.el_interval.of.et.apply(Eq[1])

    Eq << Greater(b, 0, plausible=True)

    Eq << algebra.gt.gt.then.gt.trans.apply(Eq[0], Eq[-1])

    Eq << algebra.gt_zero.then.gt_zero.div.apply(Eq[-1])

    Eq << algebra.gt_zero.gt.then.gt.div.apply(Eq[-2], Eq[0])

    Eq << algebra.gt_zero.gt.then.gt.div.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-10-04
