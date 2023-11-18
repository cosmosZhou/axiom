from util import *


@apply(simplify=None)
def apply(given, *, evaluate=True):
    n, b = given.of(GreaterEqual)
    assert n.is_finite
    assert b > 0
    return Element(1 / n, Interval.Lopen(0, 1 / b), evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(real=True)
    b = Symbol(real=True, positive=True)
    Eq << apply(n >= b)

    Eq << sets.el_interval.given.et.apply(Eq[1])

    Eq << Greater(b, 0, plausible=True)

    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[0], Eq[-1])

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[-1])

    Eq << algebra.gt_zero.ge.imply.ge.div.apply(Eq[-2], Eq[0])

    Eq << algebra.gt_zero.ge.imply.ge.div.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].reversed

    


if __name__ == '__main__':
    run()
# created on 2023-10-04
