from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(LessEqual)
    assert n > 0
    return Element(1 / n, Interval(1 / b, oo))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(real=True, positive=True)
    b = Symbol(real=True)
    Eq << apply(n <= b)

    Eq << sets.el_interval.of.et.apply(Eq[1])

    Eq << Greater(n, 0, plausible=True)

    Eq << algebra.gt.le.then.gt.trans.apply(Eq[0], Eq[-1])

    Eq << algebra.gt_zero.le.then.le.div.apply(Eq[-2], Eq[0])


    Eq << algebra.gt_zero.ge.then.ge.div.apply(Eq[-2], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-04
