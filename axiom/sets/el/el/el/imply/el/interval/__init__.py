from util import *


@apply
def apply(contains0, contains1, contains2, swap=False):
    w, interval01 = contains0.of(Element)
    assert interval01 in Interval(0, 1)

    x0, s = contains1.of(Element)
    x1, S[s] = contains2.of(Element)
    assert s.is_Interval
    if swap:
        x0, x1 = x1, x0
    return Element(x0 * w + x1 * (1 - w), s)

@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x0, x1, w = Symbol(real=True)
    domain = Interval(a, b, left_open=True)
    Eq << apply(Element(w, Interval(0, 1)), Element(x0, domain), Element(x1, domain))

    w = Symbol(domain=Eq[0].rhs)
    Eq << sets.el.el.imply.el.interval.apply(Eq[1], Eq[2], w=w)

    Eq << algebra.cond.imply.all.apply(Eq[-1], w)

    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])

    


if __name__ == '__main__':
    run()
from . import open
# created on 2020-05-30
# updated on 2023-05-04
