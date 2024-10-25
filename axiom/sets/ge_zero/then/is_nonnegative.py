from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    assert x.is_finite
    return Element(x, Interval(0, oo))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(complex=True)
    Eq << apply(x >= 0)

    Eq << sets.ge.then.is_real.apply(Eq[0], simplify=None)

    Eq << sets.el_interval.then.ou.apply(Eq[-1], 0, left_open=False)

    Eq <<= Eq[0] & Eq[-1]

    Eq << algebra.et.then.ou.apply(Eq[-1])

    Eq << algebra.et.then.et.apply(Eq[-1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2021-02-14
