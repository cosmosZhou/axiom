from util import *


@apply
def apply(given):
    a, b = given.of(LessEqual)
    return Subset({b, a}, Interval(a, b))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << sets.subset.given.all_el.apply(Eq[1])

    Eq << Eq[-1].this.apply(algebra.all.to.et.doit.setlimit)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq <<= sets.el_interval.given.et.apply(Eq[-2]), sets.el_interval.given.et.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-10-22
