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

    Eq << sets.subset.of.all_el.apply(Eq[1])

    Eq << Eq[-1].this.apply(algebra.all.to.et.doit.setlimit)

    Eq << algebra.et.of.et.apply(Eq[-1])

    Eq <<= sets.el_interval.of.et.apply(Eq[-2]), sets.el_interval.of.et.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-10-22
