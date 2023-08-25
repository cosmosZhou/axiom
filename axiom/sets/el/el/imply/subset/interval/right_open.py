from util import *


@apply
def apply(contains1, contains2):
    x, A = contains1.of(Element)
    y, S[A] = contains2.of(Element)
    a, b = A.of(Interval)
    return Subset(Interval(x, y, right_open=True), Interval(a, b, left_open=A.left_open, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x, y = Symbol(real=True, given=True)
    S = Interval(a, b, left_open=True)
    Eq << apply(Element(x, S), Element(y, S))

    Eq << sets.el.el.imply.subset.interval.apply(Eq[0], Eq[1])

    Eq << sets.subset.imply.subset.complement.apply(Eq[-1], {y})

    Eq << sets.el.imply.eq.complement.apply(Eq[1])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.subset = sets.subset.imply.subset.complement.apply(Eq[-1], Eq[-1].rhs.args[1])

    Eq << sets.el_interval.imply.le.apply(Eq[1])

    Eq << sets.le.imply.subset.interval.minus_oo.apply(Eq[-1], right_open=True)

    Eq << sets.subset.imply.subset.intersect.apply(Eq[-1], Interval.open(a, oo))
    Eq << sets.subset.subset.imply.subset.transit.apply(Eq.subset, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-11-23
