from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    b = Ceiling(b)

    a = Floor(a)
    return Element(x, Interval(a, b, **domain.kwargs))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)))

    Eq << Subset(Interval(a, b, left_open=True), Interval(Floor(a), Ceiling(b), left_open=True), plausible=True)

    Eq << sets.subset.of.all_el.apply(Eq[-1])

    Eq << sets.el.subset.then.el.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-08-29
