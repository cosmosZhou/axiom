from util import *


@apply
def apply(given, upper=None, lower=None):
    x, interval = given.of(Element)
    domain, *shape = interval.of(CartesianSpace)
    a, b = domain.of(Interval)
    if upper is not None:
        assert upper >= b or upper - b >= 0
        b = upper
    elif lower is not None:
        assert lower <= a or lower - a <= 0
        a = lower
        
    return Element(x, CartesianSpace(Interval(a, b, **domain.kwargs), *shape))


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(integer=True, positive=True)
    a, b = Symbol(integer=True)
    x = Symbol(integer=True, shape=(n,))
    Eq << apply(Element(x, CartesianSpace(Interval(a, b), n)), lower=a - 1)

    Eq << sets.el_cartesianSpace.imply.all.el.apply(Eq[0])

    Eq << sets.el_cartesianSpace.given.all.el.apply(Eq[1])

    Eq << sets.el_interval.given.el.interval.restrict.apply(Eq[-1], lower=a)

    


if __name__ == '__main__':
    run()
# created on 2023-08-20
