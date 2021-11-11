from util import *


@apply
def apply(greater_than, _greater_than):
    a, x = greater_than.of(GreaterEqual)
    _x, b = _greater_than.of(GreaterEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
    assert x == _x

    return Element(x, Interval(b, a))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x = Symbol(real=True, given=True)
    #Eq << apply(x >= b, a >= x)
    Eq << apply(b >= x, x >= a)

    Eq << sets.el.given.et.split.interval.apply(Eq[-1])



    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-04-06
# updated on 2021-04-06