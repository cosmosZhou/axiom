from util import *


@apply
def apply(given, d):
    e, interval = given.of(NotElement)
    d = sympify(d)
    assert d.is_positive

    a, b = interval.of(Range)

    e *= d

    return NotElement(e, interval.copy(start=a * d, stop=(b - 1) * d + 1))


@prove
def prove(Eq):
    from axiom import sets
    x, a, b = Symbol(integer=True, given=True)

    d = Symbol(integer=True, positive=True, given=True)

    Eq << apply(NotElement(x, Range(a, b)), d)

    Eq << ~Eq[-1]

    Eq << sets.el.imply.el.div.range.apply(Eq[-1], d)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

