from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive
    assert d.is_integer

    e, (a, b) = given.of(Element[Range])
    e /= d
    # assert e.is_integer

    b -= 1

    return Element(e, Range(start=ceiling(a / d), stop=b // d + 1))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(d * x, Range(a, b + 1)), d)

    Eq << sets.el_range.then.et.apply(Eq[0])

    Eq << algebra.lt.then.le.strengthen.apply(Eq[-1])

    Eq <<= Eq[-3] / d, Eq[-1] / d

    Eq <<= algebra.ge.then.ge.ceiling.integer.apply(Eq[-2]), algebra.le.then.le.floor.integer.apply(Eq[-1])

    Eq << sets.ge.le.then.el.range.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-05-24
