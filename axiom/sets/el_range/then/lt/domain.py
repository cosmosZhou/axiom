from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    a, b = interval.of(Range)
    assert interval.right_open
    return a < b


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, a, b = Symbol(integer=True)
    Eq << apply(Element(x, Range(a, b)))

    Eq << sets.el_range.then.et.apply(Eq[0])

    Eq << algebra.ge.lt.then.lt.trans.apply(*Eq[-2:])


if __name__ == '__main__':
    run()
# created on 2023-11-12
