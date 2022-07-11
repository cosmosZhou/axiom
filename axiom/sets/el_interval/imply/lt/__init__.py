from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)

    if interval.right_open:
        return Less(x, b)
    else:
        if interval.left_open:
            return Less(a, x)

@prove
def prove(Eq):
    from axiom import sets

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << sets.el_interval.imply.et.apply(Eq[0])




if __name__ == '__main__':
    run()

# created on 2020-04-18

from . import square
