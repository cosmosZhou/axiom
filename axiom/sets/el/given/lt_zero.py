from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    [*_] = R.of(Interval[NegativeInfinity, 0])

    assert R.right_open
    assert x.is_complex
    return Less(x, 0)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)))

    Eq << sets.lt.imply.el.interval.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2021-03-01
