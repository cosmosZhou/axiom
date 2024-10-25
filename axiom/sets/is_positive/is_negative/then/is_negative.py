from util import *


@apply
def apply(a_is_positive, b_is_negative):
    a, R = a_is_positive.of(Element)
    RR = Interval.open(0, oo)
    assert R in RR

    b, R = b_is_negative.of(Element)
    RR = Interval.open(-oo, 0)
    assert R in RR
    return Element(a * b, RR)


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(0, oo)), Element(y, Interval.open(-oo, 0)))

    Eq << sets.el.then.el.neg.apply(Eq[1])

    Eq << sets.is_positive.is_positive.then.is_positive.apply(Eq[-1], Eq[0])

    Eq << sets.el.then.el.neg.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-04-03
