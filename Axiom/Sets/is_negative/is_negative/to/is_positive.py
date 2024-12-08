from util import *


@apply
def apply(a_is_negative, b_is_negative):
    a, R = a_is_negative.of(Element)
    RR = Interval.open(-oo, 0)
    assert R in RR

    b, R = b_is_negative.of(Element)
    assert R in RR

    return Element(a * b, -RR)


@prove
def prove(Eq):
    from Axiom import Sets

    x, y = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), Element(y, Interval.open(-oo, 0)))

    Eq << Sets.In.to.In.Neg.apply(Eq[0])

    Eq << Sets.In.to.In.Neg.apply(Eq[1])

    Eq << Sets.is_positive.is_positive.to.is_positive.apply(Eq[-1], Eq[-2])






if __name__ == '__main__':
    run()
# created on 2022-04-03
