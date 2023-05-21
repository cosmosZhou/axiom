from util import *


@apply
def apply(a_is_negative, b_is_negative):
    a, R = a_is_negative.of(Element)
    RR = Interval(-oo, 0, right_open=True)
    assert R in RR
    
    b, R = b_is_negative.of(Element)
    assert R in RR
    
    return Element(a * b, -RR)


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval(-oo, 0, right_open=True)), Element(y, Interval(-oo, 0, right_open=True)))

    Eq << sets.el.imply.el.neg.apply(Eq[0])

    Eq << sets.el.imply.el.neg.apply(Eq[1])

    Eq << sets.is_positive.is_positive.imply.is_positive.apply(Eq[-1], Eq[-2])






if __name__ == '__main__':
    run()
# created on 2022-04-03
