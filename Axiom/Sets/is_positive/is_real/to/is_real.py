from util import *


@apply
def apply(is_positive, is_real):
    a, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)
    b, R = is_real.of(Element)
    assert R in Reals
    return Element(b / a, Reals)


@prove
def prove(Eq):
    from Axiom import Sets

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval.open(0, oo)), Element(y, Interval(-oo, oo)))

    Eq << Sets.is_positive.to.is_positive.Div.apply(Eq[0])

    Eq << Sets.is_real.is_real.to.is_real.apply(Eq[-1], Eq[1])




if __name__ == '__main__':
    run()
# created on 2023-05-03
