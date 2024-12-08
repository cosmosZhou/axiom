from util import *


@apply
def apply(a_is_positive, b_is_positive):
    a, R = a_is_positive.of(Element)
    positive_R = Interval.open(0, oo)
    assert R in positive_R
    b, R = b_is_positive.of(Element)
    assert R in positive_R
    return Element(a + b, positive_R)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval.open(0, oo)), Element(y, Interval.open(0, oo)))

    Eq << Sets.In_Interval.to.Gt.apply(Eq[0])

    Eq << Sets.In_Interval.to.Gt.apply(Eq[1])

    Eq << Algebra.Gt.Gt.to.Gt.Add.apply(Eq[-1], Eq[-2])

    Eq << Sets.is_real.is_real.to.is_real.Add.apply(Eq[0], Eq[1])

    Eq << Sets.Gt_0.is_complex.to.is_positive.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-03
