from util import *


@apply
def apply(a_is_negative, b_is_negative):
    a, R = a_is_negative.of(Element)
    negative_R = Interval.open(-oo, 0)
    assert R in negative_R
    b, R = b_is_negative.of(Element)
    assert R in negative_R
    return Element(a + b, negative_R)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), Element(y, Interval.open(-oo, 0)))

    Eq << Sets.In_Interval.to.Lt.apply(Eq[0])

    Eq << Sets.In_Interval.to.Lt.apply(Eq[1])

    Eq << Algebra.Lt.Lt.to.Lt.Add.apply(Eq[-1], Eq[-2])
    Eq << Sets.is_real.is_real.to.is_real.Add.apply(Eq[0], Eq[1])
    Eq << Sets.Lt_0.is_complex.to.is_negative.apply(Eq[-2], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-05-03
