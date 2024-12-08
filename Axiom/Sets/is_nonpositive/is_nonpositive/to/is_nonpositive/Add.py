from util import *


@apply
def apply(a_is_nonpositive, b_is_nonpositive):
    a, R = a_is_nonpositive.of(Element)
    nonpositive_R = Interval(-oo, 0)
    assert R in nonpositive_R
    b, R = b_is_nonpositive.of(Element)
    assert R in nonpositive_R
    return Element(a + b, nonpositive_R)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval(-oo, 0)), Element(y, Interval(-oo, 0)))

    Eq << Sets.In_Interval.to.Le.apply(Eq[0])

    Eq << Sets.In_Interval.to.Le.apply(Eq[1])

    Eq << Algebra.Le.Le.to.Le.Add.apply(Eq[-1], Eq[-2])

    Eq << Sets.is_real.is_real.to.is_real.Add.apply(Eq[0], Eq[1])

    Eq << Sets.Le_0.is_complex.to.is_nonpositive.apply(Eq[-2], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-03
