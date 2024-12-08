from util import *


@apply
def apply(a_is_nonnegative, b_is_nonnegative):
    a, R = a_is_nonnegative.of(Element)
    nonnegative_R = Interval(0, oo)
    assert R in nonnegative_R
    b, R = b_is_nonnegative.of(Element)
    assert R in nonnegative_R
    return Element(a + b, nonnegative_R)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval(0, oo)), Element(y, Interval(0, oo)))

    Eq << Sets.In_Interval.to.Ge.apply(Eq[0])

    Eq << Sets.In_Interval.to.Ge.apply(Eq[1])

    Eq << Algebra.Ge.Ge.to.Ge.Add.apply(Eq[-1], Eq[-2])

    Eq << Sets.is_real.is_real.to.is_real.Add.apply(Eq[0], Eq[1])

    Eq << Sets.Ge_0.is_complex.to.is_nonnegative.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-03
