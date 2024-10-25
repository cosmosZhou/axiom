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
    from axiom import sets, algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval(0, oo)), Element(y, Interval(0, oo)))

    Eq << sets.el_interval.then.ge.apply(Eq[0])

    Eq << sets.el_interval.then.ge.apply(Eq[1])

    Eq << algebra.ge.ge.then.ge.add.apply(Eq[-1], Eq[-2])

    Eq << sets.is_real.is_real.then.is_real.add.apply(Eq[0], Eq[1])

    Eq << sets.ge_zero.is_complex.then.is_nonnegative.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-03
