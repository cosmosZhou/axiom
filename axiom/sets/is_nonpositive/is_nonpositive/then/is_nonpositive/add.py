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
    from axiom import sets, algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval(-oo, 0)), Element(y, Interval(-oo, 0)))

    Eq << sets.el_interval.then.le.apply(Eq[0])

    Eq << sets.el_interval.then.le.apply(Eq[1])

    Eq << algebra.le.le.then.le.add.apply(Eq[-1], Eq[-2])

    Eq << sets.is_real.is_real.then.is_real.add.apply(Eq[0], Eq[1])

    Eq << sets.le_zero.is_complex.then.is_nonpositive.apply(Eq[-2], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-03
