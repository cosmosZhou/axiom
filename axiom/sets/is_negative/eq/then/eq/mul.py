from util import *


@apply
def apply(is_negative, equality):
    x, R = is_negative.of(Element)
    assert R in Interval.open(-oo, 0)

    lhs, rhs = equality.of(Equal)

    return Equal((x * lhs).expand(), (x * rhs).expand())


@prove
def prove(Eq):
    from axiom import sets, algebra
    sets.is_negative
    x = Symbol(real=True, given=True)
    g, h = Function(real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), Equal(g(x), h(x)))

    Eq << sets.is_negative.then.ne_zero.apply(Eq[0])

    Eq << algebra.ne_zero.eq.then.eq.mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-06-06
