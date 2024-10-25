from util import *


@apply
def apply(is_positive, equality):
    x, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)

    lhs, rhs = equality.of(Equal)

    return Equal((x * lhs).expand(), (x * rhs).expand())


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True, given=True)
    g, h = Function(real=True)
    Eq << apply(Element(x, Interval.open(0, oo)), Equal(g(x), h(x)))

    Eq << sets.is_positive.then.ne_zero.apply(Eq[0])

    Eq << algebra.ne_zero.eq.then.eq.mul.apply(Eq[-1], Eq[1])




if __name__ == '__main__':
    run()
# created on 2023-06-06
