from util import *


@apply
def apply(is_positive, gt):
    x, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)

    lhs, rhs = gt.of(Greater)

    return Greater(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True, given=True)
    g, h = Function(real=True)
    Eq << apply(Element(x, Interval.open(0, oo)), Greater(g(x), h(x)))

    Eq << sets.is_positive.then.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.gt.then.gt.div.apply(Eq[-1], Eq[1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2023-10-15
