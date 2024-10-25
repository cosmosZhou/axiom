from util import *


@apply
def apply(is_negative, ge):
    x, R = is_negative.of(Element)
    assert R in Interval.open(-oo, 0)

    lhs, rhs = ge.of(GreaterEqual)

    return LessEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True, given=True)
    g, h = Function(real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), GreaterEqual(g(x), h(x)))

    Eq << sets.is_negative.then.lt_zero.apply(Eq[0])

    Eq << algebra.lt_zero.ge.then.le.div.apply(Eq[-1], Eq[1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2023-10-15
