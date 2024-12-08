from util import *


@apply
def apply(is_negative, ge):
    x, R = is_negative.of(Element)
    assert R in Interval.open(-oo, 0)

    lhs, rhs = ge.of(GreaterEqual)

    return LessEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True, given=True)
    g, h = Function(real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), GreaterEqual(g(x), h(x)))

    Eq << Sets.is_negative.to.Lt_0.apply(Eq[0])

    Eq << Algebra.Lt_0.Ge.to.Le.Div.apply(Eq[-1], Eq[1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2023-10-15
