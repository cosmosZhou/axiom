from util import *


@apply
def apply(is_negative, gt):
    x, R = is_negative.of(Element)
    assert R in Interval.open(-oo, 0)

    lhs, rhs = gt.of(Greater)

    return Less(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True, given=True)
    g, h = Function(real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), Greater(g(x), h(x)))

    Eq << Sets.is_negative.to.Lt_0.apply(Eq[0])

    Eq << Algebra.Lt_0.Gt.to.Lt.Div.apply(Eq[-1], Eq[1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2023-10-15