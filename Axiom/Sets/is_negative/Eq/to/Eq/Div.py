from util import *


@apply
def apply(is_negative, equality):
    x, R = is_negative.of(Element)
    assert R in Interval.open(-oo, 0)

    lhs, rhs = equality.of(Equal)

    return Equal(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(real=True, given=True)
    g, h = Function(real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), Equal(g(x), h(x)))

    Eq << Sets.is_negative.to.Ne_0.apply(Eq[0])

    Eq << Algebra.Ne_0.Eq.to.Eq.Div.apply(Eq[-1], Eq[1], simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-06-06
