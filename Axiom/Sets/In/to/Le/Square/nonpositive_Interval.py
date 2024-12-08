from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    m, S[0] = interval.of(Interval)
    assert not interval.left_open
    assert not interval.right_open
    return LessEqual(x * x, m * m)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, m = Symbol(real=True)
    Eq << apply(Element(x, Interval(m, 0)))

    Eq << Sets.In_Interval.to.And.apply(Eq[0])

    Eq << Algebra.Le_0.Ge.to.Le.Square.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

# created on 2021-03-11
