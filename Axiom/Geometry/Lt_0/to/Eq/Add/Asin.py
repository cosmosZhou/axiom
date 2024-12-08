from util import *


@apply
def apply(is_negative):
    x = is_negative.of(Expr < 0)
    assert x in Interval(-1, 1)
    return Equal(asin(sqrt(1 - x ** 2)) - asin(x), S.Pi / 2)


@prove
def prove(Eq):
    from Axiom import Algebra, Geometry

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(x < 0)

    Eq << Algebra.Lt_0.to.Le_0.apply(Eq[0])
    Eq << Geometry.Le_0.to.Eq.Add.Asin.apply(Eq[-1])

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-07-13
