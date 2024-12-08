from util import *


@apply
def apply(given):
    x, a = given.of(Abs <= Expr)

    return Element(x, Interval(-a, a))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << Sets.In_Interval.to.And.apply(Eq[1])

    Eq << Algebra.Le.Ge.to.Le.Abs.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2021-01-06
