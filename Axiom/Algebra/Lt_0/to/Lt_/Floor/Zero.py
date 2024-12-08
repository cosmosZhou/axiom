from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)

    return Less(Floor(x), 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(real=True, given=True)
    Eq << apply(x < 0)

    Eq << Algebra.Lt_0.to.Le_0.apply(Eq[0])

    Eq << Algebra.Le_0.to.Le_.Floor.Zero.apply(Eq[-1])

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Sets.Eq_.Floor.Zero.to.In.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2020-01-20
