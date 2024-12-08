from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)

    return Greater(Ceiling(x), 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(real=True, given=True)
    Eq << apply(x > 0)

    Eq << Algebra.Gt_0.to.Ge_0.apply(Eq[0])

    Eq << Algebra.Ge_0.to.Ge_0.Ceiling.apply(Eq[-1])

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Sets.Eq_.Ceiling.Zero.to.In.apply(Eq[-1])
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2019-08-12
