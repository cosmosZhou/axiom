from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)

    return Greater(Ceil(x), 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    x = Symbol(real=True, given=True)
    Eq << apply(x > 0)

    Eq << Algebra.Ge_0.of.Gt_0.apply(Eq[0])

    Eq << Algebra.Ge_0.Ceil.of.Ge_0.apply(Eq[-1])

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Set.Mem.of.Ceil.eq.Zero.apply(Eq[-1])
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2019-08-12
