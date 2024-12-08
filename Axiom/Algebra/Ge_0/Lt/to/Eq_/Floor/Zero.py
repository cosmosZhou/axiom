from util import *


@apply
def apply(is_nonnegative, less_than):
    if not less_than.is_Less:
        less_than, is_nonnegative = given

    x = is_nonnegative.of(Expr >= 0)
    S[x], M = less_than.of(Less)

    return Equal(Floor(x), 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0, x < 1)

    Eq << Algebra.LeFloor.apply(x)

    Eq << Algebra.Le.Lt.to.Lt.trans.apply(Eq[-1], Eq[1])

    Eq << Algebra.Lt.to.Le.strengthen.apply(Eq[-1])

    Eq << Algebra.Floor.gt.Sub_1.apply(x)

    Eq << Algebra.Gt.Ge.to.Gt.trans.apply(Eq[-1], Eq[0] - 1)

    Eq << Algebra.Gt.to.Ge.strengthen.apply(Eq[-1])
    Eq <<= Eq[-4] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-10-21
