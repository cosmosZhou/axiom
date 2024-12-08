from util import *


@apply
def apply(given):
    x, y = given.of(LessEqual)
    return LessEqual(Ceiling(x), Ceiling(y))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << ~Eq[1]

    Eq << Algebra.Gt.to.Ge.strengthen.apply(Eq[-1]) - 1

    Eq << Algebra.Gt_Sub_.Ceiling.One.apply(x)

    Eq << Algebra.Gt.Ge.to.Gt.trans.apply(Eq[-2], Eq[-1])

    Eq << Algebra.GeCeiling.apply(y)

    Eq << Algebra.Gt.Ge.to.Gt.trans.apply(Eq[-2], Eq[-1])

    Eq <<= Eq[-1] & Eq[0]



if __name__ == '__main__':
    run()
# created on 2021-12-27
# updated on 2021-12-27