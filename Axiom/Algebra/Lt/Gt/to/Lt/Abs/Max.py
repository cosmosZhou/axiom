from util import *


@apply
def apply(lt, gt):
    x, a = lt.of(Less)
    S[x], b = gt.of(Greater)
    return Less(abs(x), Max(abs(a), abs(b)))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(x < a, x > b)

    Eq << Algebra.Lt_Abs.of.And.apply(Eq[-1])

    Eq <<= ~Eq[-2], -~Eq[-1]

    Eq <<= Algebra.Ge.to.Ge.relax.apply(Eq[-2], abs(a)), -Algebra.Ge.to.Ge.relax.apply(Eq[-1], abs(b))

    Eq <<= Algebra.Lt.Ge.to.Gt.trans.apply(Eq[0], Eq[-2]), -Algebra.Gt.Le.to.Lt.trans.apply(Eq[1], Eq[-1])

    Eq <<= Algebra.Le_Abs.apply(a), Algebra.Le_Abs.apply(b, negate=True)

    Eq <<= Eq[-2] & Eq[-4], Eq[-1] & Eq[-3]


if __name__ == '__main__':
    run()
# created on 2019-12-19
# updated on 2023-04-17