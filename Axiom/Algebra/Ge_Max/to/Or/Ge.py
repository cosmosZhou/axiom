from util import *


@apply
def apply(given, index=-1):
    args, x = given.of(Max >= Expr)
    first = args[:index]
    second = args[index:]

    return GreaterEqual(Max(*first), x) | GreaterEqual(Max(*second), x)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Max(y, z) >= x)

    Eq << ~Eq[1]

    Eq << Eq[-1].this.apply(Algebra.Lt.Lt.to.Lt.Max)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2022-01-02
