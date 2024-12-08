from util import *


@apply
def apply(given):
    y, fx = given.of(Equal)
    if not fx.is_Ceiling:
        y, fx = fx, y
    assert y.is_integer
    x = fx.of(Ceiling)
    return x + 1 > y, y >= x


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    y = Symbol(integer=True)
    Eq << apply(Equal(y, ceiling(x)))



    Eq <<= -Eq[-2], -Eq[-1]

    Eq << Algebra.Lt.Le.to.Eq.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Floor.eq.Neg.Ceiling)


if __name__ == '__main__':
    run()
# created on 2019-03-08
