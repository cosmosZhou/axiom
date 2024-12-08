from util import *


@apply
def apply(ge, gt):
    b, x = ge.of(GreaterEqual)
    _x, a = gt.of(Greater)
    if x != _x:
        b, x, S[x], a = _x, a, b, x
    return Greater(b, a)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(x >= b, a > x)

    Eq << ~Eq[-1]

    Eq << Algebra.Ge.Le.to.Ge.trans.apply(Eq[0], Eq[-1])

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()
# created on 2018-03-13
