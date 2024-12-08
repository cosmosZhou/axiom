from util import *


@apply
def apply(b_greater_than_x, x_greater_than_a):
    b, x = b_greater_than_x.of(Greater)
    _x, a = x_greater_than_a.of(GreaterEqual)
    if b == a:
        b, x, _x, a = _x, a, b, x
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(b > x, x >= a)

    Eq << ~Eq[-1]

    Eq << Algebra.Ge.Le.to.Le.trans.apply(Eq[1], Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2018-05-30
