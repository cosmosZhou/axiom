from util import *


@apply
def apply(lt):
    x, a = lt.of(Less)
    return Greater(a, x)


@prove
def prove(Eq):
    x, a = Symbol(real=True, given=True)
    Eq << apply(x < a)

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2019-07-17
# updated on 2019-07-17
