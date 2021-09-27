from util import *


@apply
def apply(gt):
    x, a = gt.of(Greater)
    return Less(a, x)


@prove
def prove(Eq):
    x, a = Symbol(real=True, given=True)
    Eq << apply(x > a)

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
