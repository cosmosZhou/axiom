from util import *


@apply
def apply(given, num=1, evaluate=False):
    x = given.of(Expr > 0)
    assert num > 0
    return Greater(num / x, 0, evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, given=True)
    d = Symbol(real=True, positive=True)

    Eq << apply(x > 0, num=d)

    Eq << Eq[-1] / d

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]

    Eq << Eq[-1].apply(algebra.le_zero.gt_zero.imply.le_zero)


if __name__ == '__main__':
    run()

# created on 2018-07-19
# updated on 2018-07-19
