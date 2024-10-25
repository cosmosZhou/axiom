from util import *


@apply(simplify=None)
def apply(given):
    x, a = given.of(Abs > Expr)
    return Or(x < -a, x > a)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) > a)

    Eq << ~Eq[1]

    Eq << Eq[-1].this.apply(algebra.le.ge.then.le.abs)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2018-07-31
