from util import *


@apply
def apply(given):
    a, b = given.of(LessEqual)

    return Equal(Min(a, b), a)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << Eq[-1].this.lhs.apply(algebra.min.to.piece)
    Eq <<= Eq[0] & Eq[-1]
    Eq << algebra.et.given.et.subs.bool.apply(Eq[-1], index=1)


if __name__ == '__main__':
    run()
# created on 2018-10-14
