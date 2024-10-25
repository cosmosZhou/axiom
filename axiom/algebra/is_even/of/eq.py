from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 0])
    return Equal((-1) ** n, 1)


@prove
def prove(Eq):
    from axiom import algebra
#     n = q * d + r
    n = Symbol(integer=True, given=True)

    Eq << apply(Equal(n % 2, 0))

    Eq << ~Eq[0]

    Eq << algebra.ne_zero.then.is_odd.apply(Eq[-1])

    Eq << algebra.is_odd.then.eq.pow.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()
# created on 2019-10-10
