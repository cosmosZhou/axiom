from util import *


@apply
def apply(given, n):
    from axiom.discrete.then.gt_zero.alpha import alpha
    (x, j), S[j] = given.of(All[Indexed > 0, Tuple[1, oo]])
    assert n > 0
    return Greater(alpha(x[:2 * n]), alpha(x[:2 * n + 2]))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(All[i:1:oo](x[i] > 0), n)
    return
    Eq << discrete.imply.suffice.is_positive.K.apply(x[:n])

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-09-13
