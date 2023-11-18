from util import *


@apply
def apply(given, k=None):
    n = given.of(Unequal[Expr % 2, 0])
    if k is None:
        k = Symbol(integer=True)

    return Any[k](Equal(n, k * 2 + 1))


@prove
def prove(Eq):
    from axiom import algebra

    # n = q * d + r
    n = Symbol(integer=True, given=True)
    r = Symbol(integer=True)
    Eq << apply(Unequal(n % 2, 0))

    Eq << Eq[1].this.expr.apply(algebra.eq.imply.eq.mod, 2)

    Eq << algebra.eq.imply.ne_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-26
