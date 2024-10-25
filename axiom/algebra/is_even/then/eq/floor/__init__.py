from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 0])
    return Equal(n // 2, n / 2)


@prove
def prove(Eq):
    from axiom import algebra

    # n = q * d + r
    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 0))

    Eq << algebra.is_even.then.any.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(algebra.eq.then.eq.div, 2, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.then.eq.floor, ret=0)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.then.eq.trans)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-10-10
from . import one
