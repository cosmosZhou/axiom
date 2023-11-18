from util import *


@apply
def apply(is_nonpositive, lt):
    x = is_nonpositive.of(Expr <= 0)
    M, S[x] = lt.of(Less)

    return Less(x * x, M * M)


@prove
def prove(Eq):
    from axiom import algebra

    x, M = Symbol(real=True)
    Eq << apply(x <= 0, M < x)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[0], Eq[1])

    Eq << -Eq[-1]

    Eq << algebra.le.gt.imply.gt.transit.apply(Eq[0], Eq[-1])

    Eq << algebra.lt.gt.imply.lt_zero.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    


if __name__ == '__main__':
    run()
# created on 2019-12-10
# updated on 2023-05-20
