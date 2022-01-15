from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    return Equal(abs(x), x)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)

    Eq << apply(x >= 0)

    Eq << Eq[-1].this.lhs.apply(algebra.abs.to.piece)

    Eq << algebra.cond.given.et.restrict.apply(Eq[-1], cond=Eq[0])

    Eq << algebra.et.given.et.subs.bool.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-06-16
