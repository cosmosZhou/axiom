from util import *


@apply
def apply(ge_a, ge_b):
    x, a = ge_a.of(GreaterEqual)
    y, b = ge_b.of(GreaterEqual)
    return Max(x, y) >= Max(a, b)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, a, b = Symbol(real=True, given=True)
    Eq << apply(x >= a, y >= b)

    Eq << algebra.le.le.imply.le.min.apply(-Eq[0], -Eq[1])

    Eq << Eq[-1].this.lhs.apply(algebra.min.to.mul.max)

    Eq << Eq[-1].this.rhs.apply(algebra.min.to.mul.max)

    Eq << -Eq[-1]




if __name__ == '__main__':
    run()
# created on 2019-05-16
# updated on 2023-04-23

