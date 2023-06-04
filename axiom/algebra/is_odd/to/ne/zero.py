from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 1])
    return Unequal(n % 2, 0)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 1))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.eq.imply.ne_zero)

    Eq << Eq[-1].this.lhs.apply(algebra.ne_zero.imply.is_odd)


if __name__ == '__main__':
    run()
# created on 2023-05-30
