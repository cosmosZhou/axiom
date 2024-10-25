from util import *


@apply
def apply(self):
    n = self.of(Equal[Expr % 2, 0])
    return Equal((-1) ** n, 1)


@prove
def prove(Eq):
    from axiom import algebra
#     n = q * d + r
    n = Symbol(integer=True)

    Eq << apply(Equal(n % 2, 0))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.is_even.then.eq.pow)

    Eq << Eq[-1].this.rhs.apply(algebra.is_even.of.eq)


if __name__ == '__main__':
    run()
# created on 2019-10-11
