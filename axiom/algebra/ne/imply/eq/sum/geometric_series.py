from util import *


@apply
def apply(ne, self):
    λ = ne.of(Unequal[1])
    (S[λ], k), (S[k], S[0], n) = self.of(Sum[Pow])
    return Equal(self, (1 - λ ** n) / (1 - λ), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    k, n = Symbol(integer=True)
    λ = Symbol(real=True)
    Eq << apply(Unequal(λ, 1), Sum[k:n](λ ** k))

    Eq << (λ ** (k + 1)).this.apply(algebra.pow.to.mul.split.exponent)

    Eq << Eq[-1] - λ ** k

    Eq << -Eq[-1].reversed

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.mul)

    Eq << -algebra.ne.imply.ne_zero.apply(Eq[0])

    Eq << algebra.ne_zero.eq.imply.eq.div.apply(Eq[-1], Eq[-2])

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (k, 0, n))

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.find(Sum[Pow[Add]]).apply(algebra.sum.limits.subs.offset, -1)
    


if __name__ == '__main__':
    run()
# created on 2023-04-08
# updated on 2023-04-15
