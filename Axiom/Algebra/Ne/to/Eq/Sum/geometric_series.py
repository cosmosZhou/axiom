from util import *


@apply
def apply(ne, self):
    λ = ne.of(Unequal[1])
    (S[λ], k), (S[k], S[0], n) = self.of(Sum[Pow])
    return Equal(self, (1 - λ ** n) / (1 - λ), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    k, n = Symbol(integer=True)
    λ = Symbol(real=True)
    Eq << apply(Unequal(λ, 1), Sum[k:n](λ ** k))

    Eq << (λ ** (k + 1)).this.apply(Algebra.Pow.eq.Mul.split.exponent)

    Eq << Eq[-1] - λ ** k

    Eq << -Eq[-1].reversed

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Mul)

    Eq << -Algebra.Ne.to.Ne_0.apply(Eq[0])

    Eq << Algebra.Ne_0.Eq.to.Eq.Div.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Eq.to.Eq.Sum.apply(Eq[-1], (k, 0, n))

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.rhs.find(Sum[Pow[Add]]).apply(Algebra.Sum.limits.subs.offset, -1)



if __name__ == '__main__':
    run()
# created on 2023-04-08
# updated on 2023-04-15
