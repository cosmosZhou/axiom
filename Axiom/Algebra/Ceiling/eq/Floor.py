from util import *


@apply
def apply(self):
    n, d = self.of(Ceiling[Expr / Expr])
    return Equal(self, (n + d - sign(d)) // d)


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True)
    d = Symbol(integer=True, zero=False)
    Eq << apply(ceiling(n / d))

    Eq << Eq[-1].this.lhs.apply(Algebra.Ceiling.eq.Neg.Floor)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1] + (-n // d - 1)

    Eq << Eq[-1].reversed

    Eq << Algebra.Mod.eq.Sub.apply(-n % d)

    Eq << Algebra.Mod.eq.Sub.apply((d + n - sign(d)) % d)

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1].this.find(Mod).apply(Algebra.Mod.eq.Sub)

    Eq << Eq[-1].this.find(Floor).apply(Algebra.Floor.eq.Neg.Ceiling)

    Eq << Eq[-1].this.find(Ceiling).apply(Algebra.Ceiling.eq.One)

    Eq << -Eq[-1] / d









if __name__ == '__main__':
    run()
# created on 2018-05-25
# updated on 2023-05-29
