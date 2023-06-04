from util import *


@apply
def apply(self):
    n, d = self.of(Ceiling[Expr / Expr])
    return Equal(self, (n + d - sign(d)) // d)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    d = Symbol(integer=True, zero=False)
    Eq << apply(ceiling(n / d))

    Eq << Eq[-1].this.lhs.apply(algebra.ceiling.to.neg.floor)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1] + (-n // d - 1)

    Eq << Eq[-1].reversed

    Eq << algebra.mod.to.sub.apply(-n % d)

    Eq << algebra.mod.to.sub.apply((d + n - sign(d)) % d)

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1].this.find(Mod).apply(algebra.mod.to.sub)

    Eq << Eq[-1].this.find(Floor).apply(algebra.floor.to.neg.ceiling)

    Eq << Eq[-1].this.find(Ceiling).apply(algebra.ceiling.to.one)

    Eq << -Eq[-1] / d









if __name__ == '__main__':
    run()
# created on 2018-05-25
# updated on 2023-05-29
