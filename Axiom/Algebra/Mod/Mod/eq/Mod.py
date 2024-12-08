from util import *


@apply
def apply(self):
    (n, dk), d = self.of(Mod[Mod])
    k = dk / d
    assert k.is_integer
    return Equal(self, n % d)


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True)
    d, k = Symbol(integer=True)
    Eq << apply(Mod(n % (d * k), d, evaluate=False))

    Eq << Eq[0].this.find(Mod).apply(Algebra.Mod.eq.Sub)

    Eq << Eq[-1].this.find(Mod).apply(Algebra.Mod.eq.Sub)

    Eq << Eq[-1].this.find(Mod).apply(Algebra.Mod.eq.Sub)

    Eq << Eq[-1].this.find(Mod).apply(Algebra.Mod.eq.Sub)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)


if __name__ == '__main__':
    run()
# created on 2023-12-26
