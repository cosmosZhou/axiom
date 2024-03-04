from util import *


@apply
def apply(self):
    (n, dk), d = self.of(Mod[Mod])
    k = dk / d
    assert k.is_integer
    return Equal(self, n % d)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    d, k = Symbol(integer=True)
    Eq << apply(Mod(n % (d * k), d, evaluate=False))

    Eq << Eq[0].this.find(Mod).apply(algebra.mod.to.sub)

    Eq << Eq[-1].this.find(Mod).apply(algebra.mod.to.sub)

    Eq << Eq[-1].this.find(Mod).apply(algebra.mod.to.sub)

    Eq << Eq[-1].this.find(Mod).apply(algebra.mod.to.sub)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)


if __name__ == '__main__':
    run()
# created on 2023-12-26
