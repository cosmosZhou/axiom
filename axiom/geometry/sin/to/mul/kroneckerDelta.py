from util import *


@apply
def apply(self):
    (i, j), x = self.of(sin[KroneckerDelta * Expr])
    return Equal(self, KroneckerDelta(i, j) * sin(x), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(sin(x * KroneckerDelta(i, j)))

    Eq << Eq[-1].this.find(KroneckerDelta).apply(algebra.kroneckerDelta.to.piece)

    Eq << Eq[-1].this.find(KroneckerDelta).apply(algebra.kroneckerDelta.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.piece)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.piece)


if __name__ == '__main__':
    run()
# created on 2023-06-08
