from util import *


@apply
def apply(self):
    p, q = self.of(Iff)
    return And(Imply(p, q), Imply(q, p))


@prove
def prove(Eq):
    from Axiom import Algebra

    p, q = Symbol(bool=True)
    Eq << apply(Iff(p, q))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(Algebra.Imply.Imply.of.Iff)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.Imply.to.Iff)


if __name__ == '__main__':
    run()
# created on 2022-01-27
