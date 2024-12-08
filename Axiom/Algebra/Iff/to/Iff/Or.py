from util import *


@apply
def apply(self, *, cond=None):
    p, q = self.of(Iff)
    return Iff(p | cond, q | cond)


@prove
def prove(Eq):
    from Axiom import Algebra

    p, q, r = Symbol(bool=True)
    Eq << apply(Iff(p, q), cond=r)

    Eq << Algebra.Iff.to.Imply.apply(Eq[0])

    Eq << Algebra.Imply.to.Imply.Or.apply(Eq[-1], cond=r)

    Eq << Algebra.Iff.to.Given.apply(Eq[0])

    Eq << Algebra.Given.to.Given.Or.apply(Eq[-1], cond=r)

    Eq << Algebra.Iff.of.And.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2022-01-27
