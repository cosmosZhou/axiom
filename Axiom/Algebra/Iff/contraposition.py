from util import *


@apply
def apply(self):
    p, q = self.of(Iff)
    return Iff(q.invert(), p.invert())


@prove
def prove(Eq):
    from Axiom import Algebra

    p, q = Symbol(bool=True)
    Eq << apply(Iff(p, q))

    Eq << Eq[0].this.lhs.apply(Algebra.Iff.equ.Or.And)

    Eq << Eq[-1].this.rhs.apply(Algebra.Iff.equ.Or.And)


if __name__ == '__main__':
    run()
# created on 2022-01-27