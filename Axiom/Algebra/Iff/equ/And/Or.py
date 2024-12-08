from util import *


@apply
def apply(self):
    p, q = self.of(Iff)
    return (p.invert() | q) & (q.invert() | p)


@prove
def prove(Eq):
    from Axiom import Algebra

    p, q = Symbol(bool=True)
    Eq << apply(Iff(p, q))

    Eq << Eq[0].this.lhs.apply(Algebra.Iff.equ.And.Imply)

    Eq << Eq[-1].this.find(Imply).apply(Algebra.Imply.equ.Or)

    Eq << Eq[-1].this.find(Imply).apply(Algebra.Imply.equ.Or)


if __name__ == '__main__':
    run()
# created on 2022-01-27
