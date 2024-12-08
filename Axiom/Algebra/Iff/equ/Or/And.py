from util import *


@apply
def apply(self):
    p, q = self.of(Iff)
    return (p.invert() & q.invert()) | (p & q)


@prove
def prove(Eq):
    from Axiom import Algebra

    p, q = Symbol(bool=True)
    Eq << apply(Iff(p, q))

    Eq << Eq[0].this.lhs.apply(Algebra.Iff.equ.And.Or)

    Eq << Eq[-1].this.lhs.apply(Algebra.And.equ.Or)




if __name__ == '__main__':
    run()
# created on 2022-01-27
