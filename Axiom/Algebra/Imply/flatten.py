from util import *


@apply
def apply(self, *, simplify=True):
    A, (p, q) = self.of(Imply[Basic, Imply])
    p &= A
    if simplify:
        p = p.simplify()
    return Imply(p, q)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True)
    A, B, C = Symbol(etype=dtype.real)
    Eq << apply(Imply(Element(x, A), Imply(Element(y, B), Element(z, C))))

    Eq << Eq[-1].this.find(Imply[~Imply]).apply(Algebra.Imply.equ.Or)

    Eq << Eq[-1].this.lhs.apply(Algebra.Imply.equ.Or)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.equ.Or)


if __name__ == '__main__':
    run()
# created on 2018-08-29
