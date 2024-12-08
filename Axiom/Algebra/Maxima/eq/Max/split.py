from util import *


@apply
def apply(self, *, cond=None, wrt=None, simplify=True):
    from Axiom.Algebra.Sum.eq.Add.split import split
    return Equal(self, split(Maxima, self, cond, wrt=wrt, simplify=simplify), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Maxima[x:A](f(x)), cond=B)

    Eq << Eq[-1].this.find(Maxima).apply(Algebra.Maxima.Piece)

    Eq << Eq[-1].this.rhs.find(Maxima).apply(Algebra.Maxima.Piece)

    Eq << Eq[-1].this.rhs.find(Maxima).apply(Algebra.Maxima.Piece)

    Eq << Eq[-1].this.rhs.apply(Algebra.Max.eq.Maxima)

    Eq << Eq[-1].this.find(Element).apply(Sets.In.equ.Or.split, B, simplify=None)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.eq.Max)


if __name__ == '__main__':
    run()
# created on 2023-04-23
