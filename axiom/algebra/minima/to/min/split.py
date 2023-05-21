from util import *


@apply
def apply(self, *, cond=None, wrt=None, simplify=True):
    from axiom.algebra.sum.to.add.split import split
    return Equal(self, split(Minima, self, cond, wrt=wrt, simplify=simplify), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Minima[x:A](f(x)), cond=B)

    Eq << Eq[-1].this.find(Minima).apply(algebra.minima.piece)

    Eq << Eq[-1].this.rhs.find(Minima).apply(algebra.minima.piece)

    Eq << Eq[-1].this.rhs.find(Minima).apply(algebra.minima.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.min.to.minima)

    Eq << Eq[-1].this.find(Element).apply(sets.el.to.ou.split, B, simplify=None)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.to.min)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-23
# updated on 2023-05-12
