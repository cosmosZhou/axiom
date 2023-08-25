from util import *


@apply
def apply(self):
    from axiom.geometry.sin.to.block import rewrite
    return Equal(self, rewrite(Cot, self))


@prove
def prove(Eq):
    from axiom import algebra, geometry

    n = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(n, n))
    Eq << apply(Cot(BlockMatrix([[A, B], [C, D]])))

    i = Symbol(domain=Range(n * 2))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    j = Symbol(domain=Range(n * 2))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)

    Eq << Eq[-1].this.lhs.apply(geometry.cot.to.piece)

    Eq << Eq[-1].this.find(Cot[Piecewise]).apply(geometry.cot.to.piece)

    Eq << Eq[-1].this.find(Cot[Piecewise]).apply(geometry.cot.to.piece, simplify=0)

    


if __name__ == '__main__':
    run()
# created on 2023-06-08
