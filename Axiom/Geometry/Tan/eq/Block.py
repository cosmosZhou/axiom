from util import *


@apply
def apply(self):
    from Axiom.Geometry.Sin.eq.Block import rewrite
    return Equal(self, rewrite(Tan, self))


@prove
def prove(Eq):
    from Axiom import Algebra, Geometry

    n = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(n, n))
    Eq << apply(Tan(BlockMatrix([[A, B], [C, D]])))

    i = Symbol(domain=Range(n * 2))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[-1], i)

    j = Symbol(domain=Range(n * 2))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[-1], j)

    Eq << Eq[-1].this.lhs.apply(Geometry.Tan.eq.Ite)

    Eq << Eq[-1].this.find(Tan[Piecewise]).apply(Geometry.Tan.eq.Ite)

    Eq << Eq[-1].this.find(Tan[Piecewise]).apply(Geometry.Tan.eq.Ite, simplify=0)




if __name__ == '__main__':
    run()
# created on 2023-06-08
