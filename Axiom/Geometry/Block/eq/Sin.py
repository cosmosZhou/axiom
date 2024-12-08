from util import *


@apply
def apply(self):
    from Axiom.Algebra.Block.eq.Exp import extract
    return Equal(self, Sin(extract(Sin, self)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Geometry

    n = Symbol(positive=True, integer=True)
    A, B, C, D = Symbol(shape=(n, n), real=True)
    Eq << apply(BlockMatrix([[Sin(A), Sin(B)], [Sin(C), Sin(D)]]))

    Eq << Eq[-1].this.rhs.apply(Geometry.Sin.eq.Block)


if __name__ == '__main__':
    run()
# created on 2023-06-08
