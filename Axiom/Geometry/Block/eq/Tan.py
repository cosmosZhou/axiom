from util import *


@apply
def apply(self):
    from Axiom.Algebra.Block.eq.Exp import extract
    return Equal(self, Tan(extract(Tan, self)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Geometry

    n = Symbol(positive=True, integer=True)
    A, B, C, D = Symbol(shape=(n, n), real=True)
    Eq << apply(BlockMatrix([[Tan(A), Tan(B)], [Tan(C), Tan(D)]]))

    Eq << Eq[-1].this.rhs.apply(Geometry.Tan.eq.Block)


if __name__ == '__main__':
    run()
# created on 2023-06-08
