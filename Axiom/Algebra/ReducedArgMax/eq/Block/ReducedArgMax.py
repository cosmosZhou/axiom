from util import *


@apply
def apply(self):
    assert self.shape
    args = self.of(ReducedArgMax[BlockMatrix])

    return Equal(self, BlockMatrix([ReducedArgMax(arg) for arg in args]))


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b, n = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(a, n))
    B = Symbol(real=True, shape=(b, n))
    Eq << apply(ReducedArgMax(BlockMatrix(A, B)))

    i = Symbol(domain=Range(a + b))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedArgMax.eq.Ite.ReducedArgMax)





if __name__ == '__main__':
    run()
# created on 2021-12-20
