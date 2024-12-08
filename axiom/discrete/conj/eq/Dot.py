from util import *


@apply
def apply(self):
    args = self.of(Conjugate[MatMul])
    return Equal(self, MatMul(*(~a for a in args)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Discrete

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(complex=True, shape=(n, n))
    Eq << apply(Conjugate(A @ B, evaluate=False))

    Eq << Eq[0].this.rhs.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.find(MatMul).apply(Discrete.Dot.eq.Lamda)






if __name__ == '__main__':
    run()
# created on 2023-06-23
# updated on 2023-06-24
