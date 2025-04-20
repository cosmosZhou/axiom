from util import *


@apply
def apply(self, i, j):
    ((Q, KT), d_z), V = self.of(Softmax[Expr @ Expr / Expr ** S.Half] @ Expr)
    n, S[d_z] = V.shape
    return Equal(self, Lamda[j:d_z, i:n](softmax(Q[i] @ KT / sqrt(d_z)) @ V[:, j]))


@prove
def prove(Eq):
    from Axiom import Algebra

    n, d_z = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Q, K, V = Symbol(shape=(n, d_z), real=True)
    Eq << apply(softmax(Q @ K.T / sqrt(d_z)) @ V, i, j)

    i = Symbol(domain=Range(n))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[0], i)

    j = Symbol(domain=Range(d_z))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[-1], j)




if __name__ == '__main__':
    run()
# created on 2023-05-22
