from util import *


@apply
def apply(self, i, j):
    A, S[A.T] = self.of(Expr - Expr)
    k, S[k] = A.shape
    return Equal(self, Lamda[j:k, i:k](A[i, j] - A[j, i]))



@prove
def prove(Eq):
    from Axiom import Algebra

    k = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    A = Symbol(real=True, shape=(k, k))
    Eq << apply(A - A.T, i, j)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lamda.eq.Add)




if __name__ == '__main__':
    run()
# created on 2023-05-24
# updated on 2023-08-28
