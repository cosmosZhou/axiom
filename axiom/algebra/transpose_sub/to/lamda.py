from util import *


@apply
def apply(self, i, j):
    A, S[A] = self.of(Transpose - Expr)
    k, S[k] = A.shape
    return Equal(self, Lamda[j:k, i:k](A[j, i] - A[i, j]))



@prove
def prove(Eq):
    from axiom import algebra
    
    k = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    A = Symbol(real=True, shape=(k, k))
    Eq << apply(A.T - A, i, j)
    
    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.add)


if __name__ == '__main__':
    run()
# created on 2023-05-24
