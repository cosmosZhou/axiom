from util import *


@apply
def apply(self):
    (j, i), (S[j], S[0], n), (S[i], S[0], S[n]) = self.of(Lamda[Pow])
    return Equal(self, Lamda[j:n, i:n](Binomial(i, j)) @ Lamda[j:n, i:n](Stirling(i, j) * Factorial(j)))

@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Lamda[j:n, i:n](j ** i))

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda, simplify=None)

    


if __name__ == '__main__':
    run()
# created on 2023-08-19
