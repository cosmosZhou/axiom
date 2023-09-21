from util import *


@apply
def apply(self):
    (j, i), (S[j], S[0], m), (S[i], S[0], d) = self.of(Lamda[Pow])
    return Equal(self, Lamda[j:d, i:d](Stirling(i, j) * Factorial(j)) @ Lamda[j:m, i:d](Binomial(j, i)))

@prove
def prove(Eq):
    from axiom import discrete
    
    m, d = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Lamda[j:m, i:d](j ** i))
    
    x = Symbol(real=True)
    Eq << discrete.lamda.mul.to.matmul.lamda.stirling.apply(Lamda[j:m, i:d](j ** i * x ** j))
    
    Eq << Eq[1].subs(x, 1)


if __name__ == '__main__':
    run()
# created on 2023-08-28
