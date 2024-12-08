from util import *


@apply
def apply(self):
    (((j, i), (x, S[j])), (S[j], S[0], m), (S[i], S[0], d)), (((S[-x], S[j - i]), (S[j], S[i])), (S[j], S[0], S[d]), (S[i], S[0], S[m])) = self.of(Lamda[Pow * Pow] @ Lamda[Pow * Binomial])
    assert d <= m
    return Equal(self, Lamda[j:d, i:d](x ** j * factorial(j) * Stirling(i, j)))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    m, d = Symbol(integer=True, positive=True)
    d = Symbol(domain=Range(m))
    i, j = Symbol(integer=True)
    x = Symbol(real=True)
    Eq << apply(Lamda[j:m, i:d](j ** i * x ** j) @ Lamda[j:d, i:m](Binomial(j, i) * (-x) ** (j - i)))

    Eq << Eq[-1].this.lhs.apply(Discrete.Dot.eq.Lamda, simplify=None)

    Eq << Eq[-1].this.find((-Symbol) ** Add).apply(Algebra.Pow.eq.Mul.Neg, simplify=None)

    Eq << Eq[-1].this.lhs().find(Sum).simplify()

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.Binom.eq.Mul.Stirling)





if __name__ == '__main__':
    run()
# created on 2022-01-18
# updated on 2023-08-27
