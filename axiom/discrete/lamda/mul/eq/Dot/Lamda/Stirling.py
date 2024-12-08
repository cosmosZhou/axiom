from util import *


@apply
def apply(self):
    ((j, i), (x, j)), (S[j], S[0], m), (S[i], S[0], d) = self.of(Lamda[Pow * Pow])
    return Equal(self, Lamda[j:d, i:d](Stirling(i, j) * Factorial(j) * x ** j) @ Lamda[j:m, i:d](Binomial(j, i) * x ** (j - i)))

@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    m, d = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    x = Symbol(real=True)
    Eq << apply(Lamda[j:m, i:d](j ** i * x ** j))

    Eq << Eq[-1].this.rhs.apply(Discrete.Dot.eq.Lamda, simplify=None)

    Eq << Eq[-1].this.lhs().find(Pow).apply(Discrete.Pow.eq.Sum.Stirling.FallingFactorial)

    Eq << Eq[-1].this.find(FallingFactorial).apply(Discrete.FallingFactorial.eq.Mul.Binom)

    Eq << Eq[-1].this.find(Pow * Pow).args[:2].apply(Algebra.Mul.eq.Pow.Add.exponent)

    k = Eq[-1].find(Sum).variable
    Eq << Eq[-1].this.expr.rhs.find(Sum).apply(Algebra.Sum.eq.Add.split, cond=k<=i)

    Eq << Eq[-1].this().find(Min).simplify()





if __name__ == '__main__':
    run()
# created on 2023-08-19
# updated on 2023-08-27
