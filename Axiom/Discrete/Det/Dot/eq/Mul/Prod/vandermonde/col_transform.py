from util import *


@apply
def apply(self):
    (((x, j), (delta, i)), (S[j], S[0], m), (S[i], S[0], (S[m], d))), (((λ, (S[d], S[j], S[-i])), (S[d], S[i - j])), (S[j], S[0], S[m - d]), (S[i], S[0], S[m])) = \
    self.of(Det[Lamda[Pow * Pow, Tuple[Expr - Expr]] @ Lamda[(-Expr) ** Add * Binomial]])
    delta -= j
    assert not delta._has(j)
    return Equal(self, x ** Binomial(m - d, 2) * (x - λ) ** (d * (m - d)) * Product[i:m - d](factorial(i)))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, nonnegative=True)
    i, j = Symbol(integer=True)
    λ, delta, x = Symbol(real=True)
    Eq << apply(Det(Lamda[j:m, i:m - d]((j + delta) ** i * x ** j) @ Lamda[j:m - d, i:m](binomial(d, i - j) * (-λ) ** (d + j - i))))

    Eq << Eq[-1].this.find(MatMul).apply(Discrete.Dot.vandermonde.col_transform)

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul, doit=True, deep=False)

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.Binom.eq.Pow.Newton)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.eq.Mul)

    Eq << Eq[-1].this.find(Det).apply(Discrete.Det.Mul.eq.Mul.Prod)

    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.Pow.Sum)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Mul.series.arithmetic)

    Eq << Eq[-1].this.find(Add[Lamda]).apply(Algebra.Add.eq.Lamda)

    Eq << Eq[-1].this.find(Pow[Lamda]).apply(Algebra.Pow.eq.Lamda, simplify=None)

    Eq << Eq[-1].this.find(Det).apply(Discrete.DetLamdaPowAdd.eq.Prod_Factorial.vandermonde)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)





if __name__ == '__main__':
    run()
# created on 2022-01-15

# updated on 2023-05-20

