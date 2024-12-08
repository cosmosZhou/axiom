from util import *


@apply
def apply(gt, self, n=None, k=None):
    a, b = gt.of(Greater)
    fx, (x, S[a], S[b]) = self.of(Integral)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')

    assert fx.is_continuous_at(x)
    return Equal(self, (b - a) * Limit[n:oo](Sum[k:n](fx._subs(x, a + (b - a) * k / n)) / n))


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(a > b, Integral[x:a:b](f(x)))

    Eq << Algebra.Gt.to.Lt.reverse.apply(Eq[0])

    Eq << Calculus.Lt.to.Integral.eq.Mul.Limit.Riemann.apply(Eq[-1], Integral[x:b:a](f(x)))

    Eq << -Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.Neg)

    Eq.eq_integral = Eq[-1].this.lhs.apply(Calculus.Neg.eq.Integral)

    [(k, S[0], n)] = Eq.eq_integral.find(Sum).limits
    Eq << Eq.eq_integral.find(Sum).this.apply(Algebra.Sum.limits.subs.Neg, k, n - k)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul.eq.Add, deep=True)

    Eq << Eq[-1].this.rhs.find(Add).apply(Algebra.Add.collect, k / n)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Piece.unshift)

    Eq << Eq[-1].this.find(GreaterEqual).simplify()

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Piece.pop)

    Eq << Eq[-1].this.find(LessEqual).reversed

    Eq << Eq[-1].this.rhs.find(Add).apply(Algebra.Add.eq.Piece)

    Eq << Eq.eq_integral.subs(Eq[-1])

    Eq << Eq[-1].this.find(Limit).apply(Calculus.Limit.Piece.subs)

    Eq << Eq[-1].this.find(Limit[~Mul]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Limit).apply(Calculus.Limit.eq.Add)

    Eq << Eq[-1].this.find(Limit).doit()

    Eq << Eq[-1].this.find(Limit[-Expr]).doit()





if __name__ == '__main__':
    run()
# created on 2020-05-28
# updated on 2023-05-20
