from util import *


@apply
def apply(self):
    ((i, j), t), (S[j], S[0], i), (S[i], S[0], n) = self.of(Sum[Binomial[Expr - Expr]])
    assert t >= 0
    return Equal(self, Binomial(n + sign(t), t + 2))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete

    i, j = Symbol(integer=True)
    n, t = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[j:i, i:n](Binomial(i - j, t)))

    Eq << Eq[0].this.find(Sign).apply(Algebra.Sign.eq.Piece)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=t > 0)

    Eq <<= Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2]), Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1], invert=True)

    Eq << GreaterEqual(t, 0, plausible=True)

    Eq << Algebra.Imply.of.And.Imply.invert.apply(Eq[-2], cond=Eq[-1])

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Mul.series.arithmetic)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[0].lhs.this.find(Binomial).apply(Discrete.Binom.eq.Sub.Pascal)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Sum.eq.Sub.telescope)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.rhs.find(Sum).expr.apply(Discrete.Binom.eq.Sub.Pascal)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Sub.telescope)

    Eq << Eq[-1].this.rhs.find(Mul[~Binomial]).apply(Discrete.Binom.eq.Div.Binom)

    Eq << Algebra.Cond.to.Imply.apply(Eq[-1], cond=t > 0)

    Eq << Algebra.Imply.to.All.apply(Eq[-1])

    Eq << Eq[-1].this().find(Mul[~Binomial]).simplify()

    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.of.Gt.relax)

    Eq << Eq[-1].subs(Eq[-1].lhs.lhs, t)



if __name__ == '__main__':
    run()
# created on 2023-10-22
