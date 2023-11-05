from util import *


@apply
def apply(self):
    ((i, j), t), (S[j], S[0], i), (S[i], S[0], n) = self.of(Sum[Binomial[Expr - Expr]])
    assert t >= 0
    return Equal(self, Binomial(n + sign(t), t + 2))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    i, j = Symbol(integer=True)
    n, t = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[j:i, i:n](Binomial(i - j, t)))

    Eq << Eq[0].this.find(Sign).apply(algebra.sign.to.piece)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=t > 0)

    Eq <<= algebra.infer.given.infer.subs.bool.apply(Eq[-2]), algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)


    Eq << GreaterEqual(t, 0, plausible=True)
    Eq << algebra.infer.given.et.infer.invert.apply(Eq[-2], cond=Eq[-1])
    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])
    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.separate)
    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.mul.series.arithmetic)
    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial.doit)
    Eq << Eq[0].lhs.this.find(Binomial).apply(discrete.binom.to.sub.Pascal)
    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.separate)
    Eq << Eq[-1].this.rhs.expr.apply(algebra.sum.to.sub.telescope)
    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)
    Eq << Eq[-1].this.rhs.find(Sum).expr.apply(discrete.binom.to.sub.Pascal)
    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.sub.telescope)
    Eq << Eq[-1].this.rhs.find(Mul[~Binomial]).apply(discrete.binom.to.div.binom)
    Eq << algebra.cond.imply.infer.apply(Eq[-1], cond=t > 0)
    Eq << algebra.infer.imply.all.apply(Eq[-1])
    Eq << Eq[-1].this().find(Mul[~Binomial]).simplify()
    Eq << algebra.all.imply.infer.apply(Eq[-1])
    Eq << Eq[-1].this.lhs.apply(algebra.ge.given.gt.relax)
    Eq << Eq[-1].subs(Eq[-1].lhs.lhs, t)



if __name__ == '__main__':
    run()
# created on 2023-10-22
