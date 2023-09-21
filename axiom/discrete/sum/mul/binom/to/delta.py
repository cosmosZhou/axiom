from util import *


@apply
def apply(self):
    (a, b), (k, start, n) = self.of(Sum[Expr * (-1) ** Expr])
    n -= 1
    S[k], i = a.of(Binomial * Binomial(n, k))
    assert start in (0, i)
    assert b in (k - i, k + i, n - k, n + k)
    return Equal(self, KroneckerDelta(n, i))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    k = Symbol(integer=True)
    i = Symbol(integer=True, nonnegative=True, given=False)
    n = Symbol(domain=Range(i, oo))
    Eq << apply(Sum[k:i:n + 1](Binomial(n, k) * (-1) ** (k - i) * Binomial(k, i)))

    m = Symbol(integer=True, nonnegative=True)
    Eq.hypothesis = Eq[0].subs(n, m + i).this.rhs.apply(algebra.delta.offset, -i)

    Eq.initial = Eq.hypothesis.subs(i, 0)

    Eq << Eq.initial.this.lhs.apply(discrete.sum.binom.to.delta.zero)

    Eq.induct = Eq.hypothesis.subs(i, i + 1)

    Eq << Eq.induct.this.lhs.apply(algebra.sum.to.add.by_parts.offset, pivot=slice(1, 2))

    Eq << Eq[-1].this.find(~Binomial - Binomial).apply(discrete.binom.to.add.Pascal)

    Eq << Eq[-1].this.find(Pow).apply(algebra.pow.to.mul.split.exponent, simplify=None)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.find((-1) ** Add).apply(algebra.pow.to.mul.split.exponent, simplify=None)

    Eq << Eq[-1].this.find(Sum[Mul[~Sum]]).apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.find(Sum[Pow * Binomial]).apply(discrete.sum.binom.to.add)

    Eq << Eq[-1].this.find(Sum[Pow * Binomial]).apply(discrete.sum.binom.to.add)

    Eq << Eq[-1].this.find(Sum).expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Pow * Pow).args[:2].apply(algebra.mul.to.pow.add.exponent)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.sub.unshift)

    Eq << Eq[-1].this.find(Sum[Binomial]).apply(algebra.sum.to.sub.unshift)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Sum[Binomial]).apply(algebra.sum.limits.subs.offset, i)

    Eq << Eq[-1].this.find(Sum[Binomial]).apply(discrete.sum.binom.to.binom)

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.eq.infer.imply.eq.induct.apply(Eq.initial, Eq[-1], i, 0)

    Eq << Eq.hypothesis.subs(m, n - i)

    Eq << Eq[-1].this.rhs.apply(algebra.delta.offset, i)





if __name__ == '__main__':
    run()
# created on 2023-06-17
# updated on 2023-08-27
