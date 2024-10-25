from util import *


@apply
def apply(self):
    prod, (k, i, n) = self.of(Sum)
    n -= 1
    (S[n], S[i], S[k - i], S[n - k]), exp = prod.of(Multinomial * (-1) ** Expr)

    assert exp == k - i or exp == k + i
    return Equal(self, KroneckerDelta(n, i))


@prove
def prove(Eq):
    from axiom import discrete, algebra, sets

    k = Symbol(integer=True)
    i = Symbol(integer=True, nonnegative=True)
    n = Symbol(domain=Range(i, oo))
    Eq << apply(Sum[k:i:n + 1]((-1) ** (k - i) * Multinomial(n, i, k - i, n - k)))

    x, y, z = Symbol(real=True)
    Eq << discrete.pow.to.sum.choose.apply((x + y + z) ** n)

    Eq << Eq[-1].subs(x, -1).subs(y, 1)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.pop.cartesianSpace.cond)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.limits.pop.cartesianSpace.cond, simplify=None)

    Eq << Eq[-1].this.rhs.find(Equal).apply(algebra.eq.transport, lhs=slice(1, None))

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.bool)

    k0, k1, k2 = Eq[-1].rhs.variables
    Eq << Eq[-1].this.find(And).apply(algebra.eq.cond.to.et.subs)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.absorb)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.find(Element).apply(sets.el.negate)

    Eq << Eq[-1].this.find(Element).apply(sets.el.add, n - k2)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.rhs().find(Min).simplify()

    Eq << Eq[-1].this.rhs().find(Max).simplify()

    i_ = Symbol('i', integer=True)
    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variable, i_)

    Eq << Eq[-1].this.rhs.find(Sum).limits_subs(k1, k)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.limits.subs.negate)

    Eq << Eq[-1].this.rhs.apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.lhs.apply(discrete.pow.to.matmul.delta)

    Eq << discrete.eq_matmul.then.eq.vector.independence.st.matmul.apply(Eq[-1])

    Eq << algebra.all.then.cond.subs.apply(Eq[-1], i_, i)

    Eq << Eq[-1].this.find(Multinomial).simplify()

    Eq << Eq[0].this.lhs.apply(algebra.sum.limits.subs.offset, i).reversed





if __name__ == '__main__':
    run()
# created on 2023-08-20
# updated on 2023-08-26
