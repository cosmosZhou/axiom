from util import *


@apply
def apply(self):
    (a, exp), (k, start, n) = self.of(Sum[Expr * (-1) ** Expr])
    n -= 1
    ik, kn = a.of(Stirling * Stirling1)
    i, = {*ik} - {k}
    n_, = {*kn} - {k}
    i, = {i, n_} - {n}
    assert start in (0, i)
    assert exp in (k - i, k + i, n - k, n + k)
    return Equal(self, KroneckerDelta(n, i))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    k = Symbol(integer=True)
    i = Symbol(integer=True, nonnegative=True)
    n = Symbol(domain=Range(i, oo))
    Eq << apply(Sum[k:i:n + 1]((-1) ** (k - i) * Stirling1(n, k) * Stirling(k, i)))

    x = Symbol(complex=True)
    Eq << discrete.fallingFactorial.to.sum.stirling.apply(FallingFactorial(x, n), k)

    Eq << Eq[-1].this.rhs().find(Symbol ** Symbol).apply(discrete.pow.to.sum.stirling.fallingFactorial)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.swap.intlimit)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.rhs.apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.lhs.apply(discrete.fallingFactorial.to.matmul.delta)

    Eq << discrete.eq_matmul.then.eq.vector.independence.st.matmul.fallingFactorial.apply(Eq[-1])

    Eq << algebra.all.then.cond.subs.apply(Eq[-1], Eq[-1].variable, i)

    Eq << Eq[-1] * (-1) ** (n - i)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.delta.subs)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2023-08-20
# updated on 2023-08-27
