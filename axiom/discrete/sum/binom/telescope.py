from util import *


@apply
def apply(self):
    ((n, k), S[n + k], (fk1, fk)), (k, S[0], S[n + 1]) = self.of(Sum[Binomial * (-1) ** Expr * (Expr - Expr)])
    S[fk1] = fk._subs(k, k + 1)
    n += 1
    return Equal(self, Sum[k:n + 1]((-1) ** (n - k) * binomial(n, k) * fk))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    f = Function(real=True)
    x = Symbol(real=True)
    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    Eq << apply(Sum[k:n + 1]((-1) ** (n - k) * Binomial(n, k) * (f(x + k + 1) - f(x + k))))

    Eq.diff = discrete.diff.to.sum.binom.apply(Difference(f(x), (x, n)), k)

    Eq.diff_1 = Eq.diff.subs(x, x + 1)

    Eq <<= Eq.diff.subs(n, n + 1)

    Eq << Eq[-1].this.lhs.apply(discrete.diff.split, n)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq.diff_1 - Eq.diff

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.add.to.mul)

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq[-1], Eq[-4])




if __name__ == '__main__':
    run()
# created on 2023-06-03
