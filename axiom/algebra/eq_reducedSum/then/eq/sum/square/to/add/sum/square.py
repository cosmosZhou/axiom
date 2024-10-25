from util import *


@apply
def apply(eq_x_bar, t, k=None):
    ((x, (S[0], n)), S[n]), x_bar = eq_x_bar.of(Equal[ReducedSum[Sliced] / Symbol])
    if k is None:
        k = eq_x_bar.generate_var(integer=True, var='k', excludes=t.free_symbols)
    return Equal(Sum[k:n]((x[k] - t) ** 2), n * (x_bar - t) ** 2 + Sum[k:n]((x[k] - x_bar) ** 2))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    t = Symbol(real=True)
    x_bar = Symbol(r"{\bar {x}}", real=True)
    Eq << apply(Equal(x_bar, ReducedSum(x[:n]) / n), t, k)

    Eq << Eq[-1].this.apply(algebra.eq.transport, rhs=-1)

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.sub.square.to.mul)

    Eq << Eq[-1].this.lhs.find(Sum).apply(algebra.sum.to.add)

    Eq << Eq[0] * n

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.sum, k)

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Mul - Mul).apply(algebra.add.to.mul)

    


if __name__ == '__main__':
    run()
# created on 2023-11-06
