from util import *


@apply
def apply(eq_x_bar, eq_s2):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    (s, S[n]), ((diff, limit), S[n]) = eq_s2.of(Equal[Indexed ** 2, Sum[Expr ** 2] / (Symbol - 1)])
    k, S[0], S[n] = limit
    S[x[k]], S[x_bar[n]] = diff.of(Expr - Expr)
    return Equal(Difference[n](s[n] ** 2), (x[n] - x_bar[n]) ** 2 / (n + 1) - s[n] ** 2 / n)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x, s = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n), Equal(s[n] ** 2, Sum[k:n]((x[k] - x_bar[n]) ** 2) / (n - 1)))

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[1] * (n - 1)

    Eq << discrete.eq_reducedSum.eq_sum.then.eq.diff.Welford.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.doit()

    Eq << algebra.eq_reducedSum.then.eq.sub.to.mul.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.apply(algebra.eq.transport, lhs=0)

    Eq << algebra.cond.then.cond.domain_defined.apply(Eq[0])

    Eq << algebra.et.then.cond.apply(Eq[-1], 1).reversed

    Eq << algebra.gt_zero.eq.then.eq.div.apply(Eq[-1], Eq[-3])





if __name__ == '__main__':
    run()
# created on 2023-11-06
# updated on 2023-11-07
